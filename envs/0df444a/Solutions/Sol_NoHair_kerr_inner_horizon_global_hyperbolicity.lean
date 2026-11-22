-- Prove2me | solution 1 for NoHair.kerr_inner_horizon_global_hyperbolicity
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T23:23:55.28487+00:00
-- url     : https://prove2.me/submissions/7eb6769a-0c83-4aa1-9bf1-80e92166d853

import Definitions.Def_NoHair_KerrNewmanExteriorGeodesics
import Theorems.Thm_NoHair_kerrNewman_outerHorizon_futureTrapped
import Theorems.Thm_NoHair_kerr_inner_horizon_diamond_confinement
import Theorems.Thm_NoHair_kerr_inner_horizon_compact_limit

open NoHair Set
open scoped Manifold ContDiff Topology
noncomputable section

private abbrev Reg := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
private abbrev Met := kerrNewmanMetricField (5/2) 2 0
private abbrev Orient := kerrNewmanTimeDirection (5/2) 2 0
private abbrev UnitInterval := Icc (0:ℝ) 1

private def component (v : E4) (i : Fin 4) : ℝ := v i

private theorem clock_data (γ : ℝ → kerrNewmanSpacetime 2)
    (hγ : IsFutureCausalCurveIn Met Orient Reg γ) :
    (∀ i : Fin 4, ∀ t, HasDerivAt (fun s => (γ s).val i) (component (velocity γ t) i) t) ∧
      ∀ t∈UnitInterval, 0 < component (velocity γ t) 0 ∧ ∀ i : Fin 4, |component (velocity γ t) i| ≤ component (velocity γ t) 0 := by
  let f : ℝ → E4 := Subtype.val ∘ γ
  let I4 := 𝓘(ℝ,E4)
  have hval : ContMDiff I4 I4 1 (Subtype.val : kerrNewmanSpacetime 2 → E4) := contMDiff_subtype_val
  have hf : ContDiff ℝ 1 f := (hval.comp hγ.1).contDiff
  constructor
  · intro i t
    have hd := ((hf.differentiable_one t).hasFDerivAt).hasDerivAt
    have he := NoHair.ExteriorGeodesics.ambient_velocity 2 γ hγ.1 t (deriv f t) hd
    have hi := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t hd
    rw [he]
    exact hi
  · intro t ht
    let x := γ t
    have hr : 0 < ksRadius 2 x.val := x.property
    have hF : 0 ≤ ksProfile (5/2) 2 0 x.val := by
      unfold ksProfile
      simp only [zero_pow (by decide : 2 ≠ 0),sub_zero]
      positivity
    have hdir : 0 < component (Orient x) 0 := by change 0 < 1+ksProfile (5/2) 2 0 x.val/2; linarith
    obtain ⟨_,hn,hv,hfut⟩ := hγ.2 t ht
    have hp : IsKerrNewmanBlackHoleParams (5/2) 2 0 := by norm_num [IsKerrNewmanBlackHoleParams]
    have htime := (kerrNewman_outerHorizon_futureTrapped _ _ _ hp).1
    obtain ⟨hb,hs⟩ := NoHair.ExteriorGeodesics.cone_estimates (5/2) 2 0 x hF
      (velocity γ t) (Orient x) hn hv hfut (htime.2 x)
    have hpos : 0 < component (velocity γ t) 0 := by
      by_contra! h
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg h hdir.le)) hs
    exact ⟨hpos,fun i => (hb i).trans_eq (abs_of_pos hpos)⟩

private theorem clock_strict (γ : ℝ → kerrNewmanSpacetime 2)
    (hγ : IsFutureCausalCurveIn Met Orient Reg γ) : StrictMonoOn (fun s => (γ s).val 0) UnitInterval := by
  obtain ⟨hd,hv⟩ := clock_data γ hγ
  exact strictMonoOn_of_deriv_pos (convex_Icc 0 1) (fun t _ => (hd 0 t).continuousAt.continuousWithinAt)
    (fun t ht => (hd 0 t).deriv.symm ▸ (hv t (interior_subset ht)).1)

theorem solution :
    let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
    let g := kerrNewmanMetricField (5/2) 2 0
    let T := kerrNewmanTimeDirection (5/2) 2 0
    IsGloballyHyperbolicOn g T A  := by
  dsimp only
  constructor
  · intro p _ he
    obtain ⟨γ,hγ,h0,h1⟩ := he
    have h := clock_strict γ hγ (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_lt_one
    change (γ 0).val 0 < (γ 1).val 0 at h
    rw [h0,h1] at h
    exact (lt_irrefl _) h
  intro p hpD q hqD
  let E := causalFuture Met Orient Reg p ∩ causalPast Met Orient Reg q
  obtain ⟨K,hK,hKD,hpK,hqK,hconf⟩ := kerr_inner_horizon_diamond_confinement p hpD q hqD
  let J : Set ((kerrNewmanSpacetime 2) × (kerrNewmanSpacetime 2)) := {z | z.1 ∈ K ∧ z.2 ∈ K ∧ z.2 ∈ causalFuture Met Orient K z.1}
  let B : Set (kerrNewmanSpacetime 2) := (fun x => (p,x)) ⁻¹' closure J ∩ (fun x => (x,q)) ⁻¹' closure J
  have hB : IsClosed B := (isClosed_closure.preimage (continuous_const.prodMk continuous_id)).inter
    (isClosed_closure.preimage (continuous_id.prodMk continuous_const))
  have hlim := kerr_inner_horizon_compact_limit K hK hKD
  have hE : E = K ∩ B := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxK,hpx,hxq⟩ := hconf x hx
      exact ⟨hxK,subset_closure (show (p,x) ∈ J from ⟨hpK,hxK,hpx⟩),
        subset_closure (show (x,q) ∈ J from ⟨hxK,hqK,hxq⟩)⟩
    · rintro ⟨_,hx,hx'⟩
      exact ⟨hlim (show (p,x) ∈ closure J from hx),hlim (show (x,q) ∈ closure J from hx')⟩
  change IsCompact E
  rw [hE]
  exact hK.inter_right hB
