-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_coefficient_when_zero_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T14:12:01.804936+00:00
-- url     : https://prove2.me/submissions/72ece753-f262-4852-a1de-cf8fc4b28ec4

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem scaleRoot_nonneg_root
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) : 0 ≤ Phi ψ q ∧ ψ (Phi ψ q) = q :=
  (hW q hq).1.2.1

private theorem scaleRoot_pos
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (hzero : ψ 0 = 0) (q : ℝ) (hq : 0 < q) : 0 < Phi ψ q := by
  obtain ⟨hn, he⟩ := scaleRoot_nonneg_root ψ W hW q hq.le
  by_contra! h
  rw [le_antisymm h hn, hzero] at he
  exact hq.ne' he.symm

private theorem exponent_secants_mono
    (ψ : ℝ → ℝ) (hconv : ConvexOn ℝ (Ici 0) ψ) (hzero : ψ 0 = 0) :
    MonotoneOn (fun x : ℝ => ψ x / x) (Ioi 0) := by
  intro x hx y hy hxy
  simpa only [hzero, sub_zero] using hconv.secant_mono (a := (0 : ℝ)) (by simp)
    (mem_Ici.mpr (le_of_lt hx)) (mem_Ici.mpr (le_of_lt hy)) (ne_of_gt hx) (ne_of_gt hy) hxy

private theorem exponent_positive_if_zero_largest_root
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (hconv : ConvexOn ℝ (Ici 0) ψ) (hzero : ψ 0 = 0) (hPhi : Phi ψ 0 = 0)
    (x : ℝ) (hx : 0 < x) : 0 < ψ x := by
  have hsec := exponent_secants_mono ψ hconv hzero
  let y := Phi ψ 1
  have hy : 0 < y := scaleRoot_pos ψ W hW hzero 1 zero_lt_one
  have hyval : ψ y = 1 := (scaleRoot_nonneg_root ψ W hW 1 zero_le_one).2
  by_contra! hnx
  have hxy : x < y := by
    by_contra! hyx
    have hle := hsec hy hx hyx
    have hpos : 0 < ψ y / y := by rw [hyval]; exact div_pos zero_lt_one hy
    exact (not_le_of_gt hpos) (hle.trans (div_nonpos_of_nonpos_of_nonneg hnx hx.le))
  have hC : ContinuousOn ψ (Ioi 0) := by
    simpa only [interior_Ici] using hconv.continuousOn_interior
  have hsub : Icc x y ⊆ Ioi (0 : ℝ) := fun z hz => hx.trans_le hz.1
  obtain ⟨z, hz, hψz⟩ := intermediate_value_Icc hxy.le (hC.mono hsub)
    (show (0 : ℝ) ∈ Icc (ψ x) (ψ y) by rw [hyval]; exact ⟨hnx, zero_le_one⟩)
  have hroot : z ∈ RightRootSet ψ 0 := ⟨(hx.trans_le hz.1).le, hψz⟩
  have hle := (hW 0 le_rfl).1.2.2 z hroot
  rw [hPhi] at hle
  exact (hx.trans_le hz.1).not_ge hle

private theorem positive_roots_tendsto_zero
    (ψ φ : ℝ → ℝ) (hs : MonotoneOn (fun x : ℝ => ψ x / x) (Ioi 0))
    (hp : ∀ b : ℝ, 0 < b → 0 < ψ b)
    (hr : ∀ q : ℝ, 0 < q → 0 < φ q ∧ ψ (φ q) = q) :
    Tendsto φ (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
  have hqev : ∀ᶠ q in nhdsWithin (0 : ℝ) (Ioi 0), 0 < q := self_mem_nhdsWithin
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within φ ?_
    (hqev.mono fun q hq => (hr q hq).1)
  refine tendsto_order.2 ⟨fun b hb => hqev.mono fun q hq => hb.trans (hr q hq).1, ?_⟩
  intro b hb
  have hsmall : ∀ᶠ q in nhdsWithin (0 : ℝ) (Ioi 0), q < ψ b :=
    (show ∀ᶠ q in nhds (0 : ℝ), q < ψ b from Iio_mem_nhds (hp b hb)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hqev, hsmall] with q hq hlt
  obtain ⟨hpos, heq⟩ := hr q hq
  by_contra! hle
  have hquot := hs hb hpos hle
  change ψ b / b ≤ ψ (φ q) / φ q at hquot
  rw [heq] at hquot
  have h1 := (div_le_iff₀ hb).mp hquot
  have h2 := mul_le_mul_of_nonneg_left hle (div_nonneg hq.le hpos.le)
  rw [div_mul_cancel₀ q hpos.ne'] at h2
  exact hlt.not_ge (h1.trans h2)

theorem solution
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (hconv : ConvexOn ℝ (Ici 0) ψ) (hzero : ψ 0 = 0) (hφ0 : Phi ψ 0 = 0) :
    (∀ d : ℝ, HasPositiveFiniteRightPsiSlope ψ d →
      Tendsto (fun q : ℝ => q / Phi ψ q)
        (nhdsWithin 0 (Ioi 0)) (nhds d)) ∧
    ((¬ ∃ d : ℝ, HasPositiveFiniteRightPsiSlope ψ d) →
      Tendsto (fun q : ℝ => q / Phi ψ q)
        (nhdsWithin 0 (Ioi 0)) (nhds 0)) := by
  let N := nhdsWithin (0 : ℝ) (Ioi 0)
  haveI : N.NeBot := nhdsWithin_Ioi_neBot le_rfl
  have hqev : ∀ᶠ q in N, 0 < q := self_mem_nhdsWithin
  have hsec := exponent_secants_mono ψ hconv hzero
  have hpositive := exponent_positive_if_zero_largest_root ψ W hW hconv hzero hφ0
  have hφ := positive_roots_tendsto_zero ψ (Phi ψ) hsec hpositive
    (fun q hq => ⟨scaleRoot_pos ψ W hW hzero q hq, (scaleRoot_nonneg_root ψ W hW q hq.le).2⟩)
  let G : ℝ → ℝ := fun x => ψ x / x
  let d : ℝ := sInf (G '' Ioo (0 : ℝ) 1)
  have hI : (Ioo (0 : ℝ) 1).Nonempty := ⟨1 / 2, by norm_num⟩
  have hG : ∀ y ∈ G '' Ioo (0 : ℝ) 1, 0 ≤ y := by
    rintro _ ⟨x, hx, rfl⟩
    exact div_nonneg (hpositive x hx.1).le hx.1.le
  have hlim : Tendsto G N (nhds d) :=
    MonotoneOn.tendsto_nhdsWithin_Ioo_right hI
      (hsec.mono Ioo_subset_Ioi_self) ⟨0, hG⟩
  have hcoef : Tendsto (fun q => q / Phi ψ q) N (nhds d) :=
    (hlim.comp hφ).congr' (hqev.mono fun q hq => by
      change ψ (Phi ψ q) / Phi ψ q = q / Phi ψ q
      rw [(scaleRoot_nonneg_root ψ W hW q hq.le).2])
  refine ⟨?_, ?_⟩
  · intro c hc
    have hEq : d = c := tendsto_nhds_unique hlim (by simpa [G, hzero] using hc.2)
    rwa [hEq] at hcoef
  · intro hnone
    have heq : d = 0 := le_antisymm (le_of_not_gt fun hpos =>
      hnone ⟨d, hpos, by simpa [G, hzero] using hlim⟩) (le_csInf (hI.image G) hG)
    rwa [heq] at hcoef
