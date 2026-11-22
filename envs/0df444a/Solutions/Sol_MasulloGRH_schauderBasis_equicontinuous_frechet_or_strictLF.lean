-- Prove2me | solution 1 for MasulloGRH.schauderBasis_equicontinuous_frechet_or_strictLF
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-11-21T08:03:20.938411+00:00
-- url     : https://prove2.me/submissions/cc4375fa-54cd-4120-82ec-f995a5feb8a6

import Definitions.Def_MasulloGRH_SchauderBases
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open MasulloGRH Topology Filter Set
open scoped Uniformity
noncomputable section

private theorem frechet_barrelled (E : Type u) [AddCommGroup E] [Module ℂ E]
    [tE : TopologicalSpace E] (hE : IsFrechet E) : BarrelledSpace ℂ E := by
  obtain ⟨ι, hι, p, hp⟩ := hE.1
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  have : T2Space E := hE.2.1.1
  have : TopologicalSpace.MetrizableSpace E := hE.2.2
  let _ : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace E := by
    constructor
    intro f hf
    apply hE.2.1.2 f
    obtain ⟨hne, ht⟩ := (IsUniformAddGroup.cauchy_iff_tendsto f).mp hf
    refine ⟨hne, ?_⟩
    intro U hU
    obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp (ht hU)
    exact ⟨A ∩ B, inter_mem hA hB, fun x hx y hy ↦ hAB (show (x, y) ∈ A ×ˢ B from ⟨hx.1, hy.2⟩)⟩
  have : (𝓤 E).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero E]
    infer_instance
  have : BaireSpace E := by infer_instance
  infer_instance

private theorem strictLF_barrelled (E : Type u) [AddCommGroup E] [Module ℂ E]
    [tE : TopologicalSpace E] (hE : IsStrictLF E) : BarrelledSpace ℂ E := by
  rcases hE with ⟨X, _, _, hX, htop⟩
  constructor
  intro q hq
  let p : SeminormFamily ℂ E PUnit.{u+1} := fun _ ↦ q
  let t : TopologicalSpace E := p.moduleFilterBasis.topology
  have ht : @WithSeminorms ℂ E PUnit.{u+1} _ _ _ p t := ⟨rfl⟩
  let : TopologicalSpace E := tE
  have hle : tE ≤ t := by
    rw [htop]
    apply sInf_le
    refine ⟨⟨PUnit.{u+1}, inferInstance, p, ht⟩, ?_⟩
    intro n
    let : TopologicalSpace E := tE
    obtain ⟨ι, hι, r, hr⟩ := (hX n).1
    have : IsTopologicalAddGroup (X n) := hr.topologicalAddGroup
    have : BarrelledSpace ℂ (X n) := frechet_barrelled (X n) (hX n)
    have hcont : Continuous (q.comp (X n).subtype) :=
      (q.comp (X n).subtype).continuous_of_lowerSemicontinuous
        (hq.comp continuous_subtype_val)
    let : TopologicalSpace E := t
    let : TopologicalSpace (X n) := TopologicalSpace.induced (Subtype.val : X n → E) tE
    exact ht.continuous_of_continuous_comp (X n).subtype (fun _ ↦ hcont)
  have hid : @Continuous E E tE t id := continuous_id_iff_le.mpr hle
  have hcont : @Continuous E ℝ t _ q := by
    let : TopologicalSpace E := t
    exact ht.continuous_seminorm PUnit.unit
  exact @Continuous.comp E E ℝ tE t _ id q hcont hid

private theorem projections_equicontinuous (E : Type u) [AddCommGroup E] [Module ℂ E]
    [tE : TopologicalSpace E] (hE : IsHLCS E) [BarrelledSpace ℂ E]
    (x : ℕ → E) (f : ℕ → StrongDual ℂ E) (hx : IsSchauderBasis x f) :
    IsEquicontinuousBasis x f := by
  classical
  obtain ⟨ι, hι, p, hp⟩ := hE.1
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  let P : ℕ → E →L[ℂ] E := fun k ↦ ∑ m ∈ Finset.range (k+1), (f m).smulRight (x m)
  have hP (k : ℕ) (u : E) : P k u = basicProjection x f k u := by
    simp [P, basicProjection]
  have hb (i : ι) : BddAbove (range fun k ↦ (p i).comp (P k).toLinearMap) := by
    rw [Seminorm.bddAbove_range_iff]
    intro u
    have ht := (hp.continuous_seminorm i).continuousAt.tendsto.comp (hx.expansion u)
    simpa only [hP, Seminorm.comp_apply, ContinuousLinearMap.coe_coe, Function.comp_def] using ht.bddAbove_range
  let Q : ι → Seminorm ℂ E := fun i ↦ ⨆ k, (p i).comp (P k).toLinearMap
  have hQ (i : ι) : Continuous (Q i) := by
    rw [show (Q i : E → ℝ) = ⨆ k, ⇑((p i).comp (P k).toLinearMap) from
      Seminorm.coe_iSup_eq (hb i)]
    exact Seminorm.continuous_iSup _ (fun k ↦ show Continuous ((p i).comp (P k).toLinearMap) from
      (hp.continuous_seminorm i).comp (P k).continuous) (hb i)
  intro U hU
  obtain ⟨⟨s, r⟩, hr, hs⟩ := hp.hasBasis_zero_ball.mem_iff.mp hU
  let q : Seminorm ℂ E := s.sup Q
  have hq : Continuous q := Seminorm.continuous_finsetSup (fun i _ ↦ hQ i)
  refine ⟨q.ball 0 r, ?_, ?_⟩
  · exact Seminorm.ball_mem_nhds hq hr
  · intro k u hu
    apply hs
    change (s.sup p) (basicProjection x f k u - 0) < r
    rw [sub_zero]
    have hbound : (s.sup p) (P k u) ≤ q u := by
      apply Seminorm.finset_sup_apply_le (apply_nonneg q u)
      intro i hi
      exact ((le_ciSup (hb i) k : (p i).comp (P k).toLinearMap ≤ Q i) u).trans (Seminorm.le_finset_sup_apply (p := Q) (x := u) hi)
    rw [← hP]
    exact hbound.trans_lt (by simpa [Seminorm.mem_ball_zero] using hu)

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E] [tE : TopologicalSpace E]
    (hE : IsHLCS E) (x : ℕ → E) (f : ℕ → StrongDual ℂ E)
    (hx : IsSchauderBasis x f) (hspace : IsFrechet E ∨ IsStrictLF E) :
    IsEquicontinuousBasis x f := by
  have : BarrelledSpace ℂ E := hspace.elim (frechet_barrelled E) (strictLF_barrelled E)
  exact projections_equicontinuous E hE x f hx
