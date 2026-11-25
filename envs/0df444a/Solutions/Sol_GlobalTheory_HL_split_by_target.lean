-- Prove2me | solution 1 for GlobalTheory.HL.split_by_target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:01:44.688384+00:00
-- url     : https://prove2.me/submissions/fcaed5cf-cfe6-41ac-a96f-d3406a1c01f4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetMoveTermWeightCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralLinearPositiveNormBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFineSubgroupMovesAtLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermDoubleCosetMovesFiniteTargetsSplit
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_indexMeasureIntegral_linear_positive_norm_bound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution {W Y Z : Type} [AddCommGroup W] (A B : AddSubgroup W) (M : W → Prop) (m : W → Z)
    (f : Y → Z) (hf : Function.Injective f) (hB : Fine A (ind M) B)
    (hm : ∀ w, M w → ∀ b ∈ B, m (w + b) = m w) (hex : ∀ w, M w → ∃ y, f y = m w) (c : ℝ) (hc : 0 ≤ c) :
    {y | ∃ w, M w ∧ f y = m w}.Finite ∧ (∀ y, Nice A (ind fun w => M w ∧ f y = m w)) ∧
    {y | c * (cint A (ind fun w => M w ∧ f y = m w)).re ≠ 0}.Finite ∧
    (∀ y, 0 ≤ c * (cint A (ind fun w => M w ∧ f y = m w)).re) ∧
    ∀ (P : Y → Prop) (g : Y → ℂ) (G : W → ℂ), (∀ w y, (M w ∧ f y = m w) → G w = if P y then g y else 0) →
      (∀ w, ¬ M w → G w = 0) → Nice A G ∧
      ∑ᶠ y : {y // P y}, ((c * (cint A (ind fun w => M w ∧ f y = m w)).re : ℝ) : ℂ) * g y =
        (c : ℂ) * cint A G := by
  obtain ⟨hBA, hidx, hinv, hfin⟩ := hB
  have hsupp : Function.support (ind M) = {w | M w} := by
    ext w
    simp [ind]
  have hMinv : ∀ w, ∀ b ∈ B, (M (w + b) ↔ M w) := by
    intro w b hb
    have h := hinv w b hb
    simp only [ind] at h
    by_cases h1 : M (w + b) <;> by_cases h2 : M w <;> simp [h1, h2] at h ⊢
  have hTfin : {y | ∃ w, M w ∧ f y = m w}.Finite := by
    let g : Y → W ⧸ B := fun y =>
      if h : ∃ w, M w ∧ f y = m w then (QuotientAddGroup.mk h.choose : W ⧸ B) else 0
    refine Set.Finite.of_finite_image (f := g) (hfin.subset ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩
      have hy' : ∃ w, M w ∧ f y = m w := hy
      refine ⟨hy'.choose, ?_, ?_⟩
      · rw [hsupp]
        exact hy'.choose_spec.1
      · simp only [g, dif_pos hy']
    · intro y1 hy1 y2 hy2 heq
      have hy1' : ∃ w, M w ∧ f y1 = m w := hy1
      have hy2' : ∃ w, M w ∧ f y2 = m w := hy2
      simp only [g, dif_pos hy1', dif_pos hy2'] at heq
      apply hf
      rw [hy1'.choose_spec.2, hy2'.choose_spec.2]
      have hb : -hy1'.choose + hy2'.choose ∈ B := QuotientAddGroup.eq.mp heq
      have h := hm _ hy1'.choose_spec.1 _ hb
      rw [add_neg_cancel_left] at h
      exact h.symm
  have hFine : ∀ y, Fine A (ind fun w => M w ∧ f y = m w) B := by
    intro y
    refine ⟨hBA, hidx, ?_, hfin.subset ?_⟩
    · intro w b hb
      simp only [ind]
      by_cases hw : M w
      · have h1 : M (w + b) := (hMinv w b hb).mpr hw
        simp only [h1, hw, true_and, hm w hw b hb]
      · have h1 : ¬ M (w + b) := fun h => hw ((hMinv w b hb).mp h)
        simp only [h1, hw, false_and]
    · apply Set.image_mono
      intro w hw
      rw [hsupp]
      by_contra hM
      refine (Function.mem_support.mp hw) ?_
      simp only [ind]
      rw [if_neg (fun h => hM h.1)]
  have hnice : ∀ y, Nice A (ind fun w => M w ∧ f y = m w) := fun y => ⟨B, hFine y⟩
  have hzero : ∀ y, y ∉ {y | ∃ w, M w ∧ f y = m w} → cint A (ind fun w => M w ∧ f y = m w) = 0 := by
    intro y hy
    have h : (ind fun w => M w ∧ f y = m w) = fun _ => 0 := by
      funext w
      simp only [ind]
      rw [if_neg]
      exact fun h => hy ⟨w, h⟩
    rw [h]
    simp [cint]
  obtain ⟨-, hI2, hI3, hI4⟩ := GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound A
  refine ⟨hTfin, hnice, hTfin.subset ?_, fun y => mul_nonneg hc (hI3 _).1, ?_⟩
  · intro y hy
    change c * _ ≠ 0 at hy
    by_contra hyT
    rw [hzero y hyT] at hy
    simp at hy
  · intro P g G hG hG0
    have hGeq : G = fun w => ∑ y ∈ hTfin.toFinset.filter P, g y * ind (fun w => M w ∧ f y = m w) w := by
      funext w
      by_cases hw : M w
      · obtain ⟨y0, hy0⟩ := hex w hw
        have hy0T : y0 ∈ hTfin.toFinset := by
          rw [Set.Finite.mem_toFinset]
          exact ⟨w, hw, hy0⟩
        rw [hG w y0 ⟨hw, hy0⟩]
        have hother : ∀ y, y ≠ y0 → ind (fun w => M w ∧ f y = m w) w = 0 := by
          intro y hne
          simp only [ind]
          rw [if_neg]
          rintro ⟨-, h⟩
          exact hne (hf (h.trans hy0.symm))
        by_cases hP : P y0
        · rw [if_pos hP, Finset.sum_eq_single y0]
          · simp only [ind]
            rw [if_pos ⟨hw, hy0⟩, mul_one]
          · intro y _ hne
            rw [hother y hne, mul_zero]
          · intro h
            exact absurd (Finset.mem_filter.mpr ⟨hy0T, hP⟩) h
        · rw [if_neg hP, Finset.sum_eq_zero]
          intro y hy
          have hne : y ≠ y0 := by
            rintro rfl
            exact hP (Finset.mem_filter.mp hy).2
          rw [hother y hne, mul_zero]
      · rw [hG0 w hw, Finset.sum_eq_zero]
        intro y _
        simp only [ind]
        rw [if_neg (fun h => hw h.1), mul_zero]
    have hcG : Nice A G ∧ cint A G =
        ∑ y ∈ hTfin.toFinset.filter P, g y * cint A (ind fun w => M w ∧ f y = m w) := by
      obtain ⟨hn, hs⟩ := hI4 Y (hTfin.toFinset.filter P)
        (fun y w => g y * ind (fun w => M w ∧ f y = m w) w) (fun y _ => (hI2 (g y) _ (hnice y)).1)
      rw [hGeq]
      exact ⟨hn, hs.trans (Finset.sum_congr rfl fun y _ => (hI2 (g y) _ (hnice y)).2)⟩
    refine ⟨hcG.1, ?_⟩
    rw [hcG.2]
    have hsub : Function.support (fun y : {y // P y} =>
        ((c * (cint A (ind fun w => M w ∧ f y.1 = m w)).re : ℝ) : ℂ) * g y.1) ⊆
        ↑(hTfin.toFinset.subtype P) := by
      intro y hy
      rw [Finset.mem_coe, Finset.mem_subtype, Set.Finite.mem_toFinset]
      by_contra hyT
      refine (Function.mem_support.mp hy) ?_
      rw [hzero y.1 hyT]
      simp
    rw [finsum_eq_sum_of_support_subset _ hsub]
    refine (Finset.sum_subtype_eq_sum_filter
      (fun y => ((c * (cint A (ind fun w => M w ∧ f y = m w)).re : ℝ) : ℂ) * g y)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have him := (hI3 (fun w => M w ∧ f y = m w)).2
    have hre : ((cint A (ind fun w => M w ∧ f y = m w)).re : ℂ) = cint A (ind fun w => M w ∧ f y = m w) :=
      Complex.ext (by simp) (by simp [him])
    push_cast
    rw [hre]
    ring
end GlobalTheory.HL
