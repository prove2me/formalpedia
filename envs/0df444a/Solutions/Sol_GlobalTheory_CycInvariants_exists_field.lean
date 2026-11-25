-- Prove2me | solution 1 for GlobalTheory.CycInvariants.exists_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:22:35.195366+00:00
-- url     : https://prove2.me/submissions/c0e0c274-156e-4633-b2f2-af6b2b597b9e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerTraceAlmostSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumMulLeftTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegers
import Theorems.Thm_GlobalTheory_CycInvariants_exists_reps
import Theorems.Thm_GlobalTheory_CycInvariants_stabilizer_finiteIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycInvariants
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.CycInvariants
theorem _root_.solution (F : IntermediateField ℚ_[l] (Om l)) (x : Om l) :
    ∃ (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)), x ∈ L ∧ F ≤ L ∧
      (∀ h ∈ F.fixingSubgroup, ∀ x ∈ L, h x ∈ L) ∧ (∀ s ∈ S, s ∈ F.fixingSubgroup) ∧
      (∀ h ∈ F.fixingSubgroup, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) := by
  have := stabilizer_finiteIndex x
  set N := (MulAction.stabilizer (GQ l) x).normalCore with hN
  set L := IntermediateField.fixedField (F.fixingSubgroup ⊓ N) with hL
  have hle : F.fixingSubgroup ⊓ N ≤ L.fixingSubgroup :=
    (IntermediateField.le_iff_le _ _).1 le_rfl
  have hfi : (L.fixingSubgroup.subgroupOf F.fixingSubgroup).FiniteIndex := by
    refine Subgroup.finiteIndex_of_le (H := N.subgroupOf F.fixingSubgroup) ?_
    intro g hg
    exact hle ⟨g.2, hg⟩
  obtain ⟨S, hS, hu⟩ := exists_reps F.fixingSubgroup L.fixingSubgroup
  refine ⟨L, S, ?_, ?_, ?_, hS, hu⟩
  · rw [hL, IntermediateField.mem_fixedField_iff]
    intro g hg
    exact Subgroup.normalCore_le _ hg.2
  · exact (IntermediateField.le_iff_le _ _).2 inf_le_left
  · intro h hh y hy
    rw [hL, IntermediateField.mem_fixedField_iff] at hy ⊢
    intro g hg
    have h1 : h⁻¹ * g * h ∈ F.fixingSubgroup ⊓ N :=
      ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) hg.1) hh,
        by simpa using (Subgroup.normalCore_normal _).conj_mem g hg.2 h⁻¹⟩
    have h2 := congrArg h (hy _ h1)
    simpa using h2
end GlobalTheory.CycInvariants
