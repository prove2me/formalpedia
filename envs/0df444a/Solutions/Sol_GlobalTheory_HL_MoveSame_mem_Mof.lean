-- Prove2me | solution 1 for GlobalTheory.HL.MoveSame.mem_Mof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:15:17.184267+00:00
-- url     : https://prove2.me/submissions/ebb67fe7-bf33-4b9f-bf9d-ad937a44441b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMovePropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MoveLatticeIsTermSameDatumWithWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMovePreservesFrameLatticeLevels
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_WitIndep_th_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveSame
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.MoveSame
theorem _root_.solution (g g' : Fin (r + 1) → S.V) (y : S.V) :
    y ∈ S.Mof g g' ↔ ∃ al al' : Fin (r + 1) → E, y = ∑ i, al i • g i + ∑ i, al' i • g' i ∧
      ∀ i, algebraMap F E S.th * al' i ∈ L.O ∧ al i + al' i ∈ L.O := by
  have ht := WitIndep.th_mul S
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · refine ⟨Pi.single b 1, 0, by simp [Pi.single_apply], fun i => ⟨by simp, ?_⟩⟩
        by_cases h : i = b
        · subst h; simp
        · simp [h]
      · refine ⟨Pi.single b (-algebraMap F E S.th⁻¹), Pi.single b (algebraMap F E S.th⁻¹), ?_,
          fun i => ?_⟩
        · simp only [Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
            if_true, smul_sub, neg_smul]
          abel
        · by_cases h : i = b
          · subst h
            simp only [Pi.single_eq_same, neg_add_cancel, mul_comm (algebraMap F E S.th), ht]
            exact ⟨L.O.one_mem, L.O.zero_mem⟩
          · simp [h]
    | zero => exact ⟨0, 0, by simp, fun i => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, a', rfl, ha⟩ := hx
      obtain ⟨b, b', rfl, hb⟩ := hy
      refine ⟨a + b, a' + b', ?_, fun i => ⟨?_, ?_⟩⟩
      · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel
      · simpa [mul_add] using L.O.add_mem (ha i).1 (hb i).1
      · have := L.O.add_mem (ha i).2 (hb i).2
        rw [add_add_add_comm] at this
        exact this
    | smul c x _ hx =>
      obtain ⟨a, a', rfl, ha⟩ := hx
      refine ⟨fun i => c * a i, fun i => c * a' i, ?_, fun i => ⟨?_, ?_⟩⟩
      · rw [Subring.smul_def]
        simp only [smul_add, Finset.smul_sum, smul_smul]
      · have := L.O.mul_mem c.2 (ha i).1
        rw [mul_left_comm] at this
        exact this
      · have := L.O.mul_mem c.2 (ha i).2
        rw [mul_add] at this
        exact this
  · rintro ⟨al, al', rfl, h⟩
    rw [← Finset.sum_add_distrib]
    refine Submodule.sum_mem _ fun i _ => ?_
    have e : al i • g i + al' i • g' i = (al i + al' i) • g i +
        (algebraMap F E S.th * al' i) • (algebraMap F E S.th⁻¹ • (g' i - g i)) := by
      rw [smul_smul, mul_right_comm, mul_comm (algebraMap F E S.th), ht, one_mul, add_smul, smul_sub]
      abel
    rw [e]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ (⟨_, (h i).2⟩ : L.O) (Submodule.subset_span (Or.inl ⟨i, rfl⟩)))
      (Submodule.smul_mem _ (⟨_, (h i).1⟩ : L.O) (Submodule.subset_span (Or.inr ⟨i, rfl⟩)))
end GlobalTheory.HL.MoveSame
