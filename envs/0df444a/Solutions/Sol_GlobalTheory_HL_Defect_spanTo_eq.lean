-- Prove2me | solution 1 for GlobalTheory.HL.Defect.spanTo_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:31:08.76195+00:00
-- url     : https://prove2.me/submissions/56d49c7e-f7b9-4dc3-b87c-7f8d54ea3481

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqPowAndIndexGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetUpdateRowLastSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesLevelLeIffCongrFlagSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_FrameOnto_mem_spanTo
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Defect
open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat GlobalTheory.UnramOrder Matrix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.Defect
theorem _root_.solution (g g₁ : Fin (r + 1) → S.V) (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) (hg : ∀ j, g₁ j = ∑ i, s i j • g i)
    (j : ℕ) : S.spanTo g₁ j = S.spanTo g j := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    rw [hg]
    refine Submodule.sum_mem _ fun a _ => ?_
    by_cases h : i < a
    · simp [hs.1 _ _ h]
    · exact Submodule.smul_mem _ _ (FrameOnto.mem_spanTo S g (lt_of_le_of_lt (not_lt.1 h) hi))
  · have key : ∀ m : ℕ, ∀ i : Fin (r + 1), (i : ℕ) = m → (i : ℕ) < j → g i ∈ S.spanTo g₁ j := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro i him hi
        have h1 : g i = g₁ i - ∑ a ∈ Finset.univ.erase i, s a i • g a := by
          rw [hg, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hs.2]; simp
        rw [h1]
        refine Submodule.sub_mem _ (FrameOnto.mem_spanTo S g₁ hi) (Submodule.sum_mem _ fun a ha => ?_)
        rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase ha) with h | h
        · exact Submodule.smul_mem _ _ (ih a (him ▸ h) a rfl (lt_trans h hi))
        · simp [hs.1 _ _ h]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    exact key i i rfl hi
end GlobalTheory.HL.Defect
