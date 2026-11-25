-- Prove2me | solution 1 for GlobalTheory.HL.Inhab.big_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:59:25.594634+00:00
-- url     : https://prove2.me/submissions/cfde2fd2-d856-41d1-b7f7-7077258ffa18

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {s m N : ℕ} (e : Fin s ⊕ Fin m ≃ Fin N)
namespace GlobalTheory.HL.Inhab
theorem _root_.solution (L : LocE F E) (H : Matrix (Fin s) (Fin s) E) (hH : IsIntM L H) : IsIntM L (big e H) := by
  intro a b
  obtain ⟨p, rfl⟩ := e.surjective a
  obtain ⟨q, rfl⟩ := e.surjective b
  simp only [big, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases p with p | p <;> rcases q with q | q
  · simpa using hH p q
  · simp
  · simp
  · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
end GlobalTheory.HL.Inhab
