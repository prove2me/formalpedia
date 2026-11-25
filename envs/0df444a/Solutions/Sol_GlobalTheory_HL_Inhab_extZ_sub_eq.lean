-- Prove2me | solution 1 for GlobalTheory.HL.Inhab.extZ_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:41:03.219901+00:00
-- url     : https://prove2.me/submissions/80e8af00-b010-467c-81bb-c4fea6ba08e0

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
theorem _root_.solution (x y z : Fin s → E) (c : E) (h : x - y = c • z) :
    extZ e x - extZ e y = c • extZ e z := by
  funext i
  simp only [extZ, Pi.sub_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
  rcases e.symm i with a | a
  · simpa using congrFun h a
  · simp
end GlobalTheory.HL.Inhab
