-- Prove2me | solution 1 for GlobalTheory.PrimScale.gramT_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:53:41.577559+00:00
-- url     : https://prove2.me/submissions/60daa00a-e6d2-4a23-90ac-b0033aafce01

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMatrixCongruenceContentJacobianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesHermitianGramCosetContentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsConjInt
import Theorems.Thm_GlobalTheory_PrimScale_hf_sum_left
import Theorems.Thm_GlobalTheory_PrimScale_hf_cj
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_cj
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
open GlobalTheory GlobalTheory.PrimScale
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.PrimScale
theorem _root_.solution (L : LocE F E) {n m : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    gramT L Hm (rmul x A) = cT L A * gramT L Hm x * A := by
  ext a b
  have h1 : ∀ y, hf L Hm y (∑ i, A i a • x i) = ∑ i, L.cj (A i a) * hf L Hm y (x i) := by
    intro y
    rw [← hf_cj L h, hf_sum_left]
    simp only [map_sum, map_mul, hf_cj L h]
  simp only [gramT, rmul, Matrix.of_apply, hf_sum_left, h1, Matrix.mul_apply, cT]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end GlobalTheory.PrimScale
