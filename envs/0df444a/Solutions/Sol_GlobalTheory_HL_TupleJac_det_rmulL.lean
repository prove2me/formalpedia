-- Prove2me | solution 1 for GlobalTheory.HL.TupleJac.det_rmulL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:40:17.054124+00:00
-- url     : https://prove2.me/submissions/c780b5bc-169d-4d8a-a67b-7fae35e8df30

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelVolMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometry
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TupleJac
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
omit [TopologicalSpace E]
namespace GlobalTheory.HL.TupleJac
theorem _root_.solution {n m : ℕ} (A : Matrix (Fin m) (Fin m) E) :
    LinearMap.det (rmulL (n := n) A) = A.det ^ n := by
  have h : rmulL (n := n) A = (swapL n m).toLinearMap ∘ₗ
      (LinearMap.pi fun i : Fin n => (Matrix.toLin' A.transpose) ∘ₗ LinearMap.proj i) ∘ₗ
      (swapL n m).symm.toLinearMap := by
    refine LinearMap.ext fun x => ?_
    ext j k
    simp [rmulL, rmul, swapL, Matrix.mulVec, dotProduct]
  rw [h, LinearMap.det_conj, LinearMap.det_pi]
  simp [LinearMap.det_toLin']
end GlobalTheory.HL.TupleJac
