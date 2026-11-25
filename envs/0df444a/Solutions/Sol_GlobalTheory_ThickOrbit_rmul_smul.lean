-- Prove2me | solution 1 for GlobalTheory.ThickOrbit.rmul_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:06:33.279799+00:00
-- url     : https://prove2.me/submissions/99d9439c-c187-44d5-a96c-cf97b2e26c31

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryNearIdentityCloseTuplesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryTupleMatrixRightMulNearIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ThickOrbitSelfDualUnramifiedLattice
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
open GlobalTheory GlobalTheory.ThickOrbit
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.ThickOrbit
theorem _root_.solution {n m : ℕ} (c : E) (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    rmul (c • x) A = c • rmul x A := by
  funext j
  simp only [rmul, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _
end GlobalTheory.ThickOrbit
