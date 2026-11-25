-- Prove2me | solution 1 for GlobalTheory.ThickOrbit.exists_pow_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:54:09.871897+00:00
-- url     : https://prove2.me/submissions/fa30eca4-2484-480f-b474-8bf0ffc05787

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
import Theorems.Thm_GlobalTheory_PowMulMem_exists_pow_smul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.ThickOrbit
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.ThickOrbit
theorem _root_.solution (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {n : ℕ}
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (v : Fin n → E) :
    ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.PowMulMem.exists_pow_smul_mem
  | exact _root_.GlobalTheory.PowMulMem.exists_pow_smul_mem
  | (apply _root_.GlobalTheory.PowMulMem.exists_pow_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowMulMem.exists_pow_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowMulMem.exists_pow_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowMulMem.exists_pow_smul_mem ..)
end GlobalTheory.ThickOrbit
