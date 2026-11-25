-- Prove2me | solution 1 for GlobalTheory.HL.FibU.exists_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:22:04.965797+00:00
-- url     : https://prove2.me/submissions/ca07ee6e-e2e9-4061-ba1c-30c27e8e4e71

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuadricCharacterLeakSharesFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqMeanOverRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPowSmulMemOfIsLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermIntegralNearOneBound
import Theorems.Thm_GlobalTheory_PowSmulMemLattice_exists_pow_smul_mem_of_isLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FibU
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F]
namespace GlobalTheory.HL.FibU
theorem _root_.solution (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {n : ℕ}
    (Λ : Submodule L.O (Fin n → E)) (hΛ : IsLat L Λ) (y : Fin n → E) :
    ∃ m : ℕ, algebraMap F E ((ϖ : F) ^ m) • y ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.PowSmulMemLattice.exists_pow_smul_mem_of_isLat
  | exact _root_.GlobalTheory.PowSmulMemLattice.exists_pow_smul_mem_of_isLat
  | (apply _root_.GlobalTheory.PowSmulMemLattice.exists_pow_smul_mem_of_isLat <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowSmulMemLattice.exists_pow_smul_mem_of_isLat <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowSmulMemLattice.exists_pow_smul_mem_of_isLat <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowSmulMemLattice.exists_pow_smul_mem_of_isLat ..)
end GlobalTheory.HL.FibU
