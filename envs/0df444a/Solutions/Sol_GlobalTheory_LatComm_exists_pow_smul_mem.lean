-- Prove2me | solution 1 for GlobalTheory.LatComm.exists_pow_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:16:22.042209+00:00
-- url     : https://prove2.me/submissions/60071b5f-dc7b-46de-a663-1162fbf95e04

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisFurther
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerCommensurableUnramifiedHermitia
import Theorems.Thm_GlobalTheory_PowMulMemOrder_main


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
open GlobalTheory GlobalTheory.LatComm
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.LatComm
theorem _root_.solution (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (p : L.O)
    (hp : (p : E) = algebraMap F E (ϖ : F)) {n : ℕ}
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (v : Fin n → E) :
    ∃ j : ℕ, p ^ j • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.PowMulMemOrder.main
  | exact _root_.GlobalTheory.PowMulMemOrder.main
  | (apply _root_.GlobalTheory.PowMulMemOrder.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowMulMemOrder.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowMulMemOrder.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowMulMemOrder.main ..)
end GlobalTheory.LatComm
