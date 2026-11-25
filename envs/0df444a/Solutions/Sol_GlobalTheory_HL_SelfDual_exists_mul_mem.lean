-- Prove2me | solution 1 for GlobalTheory.HL.SelfDual.exists_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:40:15.248137+00:00
-- url     : https://prove2.me/submissions/b3056885-c64c-415b-8e9f-53370ec841c0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SelfDual
open Matrix GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.SelfDual
theorem _root_.solution (L : LocE F E) (x : E) :
    ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ L.O := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors 𝒪[F]) (Rₘ := F) x (Algebra.IsIntegral.isIntegral x)
  refine ⟨m, nonZeroDivisors.coe_ne_zero m, (L.O_def _).2 ?_⟩
  convert hm using 1
  rw [Submonoid.smul_def, Algebra.smul_def]
  rfl
end GlobalTheory.HL.SelfDual
