-- Prove2me | solution 1 for GlobalTheory.CommonDenominator.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:24:18.587799+00:00
-- url     : https://prove2.me/submissions/428011f3-d2de-492b-b87b-9347d17661d2

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgebraMapMemO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
open GlobalTheory GlobalTheory.CommonDenominator
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.CommonDenominator
theorem _root_.solution (L : Formalism.MainNotions.S.Loc.LocE F E) (c : E) :
    ∃ t : 𝒪[F], t ≠ 0 ∧ algebraMap F E (t : F) * c ∈ L.O := by
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank
  have hc : IsIntegral F c := Algebra.IsIntegral.isIntegral c
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors 𝒪[F]) (Rₘ := F) c hc
  refine ⟨(m : 𝒪[F]), nonZeroDivisors.ne_zero m.2, ?_⟩
  rw [L.O_def]
  have h : m • c = algebraMap F E ((m : 𝒪[F]) : F) * c := by
    rw [Submonoid.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪[F] F E]; rfl
  rw [← h]
  exact hm
end GlobalTheory.CommonDenominator
