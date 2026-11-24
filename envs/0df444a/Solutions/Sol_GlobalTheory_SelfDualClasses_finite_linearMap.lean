-- Prove2me | solution 1 for GlobalTheory.SelfDualClasses.finite_linearMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:41:14.973931+00:00
-- url     : https://prove2.me/submissions/f00a14df-da29-4189-ac9e-e70a40a62e80

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClassesSelfDualOfSelfDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory.SelfDualClasses
open ShortVectors
namespace GlobalTheory.SelfDualClasses
theorem _root_.solution {R M T : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup T] [Module R T] [Module.Finite R M] [Finite T] : Finite (M →ₗ[R] T) := by
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' R M
  refine Finite.of_injective
    (fun (g : M →ₗ[R] T) (i : Fin m) => g (f (Pi.basisFun R (Fin m) i))) fun g g' h => ?_
  rw [← LinearMap.cancel_right hf]
  exact (Pi.basisFun R (Fin m)).ext fun i => congrFun h i
end GlobalTheory.SelfDualClasses
