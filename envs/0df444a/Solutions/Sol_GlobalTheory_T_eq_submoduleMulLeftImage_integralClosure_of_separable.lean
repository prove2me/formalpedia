-- Prove2me | solution 1 for GlobalTheory.T.eq_submoduleMulLeftImage_integralClosure_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:54:43.507316+00:00
-- url     : https://prove2.me/submissions/92421746-9197-4a61-b38e-aa5d8ada8a83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqSubmoduleMulLeftImageIntegralClosureOfSeparabl
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqSubmoduleMulLeftImageIntegralClosureOfSeparablStatement
import Theorems.Thm_GlobalTheory_UnitLemma_PrincipalLatDVR_eq_mulLat_integralClosure_of_separable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → ∀ N : Submodule O A, IsLat O E N → (∀ x ∈ integralClosure O A, ∀ y ∈ N, x * y ∈ N) → ∃ t : Aˣ, N = mulLat O (t : A) (Subalgebra.toSubmodule (integralClosure O A)) := by
  first | exact @GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable | exact GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable | (intros; apply GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable <;> assumption)
end _root_.GlobalTheory.T
