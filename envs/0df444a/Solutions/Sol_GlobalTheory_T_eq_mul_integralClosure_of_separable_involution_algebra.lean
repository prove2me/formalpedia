-- Prove2me | solution 1 for GlobalTheory.T.eq_mul_integralClosure_of_separable_involution_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:20:06.349788+00:00
-- url     : https://prove2.me/submissions/bd4f1ef0-7514-4755-859d-b5545cc0887c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebraStatement
import Theorems.Thm_GlobalTheory_UnitLemma_PrincipalLat_eq_mulLat_integralClosure


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
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) → ∃ a : B.Aˣ, J = mulLat K.O (a : B.A) (Subalgebra.toSubmodule (integralClosure K.O B.A)) := by
  first | exact @GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_integralClosure | exact GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_integralClosure | (intros; apply GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_integralClosure <;> assumption)
end _root_.GlobalTheory.T
