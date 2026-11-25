-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.reducedForm_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:26:41.72212+00:00
-- url     : https://prove2.me/submissions/9d559a57-0e09-41d9-bb8d-3fe7a6d0a339

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
open GlobalTheory.DoubledSpace
variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] {σ : E →+* E}
namespace GlobalTheory.DoubledSpace
theorem _root_.solution (h : W →ₗ[E] W →ₛₗ[σ] E) (hh : ∀ x y, σ (h x y) = h y x)
    (X : Submodule E W) (x y : X.orthogonalBilin h) :
    reducedForm h hh X (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = h x y := rfl
end GlobalTheory.DoubledSpace
