-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.finrank_reduced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:32:21.819518+00:00
-- url     : https://prove2.me/submissions/a65486c8-3224-42c9-9e0c-8e24897bb485

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
import Theorems.Thm_GlobalTheory_DoubledSpace_finrank_add_finrank_orthogonal

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
variable {h : W →ₗ[E] W →ₛₗ[σ] E} {X X' : Submodule E W}
variable [FiniteDimensional E W] (hσ : Function.Involutive σ) (hh : ∀ x y, σ (h x y) = h y x)
  (hn : ∀ x, (∀ y, h x y = 0) → x = 0)
include hσ hh hn
namespace GlobalTheory.DoubledSpace
theorem _root_.solution (hX : ∀ x ∈ X, ∀ x' ∈ X, h x x' = 0) :
    finrank E (Reduced h X) + 2 * finrank E X = finrank E W := by
  have a := (X.submoduleOf (X.orthogonalBilin h)).finrank_quotient_add_finrank
  have b := (Submodule.submoduleOfEquivOfLe
    (show X ≤ X.orthogonalBilin h from fun x hx n hn => hX n hn x hx)).finrank_eq
  have c := finrank_add_finrank_orthogonal hσ hh hn X
  change finrank E (Reduced h X) + _ = _ at a
  omega
end GlobalTheory.DoubledSpace
