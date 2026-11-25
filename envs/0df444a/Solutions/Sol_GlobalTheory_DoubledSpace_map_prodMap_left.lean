-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.map_prodMap_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:49:22.172275+00:00
-- url     : https://prove2.me/submissions/d72698d4-57bc-468d-806b-8b1b18b4eef2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
import Theorems.Thm_GlobalTheory_DoubledSpace_apply_left_mem
import Theorems.Thm_GlobalTheory_IsSaturatedSubmodule_eq_of_le_of_finrank_eq


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
variable {h : W →ₗ[E] W →ₛₗ[σ] E} {I : Submodule E (W × W)}
variable [FiniteDimensional E W] (hσ : Function.Involutive σ) (hh : ∀ x y, σ (h x y) = h y x)
  (hn : ∀ x, (∀ y, h x y = 0) → x = 0) (hI : ∀ p ∈ I, ∀ q ∈ I, form h p q = 0)
  (hd : finrank E I = finrank E W)
include hσ hh hn hI hd
omit hσ hh hn hd
namespace GlobalTheory.DoubledSpace
theorem _root_.solution {u : W →ₗ[E] W} (hi : Function.Injective u)
    (hu : ∀ x ∈ (left I).orthogonalBilin h, u x - x ∈ left I) :
    I.map (u.prodMap LinearMap.id) = I := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact apply_left_mem hI hu hp
  · exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (hi.prodMap Function.injective_id) I)).symm
end GlobalTheory.DoubledSpace
