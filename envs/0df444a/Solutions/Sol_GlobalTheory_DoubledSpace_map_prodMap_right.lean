-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.map_prodMap_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:02:00.1843+00:00
-- url     : https://prove2.me/submissions/1435a2c2-fd87-47e7-a58a-ed0b74937f27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
import Theorems.Thm_GlobalTheory_DoubledSpace_apply_right_mem
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
    (hu : ∀ y ∈ (right I).orthogonalBilin h, u y - y ∈ right I) :
    I.map (LinearMap.id.prodMap u) = I := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact apply_right_mem hI hu hp
  · exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (Function.injective_id.prodMap hi) I)).symm
end GlobalTheory.DoubledSpace
