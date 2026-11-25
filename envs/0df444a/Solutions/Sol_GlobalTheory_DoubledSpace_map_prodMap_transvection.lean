-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.map_prodMap_transvection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:56:51.81473+00:00
-- url     : https://prove2.me/submissions/6103eefe-d607-4c1f-a4ee-26422b4a6785

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
import Theorems.Thm_GlobalTheory_DoubledSpace_left_isotropic
import Theorems.Thm_GlobalTheory_DoubledSpace_map_prodMap_left
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply



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
theorem _root_.solution {ξ : W} (hξ : ξ ∈ left I) (b : E) {u : W →ₗ[E] W}
    (hu : ∀ v, u v = v + (b * h v ξ) • ξ) : I.map (u.prodMap LinearMap.id) = I := by
  refine map_prodMap_left hI ?_ fun x _ => ?_
  · rw [injective_iff_map_eq_zero]
    intro v hv
    have h0 : h (u v) ξ = 0 := by simp [hv]
    rw [hu, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      left_isotropic hI ξ hξ ξ hξ, smul_zero, add_zero] at h0
    rw [hu, h0] at hv
    simpa using hv
  · rw [hu, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ hξ
end GlobalTheory.DoubledSpace
