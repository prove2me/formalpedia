-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.glue_isotropic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:39:11.056964+00:00
-- url     : https://prove2.me/submissions/0eec23a3-6081-4cf8-9f8e-aeacb0e02ef2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
import Theorems.Thm_GlobalTheory_DoubledSpace_reducedForm_mk
import Theorems.Thm_GlobalTheory_DoubledSpace_mem_glue
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply


attribute [local simp] GlobalTheory.DoubledSpace.reducedForm_mk

set_option autoImplicit false
open GlobalTheory
open Module
open GlobalTheory.DoubledSpace
variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] {σ : E →+* E}
variable {h : W →ₗ[E] W →ₛₗ[σ] E} {X X' : Submodule E W}
namespace GlobalTheory.DoubledSpace
theorem _root_.solution (hh : ∀ x y, σ (h x y) = h y x) {φ : Reduced h X →ₗ[E] Reduced h X'}
    (hφ : ∀ a b, reducedForm h hh X' (φ a) (φ b) = reducedForm h hh X a b) :
    ∀ p ∈ glue h X X' φ, ∀ q ∈ glue h X X' φ, form h p q = 0 := by
  rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq
  obtain ⟨hx, hy, e⟩ := mem_glue.1 hp
  obtain ⟨hx', hy', e'⟩ := mem_glue.1 hq
  have := hφ (Submodule.Quotient.mk ⟨x, hx⟩) (Submodule.Quotient.mk ⟨x', hx'⟩)
  rw [e, e', reducedForm_mk, reducedForm_mk] at this
  rw [form_apply, sub_eq_zero]
  exact this.symm
end GlobalTheory.DoubledSpace
