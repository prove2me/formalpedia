-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.left_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:32:50.725665+00:00
-- url     : https://prove2.me/submissions/38efbab7-fb60-440e-8c1f-b7eff2449550

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
theorem _root_.solution (hX : ∀ x ∈ X, ∀ x' ∈ X, h x x' = 0) (φ : Reduced h X ≃ₗ[E] Reduced h X') :
    left (glue h X X' φ) = X := by
  ext x
  rw [mem_left, mem_glue]
  constructor
  · rintro ⟨hx, hy, e⟩
    have e0 : (Submodule.Quotient.mk ⟨0, hy⟩ : Reduced h X') = 0 := rfl
    rw [e0, LinearEquiv.coe_coe, φ.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at e
    exact e
  · intro hx
    have hx' : x ∈ X.orthogonalBilin h := fun n hn => hX n hn x hx
    refine ⟨hx', Submodule.zero_mem _, ?_⟩
    have e1 : (Submodule.Quotient.mk ⟨x, hx'⟩ : Reduced h X) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hx
    rw [e1, map_zero]; rfl
end GlobalTheory.DoubledSpace
