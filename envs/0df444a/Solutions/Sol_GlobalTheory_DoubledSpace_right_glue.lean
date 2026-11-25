-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.right_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:32:27.937655+00:00
-- url     : https://prove2.me/submissions/51f39ca2-15b1-475f-b33e-7ba270b03f53

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
theorem _root_.solution (hX' : ∀ x ∈ X', ∀ x' ∈ X', h x x' = 0) (φ : Reduced h X →ₗ[E] Reduced h X') :
    right (glue h X X' φ) = X' := by
  ext y
  rw [mem_right, mem_glue]
  constructor
  · rintro ⟨hx, hy, e⟩
    have e0 : (Submodule.Quotient.mk ⟨0, hx⟩ : Reduced h X) = 0 := rfl
    rw [e0, map_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at e
    exact e
  · intro hy
    have hy' : y ∈ X'.orthogonalBilin h := fun n hn => hX' n hn y hy
    refine ⟨Submodule.zero_mem _, hy', ?_⟩
    have e1 : (Submodule.Quotient.mk ⟨y, hy'⟩ : Reduced h X') = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hy
    rw [e1]; exact map_zero φ
end GlobalTheory.DoubledSpace
