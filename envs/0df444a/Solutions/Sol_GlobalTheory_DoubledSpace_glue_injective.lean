-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.glue_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:38:55.198251+00:00
-- url     : https://prove2.me/submissions/2ba13ffa-eccf-42d7-9e42-0f7a6256354a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
import Theorems.Thm_GlobalTheory_DoubledSpace_reducedForm_mk
import Theorems.Thm_GlobalTheory_DoubledSpace_mk_mem_glue
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
theorem _root_.solution : Function.Injective (glue h X X') := by
  intro φ ψ e
  refine LinearMap.ext fun a => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (φ (Submodule.Quotient.mk x))
  have := (mk_mem_glue x y).2 hy.symm
  rw [e, mk_mem_glue] at this
  rw [this, hy]
end GlobalTheory.DoubledSpace
