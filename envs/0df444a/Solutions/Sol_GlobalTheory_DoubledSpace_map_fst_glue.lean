-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.map_fst_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:39:40.035627+00:00
-- url     : https://prove2.me/submissions/67a27959-da55-463d-8e64-d0426c3c469b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
import Theorems.Thm_GlobalTheory_DoubledSpace_mem_glue
import Theorems.Thm_GlobalTheory_DoubledSpace_mk_mem_glue

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
namespace GlobalTheory.DoubledSpace
theorem _root_.solution (φ : Reduced h X →ₗ[E] Reduced h X') :
    (glue h X X' φ).map (LinearMap.fst E W W) = X.orthogonalBilin h := by
  apply le_antisymm
  · rintro _ ⟨⟨x, y⟩, hp, rfl⟩
    exact (mem_glue.1 hp).1
  · intro x hx
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (φ (Submodule.Quotient.mk ⟨x, hx⟩))
    exact ⟨(x, y.1), (mk_mem_glue ⟨x, hx⟩ y).2 hy.symm, rfl⟩
end GlobalTheory.DoubledSpace
