-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.mk_mem_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:32:25.34833+00:00
-- url     : https://prove2.me/submissions/a734d3b1-9a22-4795-a74a-898bd7274a02

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
import Theorems.Thm_GlobalTheory_DoubledSpace_mem_glue

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
theorem _root_.solution {φ : Reduced h X →ₗ[E] Reduced h X'} (x : X.orthogonalBilin h)
    (y : X'.orthogonalBilin h) :
    (x.1, y.1) ∈ glue h X X' φ ↔ φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
  rw [mem_glue]
  exact ⟨fun ⟨_, _, e⟩ => e, fun e => ⟨x.2, y.2, e⟩⟩
end GlobalTheory.DoubledSpace
