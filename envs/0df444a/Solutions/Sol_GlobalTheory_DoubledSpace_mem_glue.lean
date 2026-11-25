-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.mem_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:25:41.371415+00:00
-- url     : https://prove2.me/submissions/474ccad0-42c0-43b8-8a4e-8f87c0756fa4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral

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
namespace GlobalTheory.DoubledSpace
theorem _root_.solution {h : W →ₗ[E] W →ₛₗ[σ] E} {X X' : Submodule E W}
    {φ : Reduced h X →ₗ[E] Reduced h X'} {x y : W} :
    (x, y) ∈ glue h X X' φ ↔ ∃ (hx : x ∈ X.orthogonalBilin h) (hy : y ∈ X'.orthogonalBilin h),
      φ (Submodule.Quotient.mk ⟨x, hx⟩) = Submodule.Quotient.mk ⟨y, hy⟩ := by
  constructor
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hp, e⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 e
    exact ⟨ha, hb, Eq.symm hp⟩
  · rintro ⟨hx, hy, e⟩
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), e.symm, rfl⟩
end GlobalTheory.DoubledSpace
