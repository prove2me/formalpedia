-- Prove2me | solution 1 for GlobalTheory.K4.TopW.conj_mem_geo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:55:10.188285+00:00
-- url     : https://prove2.me/submissions/eb1d4efd-7ea6-4392-b948-879c2f7d097e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_CobOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsFirstChernClassOfLineBundle
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsTopWTopWOfExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K4
open GlobalTheory.KEdge GlobalTheory.NeedB
variable {F K Ω : Type*} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]
open GlobalTheory.K4.TopW
variable {N : ℕ} {ζ : Ω} {x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)} {η : (Ω ≃ₐ[F] Ω) → ZMod N}
namespace GlobalTheory.K4.TopW
theorem _root_.solution [Normal F K] (σ : Ω ≃ₐ[F] Ω) {h : Ω ≃ₐ[F] Ω} (hh : h ∈ geo F K Ω) : σ * h * σ⁻¹ ∈ geo F K Ω := by
  rw [mem_geo] at hh ⊢
  intro z
  have h1 : σ⁻¹ (algebraMap K Ω z) = algebraMap K Ω ((σ⁻¹).restrictNormal K z) :=
    (AlgEquiv.restrictNormal_commutes σ⁻¹ K z).symm
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1, hh, ← h1]
  exact σ.apply_symm_apply _
end GlobalTheory.K4.TopW
