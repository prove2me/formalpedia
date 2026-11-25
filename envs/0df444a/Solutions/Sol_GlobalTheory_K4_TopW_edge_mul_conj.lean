-- Prove2me | solution 1 for GlobalTheory.K4.TopW.edge_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:55:18.586806+00:00
-- url     : https://prove2.me/submissions/5d4ac51d-b1fe-49f1-afd1-cd5e6a47119e

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
theorem _root_.solution {Γ : Type*} [Group Γ] (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ τ h : Γ) :
    edge x y η (σ * τ) h = edge x y η σ (τ * h * τ⁻¹) + edge x y η τ h := by
  simp only [edge, map_mul, map_inv, toAdd_mul, toAdd_inv, mul_inv_rev]
  have : σ * τ * h * (τ⁻¹ * σ⁻¹) = σ * (τ * h * τ⁻¹) * σ⁻¹ := by group
  rw [this]; ring
end GlobalTheory.K4.TopW
