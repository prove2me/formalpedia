-- Prove2me | solution 1 for GlobalTheory.K4.TopW.edge_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:55:15.03789+00:00
-- url     : https://prove2.me/submissions/5dda72f5-8440-479f-ac4b-32008f016e6a

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
theorem _root_.solution {Γ : Type*} [Group Γ] (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ h : Γ) :
    edge x y η σ⁻¹ h = η (σ⁻¹ * h * σ) - η h + (x h).toAdd * (y σ).toAdd - (x σ).toAdd * (y h).toAdd := by
  simp only [edge, map_inv, toAdd_inv, inv_inv]
  ring
end GlobalTheory.K4.TopW
