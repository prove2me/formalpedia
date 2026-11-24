-- Prove2me | solution 1 for GlobalTheory.UnitLemma.TorusAction.torus_mem_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:11:52.373806+00:00
-- url     : https://prove2.me/submissions/492ea8e9-0924-4781-b002-27362145ee8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusSubmoduleMulLeftImageMemSelfDualStableLatti
import Theorems.Thm_GlobalTheory_UnitLemma_TorusAction_mem_mulLat_unit
import Theorems.Thm_GlobalTheory_UnitLemma_TorusAction_sigma_eq_inv
import Theorems.Thm_GlobalTheory_UnitLemma_TorusAction_isLat_mulLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TorusAction
open InvAlg
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.UnitLemma.TorusAction
theorem _root_.solution (K : UQ) (B : InvAlg K) (x : B.A) :
    ∀ t ∈ B.T, ∀ L ∈ B.X x, mulLat K.O (t : B.A) L ∈ B.X x := by
  intro t ht L hL
  obtain ⟨hlat, hg, hdual⟩ := hL
  have hs := sigma_eq_inv B t ht
  refine ⟨isLat_mulLat B t L hlat, ?_, ?_⟩
  · intro y hy
    rw [mem_mulLat_unit] at hy ⊢
    have := hg _ hy
    rwa [mul_left_comm] at this
  · intro y
    rw [mem_mulLat_unit, hdual]
    constructor
    · intro h z hz
      rw [mem_mulLat_unit] at hz
      have := h _ hz
      have e : B.herm x (((t⁻¹ : B.Aˣ) : B.A) * y) (((t⁻¹ : B.Aˣ) : B.A) * z) = B.herm x y z := by
        have hs' : B.σ ((t⁻¹ : B.Aˣ) : B.A) = (t : B.A) := by rw [← hs, B.σ_σ]
        unfold InvAlg.herm; rw [map_mul B.σ, hs']
        congr 1
        linear_combination (x * y * B.σ z) * Units.inv_mul t
      rwa [e] at this
    · intro h w hw
      have hz : (t : B.A) * w ∈ mulLat K.O (t : B.A) L := by
        rw [mem_mulLat_unit, ← mul_assoc, Units.inv_mul, one_mul]; exact hw
      have := h _ hz
      have e : B.herm x (((t⁻¹ : B.Aˣ) : B.A) * y) w = B.herm x y ((t : B.A) * w) := by
        unfold InvAlg.herm; rw [map_mul B.σ, hs]; congr 1; ring
      rwa [e]
end GlobalTheory.UnitLemma.TorusAction
