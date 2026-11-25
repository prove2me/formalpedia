-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Grading.conj_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:17.007294+00:00
-- url     : https://prove2.me/submissions/0740cd06-79f3-43d1-8b53-2a31cbf1a3d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
import Theorems.Thm_P2M_GlobalTheory_IndLine_Iwasawa_Grading__q_d9bfcabec8b3
import Theorems.Thm_P2M_GlobalTheory_IndLine_Iwasawa_Grading__r_de95acebf40e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open GlobalTheory GlobalTheory.IndLine GlobalTheory.IndLine.Iwasawa
variable {R : Type} [Ring R]
open GlobalTheory.IndLine.Iwasawa.Grading
variable {p r q θ : R} (h : Grading p r q θ)
include h
namespace GlobalTheory.IndLine.Iwasawa.Grading
theorem _root_.solution (Z : R) : θ * low p r q Z * θ = up p r q (θ * Z * θ) := by
  have a : ∀ u v u' v' : R, θ * u = u' * θ → θ * v' = v * θ → θ * (u * Z * v) * θ = u' * (θ * Z * θ) * v' := by
    intro u v u' v' h1 h2
    calc θ * (u * Z * v) * θ = (θ * u) * Z * (v * θ) := by simp only [mul_assoc]
      _ = _ := by rw [h1, ← h2]; simp only [mul_assoc]
  rw [low, up, mul_add, mul_add, add_mul, add_mul, a r p r q h.θr h.θq, a q p p q h.θq h.θq, a q r p r h.θq h.θr]
  abel
end GlobalTheory.IndLine.Iwasawa.Grading
