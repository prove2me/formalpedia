-- Prove2me | solution 1 for GlobalTheory.Published.Metaplectic.Model.chirp_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:14:26.81543+00:00
-- url     : https://prove2.me/submissions/23497477-5472-4eab-b809-38478550cb85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HolPartShear
import Theorems.Thm_GlobalTheory_Published_Metaplectic_act_fromBlocks
import Theorems.Thm_GlobalTheory_Published_Metaplectic_rho_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.Metaplectic GlobalTheory.Published.Metaplectic.Model
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.Published.Metaplectic.Model
theorem _root_.solution (C : Matrix ι ι ℝ) (hC : Cᵀ = C) (p q : ι → ℝ) (φ ψ : 𝓢(ι → ℝ, ℂ)) (h : ⇑ψ = chirp C φ) :
    chirp C (rho (p, q) φ) = rho (act (fromBlocks 1 0 C 1) (p, q)) ψ := by
  funext x
  have hs : p ⬝ᵥ C *ᵥ x = x ⬝ᵥ C *ᵥ p := by
    rw [dotProduct_mulVec, ← hC, vecMul_transpose, hC, dotProduct_comm]
  rw [act_fromBlocks, rho_apply, h]
  simp only [chirp, rho_apply, one_mulVec, zero_mulVec, add_zero, mulVec_add, dotProduct_add, add_dotProduct, hs]
  rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring
end GlobalTheory.Published.Metaplectic.Model
