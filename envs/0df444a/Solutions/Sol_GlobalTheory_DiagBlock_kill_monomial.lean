-- Prove2me | solution 1 for GlobalTheory.DiagBlock.kill_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:49:11.192655+00:00
-- url     : https://prove2.me/submissions/73159f24-f6a3-45d0-a4e9-558a2cc6f916

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock
variable {R : Type} [CommRing R] {σ : Type}
open Classical
namespace GlobalTheory.DiagBlock
theorem _root_.solution (S : σ → Prop) [DecidablePred S] (m : σ →₀ ℕ) (c : R) :
    kill S (MvPolynomial.monomial m c) =
      if ∀ x, S x → m x = 0 then MvPolynomial.monomial m c else 0 := by
  rw [kill, MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  split_ifs with h
  · rw [MvPolynomial.monomial_eq]
    congr 1
    refine Finsupp.prod_congr fun x hx => ?_
    rw [if_neg]
    intro hS
    exact (Finsupp.mem_support_iff.1 hx) (h x hS)
  · push Not at h
    obtain ⟨x, hS, hx⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hx), mul_zero]
    rw [if_pos hS, zero_pow hx]
end GlobalTheory.DiagBlock
