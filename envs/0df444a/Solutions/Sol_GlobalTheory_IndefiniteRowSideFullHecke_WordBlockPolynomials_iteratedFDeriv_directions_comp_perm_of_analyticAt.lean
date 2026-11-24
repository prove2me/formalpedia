-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials.iteratedFDeriv_directions_comp_perm_of_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:19:34.350957+00:00
-- url     : https://prove2.me/submissions/e96b92fa-9e1d-48a3-aa86-23a0eeb641d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_WordDerivativeBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
variable {ι : Type} {dim : ι → ℕ} {n : ℕ}
variable {Λ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
theorem _root_.solution (dir : Λ → W) {F : W → ℂ} {p : W} (hF : AnalyticAt ℂ F p)
    {k : ℕ} (u v : Fin k → Λ) (σ : Equiv.Perm (Fin k)) (h : u = v ∘ σ) :
    iteratedFDeriv ℂ k F p (fun j => dir (u j)) = iteratedFDeriv ℂ k F p (fun j => dir (v j)) := by
  subst h
  exact (hF.contDiffAt (n := ⊤)).iteratedFDeriv_comp_perm (fun j => dir (v j)) σ
end GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
