-- Prove2me | solution 1 for GlobalTheory.sum_eq_zero_of_factorsThrough_characters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:36:12.960108+00:00
-- url     : https://prove2.me/submissions/af27b809-78da-4862-9eda-ec4489dbb0cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory
variable {X H : Type*} [MulOneClass H]
namespace GlobalTheory
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R]
    (χ : X → (H →* R)) (f : X →₀ R) (hf : ∀ s : H, f.sum (fun x a => a * χ x s) = 0)
    (c : X → R) (hc : ∀ x y, χ x = χ y → c x = c y) : f.sum (fun x a => a * c x) = 0 := by
  classical
  have h0 : Finsupp.mapDomain χ f = 0 := by
    refine linearIndependent_iff.1 (linearIndependent_monoidHom H R) _ ?_
    rw [Finsupp.linearCombination_mapDomain]
    funext s
    rw [Finsupp.linearCombination_apply, Finsupp.sum_apply', Pi.zero_apply, ← hf s]
    rfl
  have hfac : Function.FactorsThrough c χ := fun x y h => hc x y h
  have h1 : Finsupp.linearCombination R (Function.extend χ c 0) (Finsupp.mapDomain χ f) = 0 := by
    rw [h0, map_zero]
  rw [Finsupp.linearCombination_mapDomain, hfac.extend_comp, Finsupp.linearCombination_apply] at h1
  exact h1
end GlobalTheory
