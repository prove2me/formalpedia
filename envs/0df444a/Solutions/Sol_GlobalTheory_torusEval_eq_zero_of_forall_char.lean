-- Prove2me | solution 1 for GlobalTheory.torusEval_eq_zero_of_forall_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:44:33.458045+00:00
-- url     : https://prove2.me/submissions/6c643280-9937-43b3-ae8a-71199f7dbedf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Theorems.Thm_GlobalTheory_sum_eq_zero_of_factorsThrough_characters
import Theorems.Thm_GlobalTheory_torusEval_apply

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
open AddMonoidAlgebra
variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X]
variable [IsDomain R]
namespace GlobalTheory
theorem _root_.solution (H : Subgroup (Multiplicative X →* Rˣ))
    {f : AddMonoidAlgebra R X} (hf : ∀ s ∈ H, torusEval s f = 0) {t : Multiplicative X →* Rˣ}
    (ht : ∀ x : Multiplicative X, (∀ s ∈ H, s x = 1) → t x = 1) : torusEval t f = 0 := by
  rw [torusEval_apply]
  refine sum_eq_zero_of_factorsThrough_characters
    (fun x => (torusChar x).comp H.subtype) f.coeff (fun s => ?_) _ fun x y hxy => ?_
  · rw [← hf s s.2, torusEval_apply]
    rfl
  · have := ht (Multiplicative.ofAdd x * (Multiplicative.ofAdd y)⁻¹) fun s hs => by
      have h := DFunLike.congr_fun hxy ⟨s, hs⟩
      rw [map_mul, map_inv, mul_inv_eq_one]
      exact Units.ext h
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    rw [this]
end GlobalTheory
