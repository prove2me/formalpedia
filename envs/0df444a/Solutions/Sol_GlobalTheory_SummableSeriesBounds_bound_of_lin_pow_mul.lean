-- Prove2me | solution 1 for GlobalTheory.SummableSeriesBounds.bound_of_lin_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:12:26.62982+00:00
-- url     : https://prove2.me/submissions/500be664-4e55-4882-9f88-7cd35c6906c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableNormMulPowOfBounded
import Theorems.Thm_GlobalTheory_SummableSeriesBounds_bound_of_lin_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummableSeriesBounds
open PowerSeries Filter Topology
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
namespace GlobalTheory.SummableSeriesBounds
theorem _root_.solution {π : C} (hπ : ‖π‖ < 1) {b : ℝ} (n : ℕ) (G : bdd C)
    (hb : ∀ m, ‖coeff m ((lin π ^ n * G : bdd C) : PowerSeries C)‖ ≤ b) (m : ℕ) :
    ‖coeff m (G : PowerSeries C)‖ ≤ b := by
  induction n generalizing m with
  | zero => simpa using hb m
  | succ n ih =>
    refine ih (fun j => ?_) m
    obtain ⟨c, hc⟩ := (lin π ^ n * G).2
    refine bound_of_lin_mul hπ hc (fun i => ?_) j
    have := hb i
    rwa [pow_succ', mul_assoc, Subring.coe_mul] at this
end GlobalTheory.SummableSeriesBounds
