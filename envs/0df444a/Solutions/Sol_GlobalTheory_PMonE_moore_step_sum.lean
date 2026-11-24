-- Prove2me | solution 1 for GlobalTheory.PMonE.moore_step_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:18:41.834238+00:00
-- url     : https://prove2.me/submissions/8a5eeb7e-7d9d-445d-8f8c-1ea8fd0e0602

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MoorePowSubSelfEqProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset Polynomial
namespace GlobalTheory.PMonE
theorem _root_.solution {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] {h : ℕ} (c : Fin h → ℤ)
    (x : Fin h → F) (t : F) :
    ∑ i, (c i : F) * (x i ^ p - t ^ (p - 1) * x i) =
      (∑ i, (c i : F) * x i) ^ p - t ^ (p - 1) * ∑ i, (c i : F) * x i := by
  rw [sum_pow_char, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (c i : F) ^ p = c i := by
    have := map_intCast (frobenius F p) (c i)
    rwa [frobenius_def] at this
  rw [mul_pow, this]
  ring
end GlobalTheory.PMonE
