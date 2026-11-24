-- Prove2me | solution 1 for GlobalTheory.TraceAeval.trace_aeval_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:37:13.600378+00:00
-- url     : https://prove2.me/submissions/bc517f29-c052-460c-a80e-a9a2568b5fc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TracePowerSumModEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TraceAeval
open Module
namespace GlobalTheory.TraceAeval
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (g : Module.End ℂ V) (μ : ℂ) (h : IsNilpotent (g - algebraMap ℂ _ μ)) (p : ℂ[X]) :
    LinearMap.trace ℂ V (aeval g p) = (finrank ℂ V : ℂ) * p.eval μ := by
  have hk : ∀ k : ℕ, LinearMap.trace ℂ V (g ^ k) = (finrank ℂ V : ℂ) * μ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ
        ((Commute.refl g).pow_left k) h
      rw [pow_succ, Module.End.mul_eq_comp, this, ih]; ring
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, eval_add]; ring
  | monomial k a =>
    rw [aeval_monomial, ← Algebra.smul_def, map_smul, hk, eval_monomial, smul_eq_mul]; ring
end GlobalTheory.TraceAeval
