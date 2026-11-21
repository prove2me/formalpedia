-- Prove2me | solution 1 for MasulloRH.regularized_trace_scalar_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:36:13.807347+00:00
-- url     : https://prove2.me/submissions/35ec0bc4-7709-4342-ac84-19c7c5bacf0a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlpoGeChallenge_LFunction_eq_zero_re_of_isPrimitive
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Theorems.Thm_MasulloRH_trace_formula_rational_iff_RH
import Theorems.Thm_MasulloRH_regularized_initial_identity_iff_scalar_bound
import Theorems.Thm_MasulloRH_regularized_test_admissible
import Theorems.Thm_MasulloRH_regularized_mellin_limit
import Theorems.Thm_MasulloRH_regularized_prime_limit
import Theorems.Thm_MasulloRH_regularized_arch_limit
import Theorems.Thm_MasulloRH_regularized_spectral_limit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

open MasulloRH Filter
open scoped Topology

/-- GRH for primitive Dirichlet characters, at the trivial character of modulus one,
gives Mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_primitive_dirichlet_GRH' : RiemannHypothesis := by
  rw [riemannHypothesis_iff_zeros_in_strip_on_line]
  intro s hs h0 h1
  refine AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive 1 (1 : DirichletCharacter ℂ 1)
    DirichletCharacter.isPrimitive_one_level_one s h0 h1 ?_
  rwa [DirichletCharacter.LFunction_modOne_eq]

/-- Under RH the regularized initial identity holds (argument of the accepted sketch
270062f2 of `regularized_initial_identity`, with the trace formula supplied by
`trace_formula_rational_iff_RH`). -/
theorem regularized_initial_identity_of_RH (hRH : RiemannHypothesis)
    (α : ℝ) (hα : 0 < α) (hαsmall : α < 1 / 2)
    (s : ℂ) (hs : (3 / 2 : ℝ) < s.re) :
    regularizedTraceRHS α s = zetaLogDeriv s := by
  have htf := trace_formula_rational_iff_RH.2 hRH
  have hplus := regularized_mellin_limit s (1 / 2)
    (by norm_num; linarith) (by norm_num)
  have hminus := regularized_mellin_limit s (-1 / 2)
    (by norm_num; linarith) (by norm_num)
  have hpolar : Tendsto (fun n : ℕ => cutoffPolar n s) atTop
      (𝓝 (regularizedPolar s)) := by
    convert hplus.add hminus using 1 <;>
      simp only [cutoffPolar, regularizedPolar] <;> congr 2 <;> ring
  have hleft := (regularized_arch_limit s hs).add (regularized_prime_limit s hs)
  have hright := hpolar.sub (regularized_spectral_limit α hα hαsmall s hs)
  have heq : (fun n : ℕ => cutoffArch n s + cutoffPrime n s) =
      (fun n : ℕ => cutoffPolar n s - cutoffSpectral α n s) := by
    funext n
    exact (htf α hα (regularizedTraceTest n s) (regularized_test_admissible n s)).2.2.2
  rw [heq] at hleft
  have hlimit := tendsto_nhds_unique hleft hright
  unfold regularizedTraceRHS
  linear_combination hlimit

theorem solution (α : ℝ) (hα : 0 < α) (hsmall : α < 1/2) :
    (zetaLogDeriv 3).re ≤ (regularizedTraceRHS α 3).re :=
  (regularized_initial_identity_iff_scalar_bound α).1
    (regularized_initial_identity_of_RH riemannHypothesis_of_primitive_dirichlet_GRH' α hα hsmall)
