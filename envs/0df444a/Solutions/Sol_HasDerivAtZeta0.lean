-- Prove2me | solution 1 for HasDerivAtZeta0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T17:41:42.879367+00:00
-- url     : https://prove2.me/submissions/6165bd9f-86db-4035-99a7-24b3fdd0a837

import Batteries.Tactic.Lemma
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs
import Theorems.Thm_HasDerivAt_cpow_over_var
import Theorems.Thm_HasDerivAt_neg_cpow_over2
import Theorems.Thm_div_cpow_eq_cpow_neg
import Theorems.Thm_hasDerivAt_Zeta0Integral

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

-- move near `Real.differentiableAt_rpow_const_of_ne`

theorem solution {N : ℕ} (Npos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    HasDerivAt (ζ₀ N) (ζ₀' N s) s := by
  unfold riemannZeta0 ζ₀'
  have hterm : ∀ n : ℕ, HasDerivAt (fun z : ℂ ↦ 1 / (n : ℂ) ^ z)
      (-1 / (n : ℂ) ^ s * Real.log n) s := by
    intro n
    have hf : (fun z : ℂ ↦ 1 / (n : ℂ) ^ z) = fun z ↦ (n : ℂ) ^ (-z) := by
      funext z; rw [cpow_neg, one_div]
    rw [hf]
    refine (hasDerivAt_neg' s |>.const_cpow (c := n) (by aesop)).congr_deriv ?_
    rw [cpow_neg, natCast_log]
    ring
  have h1 : HasDerivAt (fun z : ℂ ↦ ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ z)
      (∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n) s :=
    HasDerivAt.fun_sum (u := Finset.range (N + 1)) (A := fun (n : ℕ) (z : ℂ) ↦ 1 / (n : ℂ) ^ z)
      (A' := fun (n : ℕ) ↦ -1 / (n : ℂ) ^ s * Real.log n) fun n _ ↦ hterm n
  have h2 : HasDerivAt (fun z : ℂ ↦ (-(N : ℂ) ^ (1 - z)) / (1 - z))
      (-(N : ℂ) ^ (1 - s) / (1 - s) ^ 2 + Real.log N * (N : ℂ) ^ (1 - s) / (1 - s)) s := by
    have hc : HasDerivAt (fun z : ℂ ↦ 1 - z) (-1) s := (hasDerivAt_id s).const_sub 1
    have := (HasDerivAt_cpow_over_var N (z := 1 - s)
      (by rw [sub_ne_zero]; exact s_ne_one.symm)).comp s hc
    refine this.congr_deriv ?_
    ring
  have h3 : HasDerivAt (fun z : ℂ ↦ (-(N : ℂ) ^ (-z)) / 2)
      (Real.log N * (N : ℂ) ^ (-s) / 2) s := by
    refine (HasDerivAt_neg_cpow_over2 Npos s).congr_deriv ?_
    ring
  have h4 : HasDerivAt
      (fun z : ℂ ↦ z * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (z + 1))
      (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
        s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by
    simp_rw [div_cpow_eq_cpow_neg, neg_add, ← sub_eq_add_neg]
    exact (hasDerivAt_id s).mul (hasDerivAt_Zeta0Integral Npos reS_pos)
  exact ((h1.add h2).add h3).add h4

-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`

-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**

-- **End collaboration 6/20/25**

/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we
want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{lemma}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{lemma}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/

-- **Begin collaboration with the Alpha Proof team! 5/29/25**

-- **End collaboration**

open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients
