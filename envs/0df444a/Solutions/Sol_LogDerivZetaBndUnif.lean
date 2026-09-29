-- Prove2me | solution 1 for LogDerivZetaBndUnif
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T19:10:49.990548+00:00
-- url     : https://prove2.me/submissions/ab1e2fed-2bb9-42c5-a4e7-9f37b429b1ec

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
import Theorems.Thm_ZetaDerivUpperBnd
import Theorems.Thm_ZetaInvBnd
import Theorems.Thm_ZetaInvBnd_aux
import Theorems.Thm_logt_gt_one
import Theorems.Thm_triv_bound_zeta

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

-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`

-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**

-- **End collaboration 6/20/25**

theorem LogDerivZetaBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / Real.log |t| ^ 9) (1 + A / Real.log |t| ^ 9)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
      C * Real.log |t| ^ 9 := by
  obtain ⟨A, hA, C, hC, h⟩ := ZetaInvBnd
  obtain ⟨A', hA', C', hC', h'⟩ := ZetaDerivUpperBnd
  use min A A', ⟨lt_min hA.1 hA'.1, min_le_of_right_le hA'.2⟩, C * C', mul_pos hC hC'
  intro σ t t_gt ⟨σ_ge, σ_lt⟩
  have logt_gt : (1 : ℝ) < Real.log |t| := logt_gt_one t_gt.le
  have σ_ge' : 1 - A / Real.log |t| ^ 9 ≤ σ := by
    apply le_trans (tsub_le_tsub_left ?_ 1) σ_ge
    apply div_le_div_of_nonneg_right (min_le_left A A')
    exact pow_nonneg (zero_le_one.trans logt_gt.le) _
  have σ_ge'' : 1 - A' / Real.log |t| ≤ σ := by
    apply le_trans (tsub_le_tsub_left ?_ 1) σ_ge
    apply div_le_div₀ hA'.1.le (min_le_right A A') (lt_trans (by norm_num) logt_gt) ?_
    exact le_self_pow₀ logt_gt.le (by norm_num)
  replace h := h σ t t_gt ⟨σ_ge', by calc
    σ < 1 + min A A' / Real.log |t| ^ 9 := σ_lt
    _ ≤ 1 + A / Real.log |t| ^ 9 := by gcongr; simp⟩
  replace h' := h' σ t t_gt ⟨σ_ge'', by
   calc
    σ ≤ 1 + min A A' / Real.log |t| ^ 9 := by linarith [σ_lt]

    _ ≤ 1 + (1/2) / Real.log |t| ^ 9 := by gcongr; simp [Set.mem_Ioc] at hA' hA ⊢ ; simp [hA.2]

    _ ≤ 1 + (1/2) / 1 := by
          gcongr
          calc
            1 ≤ Real.log |t| := by linarith
            _ ≤ (Real.log |t|)^9 := Real.self_le_rpow_of_one_le (by linarith) (by linarith)
          norm_cast

    _ ≤ 2 := by linarith
    ⟩
  simp only [norm_div]
  have hpos : 0 ≤ C * Real.log |t| ^ (7 : ℝ) := by positivity
  convert mul_le_mul h h' (by simp) hpos using 1 <;> (norm_cast <;> ring_nf)

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

theorem solution :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ 9)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
      C * Real.log |t| ^ 9 := by
  let ⟨A, pf_A, C, C_pos, ζbd_in⟩ := LogDerivZetaBnd
  let ⟨C_triv, ⟨pf_C_triv, ζbd_out⟩⟩ := triv_bound_zeta
  have T0 : A > 0 := pf_A.1

  have ha : 1 ≤ A⁻¹ := by
    simp only [one_div, mem_Ioc, true_and, T0] at pf_A
    have U := (inv_le_inv₀ (by positivity) (by positivity)).mpr pf_A
    simp only [inv_inv] at U
    linarith

  refine ⟨A, pf_A, ((1 + C + C_triv) * A⁻¹), (by positivity), fun σ t hyp_t hyp_σ ↦ ?_⟩
  have logt_gt' : (1 : ℝ) < Real.log |t| ^ 9 := by
    calc
      1 < Real.log |t| := logt_gt_one hyp_t.le
      _ ≤ (Real.log |t|) ^ 9 := ZetaInvBnd_aux (logt_gt_one hyp_t.le)

  have logt_gt'' : (1 : ℝ) < 1 + A / Real.log |t| ^ 9 := by
    simp only [lt_add_iff_pos_right, div_pos_iff_of_pos_left, T0]
    positivity

  have T1 : ∀⦃σ : ℝ⦄, 1 + A / Real.log |t| ^ 9 ≤ σ → 1 < σ := by
    intros
    linarith

  have T2 : ∀⦃σ : ℝ⦄, 1 + A / Real.log |t| ^ 9 ≤ σ → A / Real.log |t| ^ 9 ≤ σ - 1 := by
    intro σ' hyp_σ'
    calc
      A / Real.log |t| ^ 9 = (1 + A / Real.log |t| ^ 9) - 1 := by ring_nf
      _ ≤ σ' - 1 := by gcongr

  by_cases h : σ ∈ Ico (1 - A / Real.log |t| ^ 9) (1 + A / Real.log |t| ^ 9)
  · calc
      ‖ζ' (↑σ + ↑t * I) / ζ (↑σ + ↑t * I)‖ ≤ C * Real.log |t| ^ 9 := ζbd_in σ t hyp_t h
      _ ≤ ((1 + C + C_triv) * A⁻¹) * Real.log |t| ^ 9 := by
          gcongr
          · calc
              C ≤ 1 + C := by simp only [le_add_iff_nonneg_left, zero_le_one]
              _ ≤ (1 + C + C_triv) * 1 := by simp only [mul_one, le_add_iff_nonneg_right]; positivity
              _ ≤ (1 + C + C_triv) * A⁻¹ := by gcongr

  · simp only [mem_Ico, tsub_le_iff_right, not_and, not_lt, mem_Ici] at h hyp_σ
    replace h := h hyp_σ
    calc
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ = ‖-ζ' (σ + t * I) / ζ (σ + t * I)‖ := by simp only [Complex.norm_div,
        norm_neg]

      _ ≤ (σ - 1)⁻¹ + C_triv := ζbd_out σ t (by exact T1 h)

      _ ≤ (A / Real.log |t| ^ 9)⁻¹ + C_triv := by
          gcongr
          · exact T2 h

      _ ≤ (A / Real.log |t| ^ 9)⁻¹ + C_triv * A⁻¹ := by
          gcongr
          exact le_mul_of_one_le_right pf_C_triv ha

      _ ≤ (1 + C_triv) * A⁻¹ * Real.log |t| ^ 9 := by
          simp only [inv_div]
          ring_nf
          gcongr
          · simp only [inv_pos, le_mul_iff_one_le_left, T0]
            linarith

      _ ≤ (1 + C + C_triv) * A⁻¹ * Real.log |t| ^ 9 := by gcongr; simp only [le_add_iff_nonneg_right]; positivity
