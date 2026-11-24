-- Prove2me | solution 1 for GlobalTheory.exists_pnorm_eq_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:45:51.144269+00:00
-- url     : https://prove2.me/submissions/2d7d7974-093a-4b52-b81f-f32064f982d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_ScaledBoundInequality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormProdSignMulDetSubmatrixSubOneLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Matrix hiding gram
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory
theorem _root_.solution {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (y : Frame X.Ψ r) {t : ℝ}
    (hy : ∀ τ i, dmin X.Gm y τ i ≠ 0 ∧ |Real.log ‖dmin X.Gm y τ i‖| ≤ t) :
    ∃ s : ℝ, |s| ≤ t * ∑ τ, ∑ i, |(la τ i : ℝ)| ∧
      ∀ P : Frame X.Ψ r → ℂ, X.pnorm la P y = ‖P y‖ * Real.exp s := by
  refine ⟨∑ τ, ∑ i : Fin r, Real.log ‖dmin X.Gm y τ i.succ / dmin X.Gm y τ i.castSucc‖ *
    (-(la τ i : ℝ) / 2), ?_, fun P => ?_⟩
  · rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    obtain ⟨h1, h2⟩ := hy τ i.succ
    obtain ⟨h3, h4⟩ := hy τ i.castSucc
    rw [norm_div, Real.log_div (norm_ne_zero_iff.2 h1) (norm_ne_zero_iff.2 h3), abs_mul, abs_div,
      abs_neg, abs_two]
    have h5 := abs_sub (Real.log ‖dmin X.Gm y τ i.succ‖) (Real.log ‖dmin X.Gm y τ i.castSucc‖)
    nlinarith [abs_nonneg (la τ i : ℝ)]
  · rw [Data.pnorm, Real.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact Real.rpow_def_of_pos (norm_pos_iff.2 (div_ne_zero (hy τ _).1 (hy τ _).1)) _
end GlobalTheory
