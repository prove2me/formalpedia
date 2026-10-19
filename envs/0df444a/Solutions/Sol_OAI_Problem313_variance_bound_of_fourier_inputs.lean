-- Prove2me | solution 1 for OAI.Problem313.variance_bound_of_fourier_inputs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:39:37.292868+00:00
-- url     : https://prove2.me/submissions/5ed17135-77c4-4188-9a22-8308cea1ae0b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/VarianceReduction.lean:L35-L58
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.variance_bound_of_fourier_inputs. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Theorems.Thm_OAI_Problem313_quadratic_mul_exp_neg_eighth_le
import Theorems.Thm_OAI_Problem313_variance_from_fourier_capture
import Theorems.Thm_OAI_Problem313_variance_le_dirichlet_of_fourier

-- ---- from OAI.Combinatorics.SharpThreshold.SpectralBounds ----
namespace OAI

universe u

noncomputable section

namespace Problem313

/-- A more flexible numerical budget, useful with coarse exponential estimates. -/
theorem variance_constant_assembly_budget (t ell lowConstant budget : ℝ)
    (ht : 0 < t) (hell : t / 3 ≤ ell)
    (hlow : lowConstant ≤ budget / t ^ 2)
    (hbudget : budget + 73728 ≤ (2 : ℝ) ^ 17) :
    lowConstant + 8192 / ell ^ 2 ≤ (2 : ℝ) ^ 17 / t ^ 2 := by
  have hellpos : 0 < ell := lt_of_lt_of_le (by positivity : 0 < t / 3) hell
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ t / 3) hell
  have htail : 8192 / ell ^ 2 ≤ 73728 / t ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hellpos) (sq_pos_of_pos ht)).2
    nlinarith
  calc
    lowConstant + 8192 / ell ^ 2 ≤ budget / t ^ 2 + 73728 / t ^ 2 :=
      add_le_add hlow htail
    _ = (budget + 73728) / t ^ 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hbudget (sq_nonneg t)

/-- A small logarithm only needs the elementary Poincaré bound. -/
theorem variance_small_log_assembly (t variance influence : ℝ)
    (ht : 0 < t) (htsmall : t ≤ 16) (hinfluence : 0 ≤ influence)
    (hpoincare : variance ≤ influence / 4) :
    variance ≤ ((2 : ℝ) ^ 17 / t ^ 2) * influence := by
  have hsq : t ^ 2 ≤ 256 := by nlinarith
  have hfactor : (1 / 4 : ℝ) ≤ (2 : ℝ) ^ 17 / t ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos ht)).2
    norm_num
    nlinarith
  calc
    variance ≤ (1 / 4 : ℝ) * influence := by linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor hinfluence

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.ExpQuadratic ----
namespace OAI

noncomputable section

namespace Problem313

/-- A form requiring only the logarithmic lower bound used for the spectral tail. -/
lemma block_exponential_remainder_le_of_third (t ell : ℝ) (ht : 0 ≤ t)
    (hell : t / 3 ≤ ell) :
    (4 * Real.exp (-ell / 4)) * t ^ 2 ≤ 2304 := by
  have hquad := quadratic_mul_exp_neg_eighth_le (2 * t / 3) (by positivity)
  have harg : -(2 * t / 3) / 8 = -t / 12 := by ring
  rw [harg] at hquad
  have hmono : Real.exp (-ell / 4) ≤ Real.exp (-t / 12) :=
    Real.exp_le_exp.mpr (by linarith)
  have hmul := mul_le_mul_of_nonneg_right hmono (sq_nonneg t)
  nlinarith

/-- The fractional-power form of the block remainder estimate. -/
lemma block_rpow_remainder_le (t m : ℝ) (ht : 0 ≤ t) (hm : 0 < m)
    (hm_log : t / 3 ≤ Real.log m) :
    (4 * m ^ (-1 / 4 : ℝ)) * t ^ 2 ≤ 2304 := by
  rw [Real.rpow_def_of_pos hm]
  have harg : Real.log m * (-1 / 4 : ℝ) = -Real.log m / 4 := by ring
  rw [harg]
  exact block_exponential_remainder_le_of_third t (Real.log m) ht hm_log

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.VarianceReduction ----
namespace OAI

universe u

noncomputable section

namespace Problem313

/-- The graph-independent final step of the variance proof: capture at squared
logarithmic degree, together with Parseval and the Dirichlet identity, yields
the exact advertised numerical constant. -/
theorem variance_bound_of_fourier_capture {ι : Type u} [Fintype ι] [DecidableEq ι]
    (coeff : Finset ι → ℝ) (variance sigma influence t m : ℝ)
    (hsigma : 0 < sigma) (hinfluence : 0 ≤ influence)
    (ht : 0 < t) (hm : 0 < m) (hlog : t / 3 ≤ Real.log m)
    (hvariance : variance = ∑ S : Finset ι with S.Nonempty, coeff S ^ 2)
    (hdirichlet : (∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2) = sigma ^ 2 * influence)
    (hcapture : (∑ S : Finset ι with S.Nonempty ∧
        (S.card : ℝ) ≤ (sigma * Real.log m / 64) ^ 2 / 2, coeff S ^ 2)
      ≤ (4 * m ^ (-1 / 4 : ℝ)) * influence) :
    variance ≤ ((2 : ℝ) ^ 17 / t ^ 2) * influence := by
  have hell : 0 < Real.log m := lt_of_lt_of_le (by positivity : 0 < t / 3) hlog
  have hpre := variance_from_fourier_capture coeff variance sigma (Real.log m)
    influence (4 * m ^ (-1 / 4 : ℝ)) hsigma hell hvariance hdirichlet hcapture
  have hrem : 4 * m ^ (-1 / 4 : ℝ) ≤ 2304 / t ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos ht)).2
    exact block_rpow_remainder_le t m ht.le hm hlog
  have hconstant := variance_constant_assembly_budget t (Real.log m)
    (4 * m ^ (-1 / 4 : ℝ)) 2304 ht hlog hrem (by norm_num)
  exact hpre.trans (mul_le_mul_of_nonneg_right hconstant hinfluence)

/-- A complete numerical reduction for all logarithmic scales. The only
large-scale input remaining is capture of low Fourier supports. -/
theorem variance_bound_of_fourier_inputs {ι : Type u} [Fintype ι] [DecidableEq ι]
    (coeff : Finset ι → ℝ) (variance sigma influence t : ℝ)
    (hsigma : 0 < sigma) (hsigma_sq : sigma ^ 2 ≤ 1 / 4)
    (hinfluence : 0 ≤ influence) (ht : 0 < t)
    (hvariance : variance = ∑ S : Finset ι with S.Nonempty, coeff S ^ 2)
    (hdirichlet : (∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2) = sigma ^ 2 * influence)
    (hcapture : 16 ≤ t → ∃ m : ℝ, 0 < m ∧ t / 3 ≤ Real.log m ∧
      (∑ S : Finset ι with S.Nonempty ∧
        (S.card : ℝ) ≤ (sigma * Real.log m / 64) ^ 2 / 2, coeff S ^ 2)
        ≤ (4 * m ^ (-1 / 4 : ℝ)) * influence) :
    variance ≤ ((2 : ℝ) ^ 17 / t ^ 2) * influence := by
  by_cases hlarge : 16 ≤ t
  · obtain ⟨m, hm, hlog, hcap⟩ := hcapture hlarge
    exact variance_bound_of_fourier_capture coeff variance sigma influence t m
      hsigma hinfluence ht hm hlog hvariance hdirichlet hcap
  · have hpoincare := variance_le_dirichlet_of_fourier coeff variance
      (sigma ^ 2 * influence) hvariance hdirichlet
    have hquarter : variance ≤ influence / 4 := by
      have h := mul_le_mul_of_nonneg_right hsigma_sq hinfluence
      linarith
    exact variance_small_log_assembly t variance influence ht (by linarith)
      hinfluence hquarter

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution.{u} : type_of% @_root_.OAI.Problem313.variance_bound_of_fourier_inputs.{u} := @_root_.OAI.Problem313.variance_bound_of_fourier_inputs.{u}
