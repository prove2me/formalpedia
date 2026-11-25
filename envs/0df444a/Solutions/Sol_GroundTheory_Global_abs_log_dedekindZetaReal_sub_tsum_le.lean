-- Prove2me | solution 1 for GroundTheory.Global.abs_log_dedekindZetaReal_sub_tsum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:25:05.352308+00:00
-- url     : https://prove2.me/submissions/badd257d-1ea3-4595-90b7-eef9cc3c82f1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Theorems.Thm_GroundTheory_Global_exp_sub_sq_le_one_add
import Theorems.Thm_GroundTheory_Global_rpow_neg_absNorm_le_half
import Theorems.Thm_GroundTheory_Global_prod_one_add_rpow_neg_eq_sum
import Theorems.Thm_GroundTheory_Global_sum_rpow_neg_le_dedekindZetaReal
import Theorems.Thm_GroundTheory_Global_one_le_dedekindZetaReal
import Theorems.Thm_GroundTheory_Global_dedekindZetaReal_le_exp
import Theorems.Thm_GroundTheory_Global_one_le_absNorm
import Theorems.Thm_GroundTheory_Global_summable_absNorm_rpow_neg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Global
theorem _root_.solution {s : ℝ} (hs : 1 < s)
    (hζ : Summable (dedekindZetaTerm K s)) :
    |Real.log (dedekindZetaReal K s) -
        ∑' w : HeightOneSpectrum (𝓞 K), (absNorm w.asIdeal : ℝ) ^ (-s)| ≤
      2 * ∑' w : HeightOneSpectrum (𝓞 K), (absNorm w.asIdeal : ℝ) ^ (-(2 : ℝ)) := by
  set x := fun w : HeightOneSpectrum (𝓞 K) => (absNorm w.asIdeal : ℝ) ^ (-s) with hx
  set y := fun w : HeightOneSpectrum (𝓞 K) => (absNorm w.asIdeal : ℝ) ^ (-(2 : ℝ)) with hy
  have hxs : Summable x := summable_absNorm_rpow_neg hs
  have hys : Summable y := summable_absNorm_rpow_neg (by norm_num)
  have hx0 : ∀ w, 0 ≤ x w := fun w => by positivity
  have hxy : ∀ w, x w ^ 2 ≤ y w := by
    intro w
    have h1 : (1 : ℝ) ≤ absNorm w.asIdeal := by exact_mod_cast one_le_absNorm w
    simp only [x, y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le h1 (by push_cast; linarith)
  have hx2s : Summable fun w => x w ^ 2 :=
    Summable.of_nonneg_of_le (fun w => by positivity) hxy hys
  have hQ : ∑' w, x w ^ 2 ≤ ∑' w, y w := Summable.tsum_le_tsum hxy hx2s hys
  have hQ0 : 0 ≤ ∑' w, x w ^ 2 := tsum_nonneg fun w => by positivity
  have hζpos : 0 < dedekindZetaReal K s := lt_of_lt_of_le one_pos (one_le_dedekindZetaReal hζ)
  have hup : Real.log (dedekindZetaReal K s) ≤ ∑' w, x w + 2 * ∑' w, x w ^ 2 := by
    rw [Real.log_le_iff_le_exp hζpos]
    have := dedekindZetaReal_le_exp (K := K) hs
    rwa [Summable.tsum_add hxs (hx2s.mul_left 2), tsum_mul_left] at this
  have hlow : ∑' w, x w - ∑' w, x w ^ 2 ≤ Real.log (dedekindZetaReal K s) := by
    rw [← Summable.tsum_sub hxs hx2s]
    refine (hxs.sub hx2s).tsum_le_of_sum_le fun F => ?_
    rw [Real.le_log_iff_exp_le hζpos, Real.exp_sum]
    calc ∏ w ∈ F, Real.exp (x w - x w ^ 2) ≤ ∏ w ∈ F, (1 + x w) :=
          Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
            (fun w _ => exp_sub_sq_le_one_add (hx0 w) (rpow_neg_absNorm_le_half w.prime hs.le))
      _ = _ := prod_one_add_rpow_neg_eq_sum F s
      _ ≤ _ := sum_rpow_neg_le_dedekindZetaReal _ hζ
  rw [abs_le]
  constructor <;> linarith
end GroundTheory.Global
