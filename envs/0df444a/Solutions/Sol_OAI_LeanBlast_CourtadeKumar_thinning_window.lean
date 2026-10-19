-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.thinning_window
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:56:49.313701+00:00
-- url     : https://prove2.me/submissions/c49208e9-2698-4ab1-aa46-7b0f9ad6c6ab

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/Window.lean:L92-L129
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.thinning_window. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SoftChannel204
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Model
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveInequality__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Comparison__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment__SoftChannel204
import Definitions.Def_OAI_InformationTheory_SoftChannel_Canonical
import Definitions.Def_OAI_InformationTheory_SoftChannel_Thinning
import Theorems.Thm_OAI_SoftChannel204_thinning_interval_aux

-- ---- from OAI.InformationTheory.BooleanNoise.EntropyScalars ----
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem ell_pos : 0 < ell := Real.log_pos (by norm_num)

theorem psi_nonneg (v : ℝ) : 0 ≤ psi v := by
  have h := Real.binEntropy_le_log_two (p := (1 + v) / 2)
  rw [← entropy_eq_binEntropy] at h
  unfold entropy ell at *
  linarith

theorem artanh_eq_log_sub {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    Real.artanh v = (Real.log (1 + v) - Real.log (1 - v)) / 2 := by
  rw [Real.artanh_eq_half_log ⟨hv.1.le, hv.2.le⟩,
    Real.log_div (by linarith [hv.1]) (by linarith [hv.2])]
  ring

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.EntropySeries ----
namespace OAI

noncomputable section

open Set Filter Finset
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

theorem psiCoeff_pos (k : ℕ) : 0 < psiCoeff k := by unfold psiCoeff; positivity

theorem psiCoeff_nonneg (k : ℕ) : 0 ≤ psiCoeff k := (psiCoeff_pos k).le

theorem hasSum_artanh {v : ℝ} (hv : |v| < 1) :
    HasSum (fun k : ℕ => v ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) (Real.artanh v) := by
  have h := (Real.hasSum_log_sub_log_of_abs_lt_one hv).mul_left (1 / 2)
  convert! h using 1
  · ext k
    ring
  · rw [artanh_eq_log_sub (abs_lt.mp hv)]
    ring

theorem psi_eq_mul_artanh_add_log {v : ℝ} (hv : |v| < 1) :
    psi v = v * Real.artanh v + 1 / 2 * Real.log (1 - v ^ 2) := by
  have hp : 1 + v ≠ 0 := by linarith [(abs_lt.mp hv).1]
  have hm : 1 - v ≠ 0 := by linarith [(abs_lt.mp hv).2]
  have hl : Real.log (1 - v ^ 2) = Real.log (1 + v) + Real.log (1 - v) := by
    rw [← Real.log_mul hp hm]
    congr 1
    ring
  rw [artanh_eq_log_sub (abs_lt.mp hv), hl]
  unfold psi
  ring

theorem hasSum_psi {v : ℝ} (hv : |v| < 1) :
    HasSum (fun k : ℕ => psiCoeff k * v ^ (2 * (k + 1))) (psi v) := by
  have hv2 : |v ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg v)]
    have h1 : 0 < 1 + v := by linarith [(abs_lt.mp hv).1]
    have h2 : 0 < 1 - v := by linarith [(abs_lt.mp hv).2]
    nlinarith [mul_pos h1 h2]
  have h := ((hasSum_artanh hv).mul_left v).add
    ((Real.hasSum_pow_div_log_of_abs_lt_one hv2).mul_left (-(1 / 2)))
  convert! h using 1
  · ext k
    have h1 : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (k : ℝ) + 1 ≠ 0 := by positivity
    have h3 : 2 * (k : ℝ) + 2 ≠ 0 := by positivity
    rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ]
    unfold psiCoeff
    field_simp
    ring
  · rw [psi_eq_mul_artanh_add_log hv]
    ring

theorem summable_psiCoeff : Summable psiCoeff := by
  have h : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  apply Summable.of_nonneg_of_le psiCoeff_nonneg ?_ h
  intro k
  unfold psiCoeff
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [sq_nonneg (k : ℝ), Nat.cast_nonneg (α := ℝ) k]

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.EntropyBounds ----
namespace OAI

noncomputable section

open Set Filter Finset
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

theorem norm_psiSeries_term_le {v : ℝ} (hv : |v| ≤ 1) (k : ℕ) :
    ‖psiCoeff k * v ^ (2 * (k + 1))‖ ≤ psiCoeff k := by
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (psiCoeff_nonneg k)]
  exact mul_le_of_le_one_right (psiCoeff_nonneg k)
    (pow_le_one₀ (abs_nonneg v) hv)

theorem summable_psi_closed {v : ℝ} (hv : |v| ≤ 1) :
    Summable (fun k : ℕ => psiCoeff k * v ^ (2 * (k + 1))) :=
  Summable.of_norm_bounded summable_psiCoeff (norm_psiSeries_term_le hv)

theorem continuousOn_psiSeries : ContinuousOn psiSeries (Icc (-1) 1) := by
  apply continuousOn_tsum
  · intro k
    fun_prop
  · exact summable_psiCoeff
  · intro k v hv
    exact norm_psiSeries_term_le (abs_le.mpr hv) k

theorem psiSeries_eq_psi {v : ℝ} (hv : |v| ≤ 1) : psiSeries v = psi v := by
  have h : EqOn psiSeries psi (Ioo (-1) 1) := by
    intro x hx
    exact (hasSum_psi (abs_lt.mpr hx)).tsum_eq
  have h' := h.of_subset_closure continuousOn_psiSeries continuous_psi.continuousOn
    Ioo_subset_Icc_self (show Icc (-1 : ℝ) 1 ⊆ closure (Ioo (-1) 1) by
      rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)])
  exact h' (abs_le.mp hv)

theorem hasSum_psi_closed {v : ℝ} (hv : |v| ≤ 1) :
    HasSum (fun k : ℕ => psiCoeff k * v ^ (2 * (k + 1))) (psi v) := by
  rw [← psiSeries_eq_psi hv]
  exact (summable_psi_closed hv).hasSum

theorem hasSum_psiCoeff : HasSum psiCoeff ell := by
  simpa using hasSum_psi_closed (v := 1) (by norm_num)

theorem psi_le_ell_mul_sq {v : ℝ} (hv : |v| ≤ 1) : psi v ≤ ell * v ^ 2 := by
  have hsq : v ^ 2 ≤ 1 := by
    have h := abs_le.mp hv
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2) (show 0 ≤ 1 + v by linarith [h.1])]
  apply hasSum_le _ (hasSum_psi_closed hv) (hasSum_psiCoeff.mul_right (v ^ 2))
  intro k
  apply mul_le_mul_of_nonneg_left _ (psiCoeff_nonneg k)
  rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add, pow_mul]
  exact mul_le_of_le_one_left (sq_nonneg v) (pow_le_one₀ (sq_nonneg v) hsq)

theorem ell_mul_one_sub_sq_le_entropy {v : ℝ} (hv : |v| ≤ 1) :
    ell * (1 - v ^ 2) ≤ entropy v := by
  have h := psi_le_ell_mul_sq hv
  unfold entropy
  nlinarith

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.PairEntropy ----
namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

theorem pair_mean_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) : a ∈ Set.Ioo (-1) 1 := by
  have ha : |a| < 1 := lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg b)) h
  exact abs_lt.mp ha

theorem pair_denom_add_pos (a b : ℝ) (h : |a| + |b| < 1) : 0 < 1 + a := by
  have ha := (pair_mean_mem_Ioo a b h).1
  linarith

theorem pair_denom_sub_pos (a b : ℝ) (h : |a| + |b| < 1) : 0 < 1 - a := by
  have ha := (pair_mean_mem_Ioo a b h).2
  linarith

theorem pair_abs_lt_denom_add (a b : ℝ) (h : |a| + |b| < 1) : |b| < 1 + a := by
  linarith [neg_le_abs a]

theorem pair_abs_lt_denom_sub (a b : ℝ) (h : |a| + |b| < 1) : |b| < 1 - a := by
  linarith [le_abs_self a]

private theorem div_mem_Ioo (s b : ℝ) (hs : 0 < s) (hb : |b| < s) :
    b / s ∈ Set.Ioo (-1) 1 := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hb
  constructor
  · apply (lt_div_iff₀ hs).2
    linarith
  · apply (div_lt_iff₀ hs).2
    linarith

theorem pair_ratio_add_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) :
    b / (1 + a) ∈ Set.Ioo (-1) 1 :=
  div_mem_Ioo (1 + a) b (pair_denom_add_pos a b h) (pair_abs_lt_denom_add a b h)

theorem pair_ratio_sub_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) :
    b / (1 - a) ∈ Set.Ioo (-1) 1 :=
  div_mem_Ioo (1 - a) b (pair_denom_sub_pos a b h) (pair_abs_lt_denom_sub a b h)

theorem pair_variance_pos (a b : ℝ) (h : |a| + |b| < 1) : 0 < 1 - a ^ 2 := by
  have hp := mul_pos (pair_denom_add_pos a b h) (pair_denom_sub_pos a b h)
  nlinarith

theorem pair_weighted_sq (a b : ℝ) (h : |a| + |b| < 1) :
    (1 + a) / 2 * (b / (1 + a)) ^ 2 + (1 - a) / 2 * (b / (1 - a)) ^ 2 =
      b ^ 2 / (1 - a ^ 2) := by
  have hp := ne_of_gt (pair_denom_add_pos a b h)
  have hm := ne_of_gt (pair_denom_sub_pos a b h)
  have hv := ne_of_gt (pair_variance_pos a b h)
  field_simp
  ring

private theorem weighted_psi_div (s b : ℝ) (hs : 0 < s) (hb : |b| < s) :
    s / 2 * psi (b / s) =
      (s + b) / 4 * Real.log (s + b) + (s - b) / 4 * Real.log (s - b) -
        s / 2 * Real.log s := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hb
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hp : s + b ≠ 0 := ne_of_gt (by linarith)
  have hm : s - b ≠ 0 := ne_of_gt (by linarith)
  have hplus : 1 + b / s = (s + b) / s := by field_simp
  have hminus : 1 - b / s = (s - b) / s := by field_simp
  rw [psi, hplus, hminus, Real.log_div hp hs0, Real.log_div hm hs0]
  field_simp
  ring

theorem pairEntropyGap_weighted (a b : ℝ) (h : |a| + |b| < 1) :
    pairEntropyGap a b =
      (1 + a) / 2 * psi (b / (1 + a)) + (1 - a) / 2 * psi (b / (1 - a)) := by
  rw [weighted_psi_div (1 + a) b (pair_denom_add_pos a b h) (pair_abs_lt_denom_add a b h),
    weighted_psi_div (1 - a) b (pair_denom_sub_pos a b h) (pair_abs_lt_denom_sub a b h)]
  unfold pairEntropyGap entropy psi
  ring_nf

theorem pairEntropyGap_nonneg (a b : ℝ) (h : |a| + |b| < 1) :
    0 ≤ pairEntropyGap a b := by
  rw [pairEntropyGap_weighted a b h]
  exact add_nonneg
    (mul_nonneg (by linarith [pair_denom_add_pos a b h]) (psi_nonneg _))
    (mul_nonneg (by linarith [pair_denom_sub_pos a b h]) (psi_nonneg _))

theorem pairEntropyGap_le_quadratic (a b : ℝ) (h : |a| + |b| < 1) :
    pairEntropyGap a b ≤ ell * (b ^ 2 / (1 - a ^ 2)) := by
  calc
    _ = (1 + a) / 2 * psi (b / (1 + a)) +
        (1 - a) / 2 * psi (b / (1 - a)) := pairEntropyGap_weighted a b h
    _ ≤ (1 + a) / 2 * (ell * (b / (1 + a)) ^ 2) +
        (1 - a) / 2 * (ell * (b / (1 - a)) ^ 2) :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (psi_le_ell_mul_sq (le_of_lt (abs_lt.mpr (pair_ratio_add_mem_Ioo a b h))))
          (by linarith [pair_denom_add_pos a b h]))
        (mul_le_mul_of_nonneg_left
          (psi_le_ell_mul_sq (le_of_lt (abs_lt.mpr (pair_ratio_sub_mem_Ioo a b h))))
          (by linarith [pair_denom_sub_pos a b h]))
    _ = ell * ((1 + a) / 2 * (b / (1 + a)) ^ 2 +
        (1 - a) / 2 * (b / (1 - a)) ^ 2) := by ring
    _ = _ := by rw [pair_weighted_sq a b h]

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.Thinning ----
namespace OAI

section

noncomputable section
open Set
namespace SoftChannel204

theorem thinning_cutoff_bound {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    4 * Real.log 2 * x ≤ (3 + x) * Real.log (1 + x) := by
  let f : ℝ → ℝ := fun y => (3 + y) * Real.log (1 + y) - 4 * Real.log 2 * y
  let f' : ℝ → ℝ := fun y =>
    Real.log (1 + y) + (3 + y) / (1 + y) - 4 * Real.log 2
  let f'' : ℝ → ℝ := fun y => (y - 1) / (1 + y) ^ 2
  have hd (y : ℝ) (hy : -1 < y) : HasDerivAt f (f' y) y := by
    have hn : 1 + y ≠ 0 := by linarith
    convert! ((((hasDerivAt_id y).const_add 3).mul
      (((hasDerivAt_id y).const_add 1).log hn)).sub
      ((hasDerivAt_id y).const_mul (4 * Real.log 2))) using 1;
      simp [f', div_eq_mul_inv]
  have hd' (y : ℝ) (hy : -1 < y) : HasDerivAt f' (f'' y) y := by
    have hn : 1 + y ≠ 0 := by linarith
    convert! ((((hasDerivAt_id y).const_add 1).log hn).add
      (((hasDerivAt_id y).const_add 3).div
        ((hasDerivAt_id y).const_add 1) hn)).sub_const (4 * Real.log 2) using 1
    dsimp [f'']
    field_simp
    ring
  have hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) f := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := f') (f'' := f'') (convex_Icc 0 1)
    · intro y hy
      exact (hd y (by linarith [hy.1])).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (hd y (by linarith [hy.1])).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (hd' y (by linarith [hy.1])).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hy.2]) (sq_nonneg _)
  have h := hc.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
    (show 0 ≤ 1 - x by linarith [hx.2]) hx.1 (by ring : 1 - x + x = 1)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at h
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 0 := by norm_num [f]
  rw [hf0, hf1] at h
  dsimp [f] at h
  linarith

theorem clipKernel_nonneg (β v : ℝ) : 0 ≤ clipKernel β v :=
  div_nonneg (le_max_right _ _) (sq_nonneg _)

open MeasureTheory

theorem continuousAt_clipKernel (β : ℝ) {v : ℝ} (hv : 0 < v) :
    ContinuousAt (clipKernel β) v := by
  unfold clipKernel
  exact ((continuousAt_id.sub continuousAt_const).max continuousAt_const).div
    (continuousAt_id.pow 2) (pow_ne_zero _ hv.ne')

theorem intervalIntegrable_clipKernel (β : ℝ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable (clipKernel β) volume u v := by
  apply ContinuousOn.intervalIntegrable
  intro w hw
  exact (continuousAt_clipKernel β
    (lt_of_lt_of_le (lt_min hu hv) hw.1)).continuousWithinAt

theorem thinning_interval {x u z : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hz0 : 0 ≤ z) (hzg : z < (1 - x) / (1 + x))
    (hulo : 1 - x - (1 + x) * z ≤ u) (huhi : u ≤ 1 - z) :
    (∫ v in u..u+z, clipKernel (Real.log (1 + x) / Real.log 2) v) ≤
      -(3 / 2 : ℝ) * Real.log (1 - ((1 - x) / (1 + x)) * z) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβ1 : Real.log (1 + x) / Real.log 2 ≤ 1 := by
    apply (div_le_one hL).mpr
    exact Real.log_le_log (by positivity) (by linarith)
  have hb := thinning_cutoff_bound ⟨hx0, hx1.le⟩
  have hcut : 4 * x / (3 + x) ≤ Real.log (1 + x) / Real.log 2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 3 + x) hL).mpr
    nlinarith
  exact thinning_interval_aux hx0 hx1 hβ1 hcut hz0 hzg hulo huhi

end SoftChannel204
end
end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.Window ----
namespace OAI

section

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace LeanBlast.CourtadeKumar
open SoftChannel204

lemma clipKernel_scaled (b v : ℝ) :
    ell * clipKernel b (ell*v) = clipKernel (b/ell) v := by
  have hL := ell_pos
  have he : ell*v-b = ell*(v-b/ell) := by field_simp
  have hm : max (ell*(v-b/ell)) 0 = ell*max (v-b/ell) 0 := by
    simpa using (mul_max_of_nonneg (v-b/ell) 0 hL.le).symm
  rw [clipKernel,clipKernel,he,hm]
  simp only [mul_pow]
  field_simp

lemma clipKernel_integral_scaled (b q s : ℝ) :
    (∫ h in q..s, clipKernel b h) = ∫ v in q/ell..s/ell, clipKernel (b/ell) v := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := q/ell) (b := s/ell)
    (clipKernel b) ell
  simp only [smul_eq_mul, mul_div_cancel₀ _ ell_pos.ne'] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v _
  exact clipKernel_scaled b v

lemma entropy_interval_bound {x z q s : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hz0 : 0 ≤ z) (hzg : z < (1-x)/(1+x))
    (hql : ell*(1-x-(1+x)*z) ≤ q) (hqs : q ≤ s)
    (hsL : s ≤ ell) (hJ : s-q ≤ ell*z) :
    (∫ h in q..s, clipKernel (Real.log (1+x)) h) ≤
      -(3/2:ℝ)*Real.log (1-((1-x)/(1+x))*z) := by
  have hL := ell_pos
  have hp : 0 < 1+x := by linarith
  have hlo : 0 < 1-x-(1+x)*z := by
    have := (lt_div_iff₀ hp).mp hzg
    nlinarith
  have hq0 : 0 < q := (mul_pos hL hlo).trans_le hql
  let u := min (q/ell) (1-z)
  have hzl : 1-x-(1+x)*z ≤ 1-z := by nlinarith
  have hul : 1-x-(1+x)*z ≤ u := le_min ((le_div_iff₀ hL).mpr (by simpa only [mul_comm] using hql)) hzl
  have huh : u ≤ 1-z := min_le_right _ _
  have huq : u ≤ q/ell := min_le_left _ _
  have hss : s/ell ≤ u+z := by
    dsimp [u]
    rw [← min_add_add_right]
    apply le_min
    · apply (div_le_iff₀ hL).mpr
      have : q/ell*ell = q := div_mul_cancel₀ q hL.ne'
      nlinarith
    · simpa using (div_le_one hL).mpr hsL
  have hu0 : 0 < u := hlo.trans_le hul
  have huz0 : 0 < u+z := by linarith
  rw [clipKernel_integral_scaled]
  calc
    _ ≤ ∫ v in u..u+z, clipKernel (Real.log (1+x)/ell) v :=
      intervalIntegral.integral_mono_interval huq ((div_le_div_iff_of_pos_right hL).mpr hqs)
        hss (Filter.Eventually.of_forall (fun v => clipKernel_nonneg _ v))
        (intervalIntegrable_clipKernel _ hu0 huz0)
    _ ≤ _ := by
      exact thinning_interval hx0 hx1 hz0 hzg hul huh

lemma thinning_window {x d e : ℝ} (hx : 0 ≤ x) (hd : 0 < d) (hxd : x+d < 1)
    (hefloor : (1-x)*entropy (d/(1-x)) ≤ e)
    (hehi : e ≤ (entropy (x+d)+entropy (x-d))/2) :
    (∫ h in (e+psi x)..(e+ell-(entropy (x+d)+entropy (x-d))/2),
      clipKernel (Real.log (1+x)) h) ≤
      -(3/2:ℝ)*Real.log (1-d^2/(1+x)^2) := by
  have hs : 0 < 1-x := by linarith
  have hp : 0 < 1+x := by linarith
  have hh : |x|+|d| < 1 := by rw [abs_of_nonneg hx,abs_of_pos hd]; exact hxd
  let z := d^2/((1-x)*(1+x))
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hdz : z < (1-x)/(1+x) := by
    dsimp [z]
    apply (div_lt_div_iff₀ (mul_pos hs hp) hp).mpr
    nlinarith [mul_pos (show 0 < 1-x-d by linarith) (show 0 < 1-x+d by linarith)]
  have hratio : |d/(1-x)| ≤ 1 := by
    rw [abs_of_pos (div_pos hd hs)]
    exact (div_le_one hs).mpr (by linarith)
  have hfloor := mul_le_mul_of_nonneg_left (ell_mul_one_sub_sq_le_entropy hratio) hs.le
  have hfloorEq : (1-x)*(ell*(1-(d/(1-x))^2)) = ell*(1-x-(1+x)*z) := by
    dsimp [z]; field_simp
  rw [hfloorEq] at hfloor
  have hql : ell*(1-x-(1+x)*z) ≤ e+psi x := by linarith [psi_nonneg x]
  have hqs : e+psi x ≤ e+ell-(entropy (x+d)+entropy (x-d))/2 := by
    have h := pairEntropyGap_nonneg x d hh
    simp only [pairEntropyGap,entropy] at h ⊢
    linarith
  have hJ : e+ell-(entropy (x+d)+entropy (x-d))/2-(e+psi x) ≤ ell*z := by
    have h := pairEntropyGap_le_quadratic x d hh
    have heq : 1-x^2 = (1-x)*(1+x) := by ring
    rw [heq] at h
    change pairEntropyGap x d ≤ ell*z at h
    simp only [pairEntropyGap,entropy] at h ⊢
    linarith
  have hzEq : ((1-x)/(1+x))*z = d^2/(1+x)^2 := by
    dsimp [z]; field_simp
  have H := entropy_interval_bound hx (by linarith) hz hdz hql hqs (by linarith) hJ
  rwa [hzEq] at H

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set MeasureTheory
open scoped Topology
open SoftChannel204


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.thinning_window := @_root_.OAI.LeanBlast.CourtadeKumar.thinning_window
