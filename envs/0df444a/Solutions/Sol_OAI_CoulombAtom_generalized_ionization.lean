-- Prove2me | solution 1 for OAI.CoulombAtom.generalized_ionization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:51:40.444021+00:00
-- url     : https://prove2.me/submissions/b58db544-6e53-40b7-b62d-8aca7f726ce4

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010
import Theorems.Thm_OAI_CoulombAtom_actual_uniform_upper_deficit
import Theorems.Thm_OAI_CoulombBarrier_exists_actual_selected_data_constants
import Theorems.Thm_OAI_CoulombBarrier_selected_data_profile_subsequence

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_RadialPower
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
namespace CoulombPDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma radialPower_pos (a : ℝ) {x : E} (hx : x ≠ 0) : 0 < radialPower a x :=
  Real.rpow_pos_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hx)) a

lemma exists_small_rpow_bound {s : ℝ} (hs : 0 < s) (M : ℝ) :
    ∃ a > 0, ∀ t : ℝ, 0 < t → t ≤ a → M ≤ t ^ (-s) := by
  have he := (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hs)).eventually (eventually_ge_atTop M)
  obtain ⟨b, hb, hsub⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨b / 2, by positivity, ?_⟩
  intro t ht htb
  apply hsub
  exact ⟨by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using
    (show t < b by linarith), ht⟩

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma exists_small_radialPower_bound {s : ℝ} (hs : 0 < s) (M : ℝ) :
    ∃ a > 0, ∀ x : E, x ≠ 0 → ‖x‖ ≤ a → M ≤ radialPower (-s) x := by
  obtain ⟨b, hb, hbound⟩ := exists_small_rpow_bound hs M
  refine ⟨min 1 b, lt_min (by norm_num) hb, ?_⟩
  intro x hx ha
  have h1 : ‖x‖ ≤ 1 := ha.trans (min_le_left _ _)
  have hb' : ‖x‖ ≤ b := ha.trans (min_le_right _ _)
  apply hbound _ (sq_pos_of_pos (norm_pos_iff.mpr hx))
  nlinarith [norm_nonneg x]

lemma exists_small_exponent {q : ℝ} (hq : 12 < q) :
    ∃ s > 0, 12 + 14 * s + 4 * s ^ 2 ≤ q := by
  let s := min 1 ((q - 12) / 36)
  have hs : 0 < s := lt_min (by norm_num) (by positivity)
  have h1 : s ≤ 1 := min_le_left _ _
  have hq' : s ≤ (q - 12) / 36 := min_le_right _ _
  refine ⟨s, hs, ?_⟩
  nlinarith [mul_nonneg hs.le (sub_nonneg.mpr h1)]

lemma rpow_three_halves_upper {B v : ℝ} (hv : 0 ≤ v) (hB : v ≤ B) :
    v ^ (3 / 2 : ℝ) ≤ B ^ (1 / 2 : ℝ) * v := by
  rw [rpow_three_halves v hv]
  have h := Real.rpow_le_rpow hv hB (by norm_num : (0 : ℝ) ≤ 1 / 2)
  nlinarith [mul_nonneg hv (sub_nonneg.mpr h)]

end CoulombPDE

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_SommerfeldCoefficient
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
namespace CoulombPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

lemma lower_barrier_laplacian {d B e s c c₀ F : ℝ} (hd : 0 ≤ d)
    (he : 0 ≤ e) (hs : 0 ≤ s) (hc : 0 ≤ c) (hc₀ : 0 < c₀)
    (hq : d * B ^ (1 / 2 : ℝ) ≤ 12)
    (hκ : (14 * s + 4 * s ^ 2) * B ≤ (12 - d * B ^ (1 / 2 : ℝ)) * c₀)
    {x : Space} (hx : x ≠ 0) (hlow : c₀ * radialPower (-2) x ≤ F)
    (hgt : F < radialCombination B (-e) s (-c) x) :
    reaction d F ≤ Δ (radialCombination B (-e) s (-c)) x := by
  let z := e * radialPower (-s) x
  let v := B - z
  have hz : 0 ≤ z := mul_nonneg he (radialPower_nonneg _ _)
  have hp := radialPower_pos (-2) hx
  have hfac : radialCombination B (-e) s (-c) x = radialPower (-2) x * v - c := by
    rw [radialCombination_factor _ _ _ _ hx]; dsimp [v, z]; ring
  have hv : c₀ < v := by
    rw [hfac] at hgt
    nlinarith
  have hvpos : 0 < v := hc₀.trans hv
  have hvB : v ≤ B := by dsimp [v]; linarith
  have hzB : z ≤ B := by dsimp [v] at hvpos; linarith
  have hf : max (F - 1) 0 ≤ radialPower (-2) x * v := by
    apply max_le
    · rw [hfac] at hgt; linarith
    · positivity
  have hcoeff : 0 ≤ 14 * s + 4 * s ^ 2 := by positivity
  have hscalar : d * B ^ (1 / 2 : ℝ) * v ≤ 12 * B - (12 + 14 * s + 4 * s ^ 2) * z := by
    have h1 := mul_le_mul_of_nonneg_left hzB hcoeff
    have h2 := mul_le_mul_of_nonneg_left hv.le (sub_nonneg.mpr hq)
    dsimp [v] at *
    nlinarith
  calc
    reaction d F ≤ d * (radialPower (-2) x * v) ^ (3 / 2 : ℝ) := by
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_max_right _ _) hf (by norm_num)) hd
    _ = radialPower (-3) x * (d * v ^ (3 / 2 : ℝ)) := by
      rw [radial_scaled_reaction hvpos.le]; ring
    _ ≤ radialPower (-3) x * (d * B ^ (1 / 2 : ℝ) * v) := by
      apply mul_le_mul_of_nonneg_left _ (radialPower_nonneg _ _)
      have h := mul_le_mul_of_nonneg_left (rpow_three_halves_upper hvpos.le hvB) hd
      nlinarith
    _ ≤ radialPower (-3) x * (12 * B - (12 + 14 * s + 4 * s ^ 2) * z) :=
      mul_le_mul_of_nonneg_left hscalar (radialPower_nonneg _ _)
    _ = Δ (radialCombination B (-e) s (-c)) x := by
      rw [radialCombination_laplacian _ _ _ _ hx]; dsimp [z]; ring

theorem singular_upper_bound {F : Space → ℝ} {d C R B : ℝ}
    (hd : 0 < d) (hC : 0 ≤ C) (hR : 0 < R) (hB : 0 < B)
    (hq : 12 < d * B ^ (1 / 2 : ℝ))
    (hreg : ∀ x, x ≠ 0 → ‖x‖ ≤ R → ContDiffAt ℝ 2 F x)
    (hpde : ∀ x, x ≠ 0 → ‖x‖ ≤ R → Δ F x = reaction d (F x))
    (hupper : ∀ x, x ≠ 0 → ‖x‖ ≤ R → F x ≤ C * radialPower (-2) x) :
    ∀ x, x ≠ 0 → ‖x‖ ≤ R →
      F x ≤ B * radialPower (-2) x + C * (R ^ 2) ^ (-2 : ℝ) + 1 := by
  obtain ⟨s, hs, hκ⟩ := exists_small_exponent hq
  let c : ℝ := C * (R ^ 2) ^ (-2 : ℝ)
  have hc : 0 ≤ c := mul_nonneg hC (Real.rpow_nonneg (sq_nonneg R) _)
  have heBound (e : ℝ) (he : 0 < e) : ∀ x, x ≠ 0 → ‖x‖ ≤ R →
      F x ≤ radialCombination B e s (c + 1) x := by
    have hm := punctured_ball_maximum_principle (u := F - radialCombination B e s (c + 1))
      (fun x hx hr => (hreg x hx hr).sub (radialCombination_contDiffAt _ _ _ _ hx))
      (fun x hx hr hp => ?_) (fun x hx => ?_) ?_
    · intro x hx hr
      exact sub_nonpos.mp (hm x hx hr)
    · rw [(hreg x hx hr).laplacian_sub (radialCombination_contDiffAt _ _ _ _ hx), hpde x hx hr]
      have hu := upper_barrier_laplacian hd.le hB he.le (by linarith : 1 ≤ c + 1) hq.le hκ hx
      have hmon := reaction_monotone hd.le (show radialCombination B e s (c + 1) x ≤ F x by
        exact le_of_lt (sub_pos.mp hp))
      linarith
    · have hx0 : x ≠ 0 := norm_pos_iff.mp (hx ▸ hR)
      have hu := hupper x hx0 hx.le
      have hrad : C * radialPower (-2) x = c := by simp only [radialPower, hx, c]
      rw [hrad] at hu
      have h1 := radialPower_nonneg (-2 : ℝ) x
      have h2 := radialPower_nonneg (-2 - s) x
      change F x - radialCombination B e s (c + 1) x ≤ 0
      unfold radialCombination
      nlinarith [mul_nonneg hB.le h1, mul_nonneg he.le h2]
    · obtain ⟨a, ha, hsmall⟩ := exists_small_radialPower_bound (E := Space) hs (C / e)
      refine ⟨min a R, lt_min ha hR, ?_⟩
      intro x hx hxa
      have ht := hsmall x hx (hxa.trans (min_le_left _ _))
      have hu := hupper x hx (hxa.trans (min_le_right _ _))
      have heC : C ≤ e * radialPower (-s) x := by
        have ht' := (div_le_iff₀ he).mp ht
        nlinarith
      change F x - radialCombination B e s (c + 1) x ≤ 0
      rw [radialCombination_factor _ _ _ _ hx]
      nlinarith [mul_nonneg (radialPower_nonneg (-2) x) (sub_nonneg.mpr heC),
        mul_nonneg hB.le (radialPower_nonneg (-2) x)]
  intro x hx hr
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hp := radialPower_pos (-2 - s) hx
  have h := heBound (δ / radialPower (-2 - s) x) (div_pos hδ hp) x hx hr
  unfold radialCombination at h
  rw [div_mul_cancel₀ _ hp.ne'] at h
  change F x ≤ B * radialPower (-2) x + c + 1 + δ
  linarith

theorem singular_lower_bound {F : Space → ℝ} {d c₀ R B : ℝ}
    (hd : 0 < d) (hc₀ : 0 < c₀) (hR : 0 < R) (hB : 0 < B)
    (hq : d * B ^ (1 / 2 : ℝ) < 12)
    (hreg : ∀ x, x ≠ 0 → ‖x‖ ≤ R → ContDiffAt ℝ 2 F x)
    (hpde : ∀ x, x ≠ 0 → ‖x‖ ≤ R → Δ F x = reaction d (F x))
    (hlower : ∀ x, x ≠ 0 → ‖x‖ ≤ R → c₀ * radialPower (-2) x ≤ F x) :
    ∀ x, x ≠ 0 → ‖x‖ ≤ R →
      B * radialPower (-2) x - B * (R ^ 2) ^ (-2 : ℝ) ≤ F x := by
  let q := d * B ^ (1 / 2 : ℝ)
  have hgap : 0 < (12 - q) * c₀ / B := div_pos (mul_pos (sub_pos.mpr hq) hc₀) hB
  obtain ⟨s, hs, hsκ⟩ := exists_small_exponent (show 12 < 12 + (12 - q) * c₀ / B by linarith)
  have hκ : (14 * s + 4 * s ^ 2) * B ≤ (12 - q) * c₀ := by
    apply (le_div_iff₀ hB).mp
    linarith
  let c : ℝ := B * (R ^ 2) ^ (-2 : ℝ)
  have hc : 0 ≤ c := mul_nonneg hB.le (Real.rpow_nonneg (sq_nonneg R) _)
  have heBound (e : ℝ) (he : 0 < e) : ∀ x, x ≠ 0 → ‖x‖ ≤ R →
      radialCombination B (-e) s (-c) x ≤ F x := by
    have hm := punctured_ball_maximum_principle (u := radialCombination B (-e) s (-c) - F)
      (fun x hx hr => (radialCombination_contDiffAt _ _ _ _ hx).sub (hreg x hx hr))
      (fun x hx hr hp => ?_) (fun x hx => ?_) ?_
    · intro x hx hr
      exact sub_nonpos.mp (hm x hx hr)
    · rw [(radialCombination_contDiffAt _ _ _ _ hx).laplacian_sub (hreg x hx hr), hpde x hx hr]
      exact sub_nonneg.mpr (lower_barrier_laplacian hd.le he.le hs.le hc hc₀ hq.le hκ hx
        (hlower x hx hr) (sub_pos.mp hp))
    · have hx0 : x ≠ 0 := norm_pos_iff.mp (hx ▸ hR)
      have hl := hlower x hx0 hx.le
      have hrad : B * radialPower (-2) x = c := by simp only [radialPower, hx, c]
      change radialCombination B (-e) s (-c) x - F x ≤ 0
      unfold radialCombination
      rw [hrad]
      nlinarith [mul_nonneg hc₀.le (radialPower_nonneg (-2) x),
        mul_nonneg he.le (radialPower_nonneg (-2 - s) x)]
    · obtain ⟨a, ha, hsmall⟩ := exists_small_radialPower_bound (E := Space) hs (B / e)
      refine ⟨min a R, lt_min ha hR, ?_⟩
      intro x hx hxa
      have ht := hsmall x hx (hxa.trans (min_le_left _ _))
      have hl := hlower x hx (hxa.trans (min_le_right _ _))
      have heB : B ≤ e * radialPower (-s) x := by
        have ht' := (div_le_iff₀ he).mp ht
        nlinarith
      change radialCombination B (-e) s (-c) x - F x ≤ 0
      rw [radialCombination_factor _ _ _ _ hx]
      nlinarith [mul_nonneg (radialPower_nonneg (-2) x) (sub_nonneg.mpr heB),
        mul_nonneg hc₀.le (radialPower_nonneg (-2) x)]
  intro x hx hr
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hp := radialPower_pos (-2 - s) hx
  have h := heBound (δ / radialPower (-2 - s) x) (div_pos hδ hp) x hx hr
  unfold radialCombination at h
  rw [neg_mul, div_mul_cancel₀ _ hp.ne'] at h
  change B * radialPower (-2) x - c ≤ F x + δ
  linarith

theorem sommerfeld_asymptotic {F : Space → ℝ} {d c C R : ℝ}
    (hd : 0 < d) (hc : 0 < c) (hC : 0 ≤ C) (hR : 0 < R)
    (hreg : ∀ x, x ≠ 0 → ‖x‖ ≤ R → ContDiffAt ℝ 2 F x)
    (hpde : ∀ x, x ≠ 0 → ‖x‖ ≤ R → Δ F x = reaction d (F x))
    (hlower : ∀ x, x ≠ 0 → ‖x‖ ≤ R → c * radialPower (-2) x ≤ F x)
    (hupper : ∀ x, x ≠ 0 → ‖x‖ ≤ R → F x ≤ C * radialPower (-2) x) :
    Tendsto (fun x => ‖x‖ ^ 4 * F x) (𝓝[≠] (0 : Space)) (𝓝 (sommerfeldCoefficient d)) := by
  have hA : 0 < sommerfeldCoefficient d := sommerfeldCoefficient_pos hd
  have hn : Tendsto (fun x : Space => ‖x‖) (𝓝[≠] (0 : Space)) (𝓝 0) := by
    simpa only [norm_zero] using (continuous_norm.continuousAt.tendsto (x := (0 : Space))).mono_left nhdsWithin_le_nhds
  have hfour : Tendsto (fun x : Space => ‖x‖ ^ 4) (𝓝[≠] (0 : Space)) (𝓝 0) := by
    simpa using hn.pow 4
  have hball : ∀ᶠ x : Space in 𝓝[≠] (0 : Space), x ≠ 0 ∧ ‖x‖ ≤ R := by
    have hsmall : ∀ᶠ x : Space in 𝓝 (0 : Space), ‖x‖ < R := by
      filter_upwards [Metric.ball_mem_nhds (0 : Space) hR] with x hx
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds] with x hx hr
    exact ⟨hx, hr.le⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨B, hB₁, hB₂⟩ := exists_between (max_lt hA ha)
    have hB : 0 < B := (le_max_left _ _).trans_lt hB₁
    have haB : a < B := (le_max_right _ _).trans_lt hB₁
    have hq : d * B ^ (1 / 2 : ℝ) < 12 := by
      have h := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hB.le hB₂ (by norm_num : (0 : ℝ) < 1 / 2)) hd
      rwa [sommerfeldCoefficient_half hd] at h
    let D := B * (R ^ 2) ^ (-2 : ℝ)
    have ht : Tendsto (fun x : Space => B - ‖x‖ ^ 4 * D) (𝓝[≠] (0 : Space)) (𝓝 B) := by
      simpa using tendsto_const_nhds.sub (hfour.mul_const D)
    have he := ht.eventually (eventually_gt_nhds haB)
    filter_upwards [hball, he] with x hx he
    have hl := singular_lower_bound hd hc hR hB hq hreg hpde hlower x hx.1 hx.2
    have hmul := mul_le_mul_of_nonneg_left hl (pow_nonneg (norm_nonneg x) 4)
    have hu := norm_four_mul_radialPower hx.1
    dsimp [D] at he
    nlinarith
  · intro b hb
    obtain ⟨B, hB₁, hB₂⟩ := exists_between hb
    have hB : 0 < B := hA.trans hB₁
    have hq : 12 < d * B ^ (1 / 2 : ℝ) := by
      have h := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hA.le hB₁ (by norm_num : (0 : ℝ) < 1 / 2)) hd
      rwa [sommerfeldCoefficient_half hd] at h
    let D := C * (R ^ 2) ^ (-2 : ℝ) + 1
    have ht : Tendsto (fun x : Space => B + ‖x‖ ^ 4 * D) (𝓝[≠] (0 : Space)) (𝓝 B) := by
      simpa using tendsto_const_nhds.add (hfour.mul_const D)
    have he := ht.eventually (eventually_lt_nhds hB₂)
    filter_upwards [hball, he] with x hx he
    have hl := singular_upper_bound hd hC hR hB hq hreg hpde hupper x hx.1 hx.2
    have hmul := mul_le_mul_of_nonneg_left hl (pow_nonneg (norm_nonneg x) 4)
    have hu := norm_four_mul_radialPower hx.1
    dsimp [D] at he
    nlinarith

lemma SingularProfile.asymptotic {d : ℝ} {F : Space → ℝ} (h : SingularProfile d F)
    (hd : 0 < d) :
    Tendsto (fun x => ‖x‖ ^ 4 * F x) (𝓝[≠] (0 : Space)) (𝓝 (sommerfeldCoefficient d)) := by
  obtain ⟨c, hc, C, hC, R, hR, hl, hu⟩ := h.bounds
  exact sommerfeld_asymptotic hd hc hC.le hR (fun x hx _ => h.regular x hx)
    (fun x hx _ => h.equation x hx) hl hu

lemma deleted_eventually_to_small_ball {P : Space → Prop}
    (h : ∀ᶠ x in 𝓝[≠] (0 : Space), P x) :
    ∃ a > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ a → P x := by
  obtain ⟨a, ha, hbound⟩ := Metric.mem_nhdsWithin_iff.mp h
  refine ⟨a / 2, by positivity, ?_⟩
  intro x hx hxa
  apply hbound
  refine ⟨?_, hx⟩
  simpa only [Metric.mem_ball, dist_zero_right] using (show ‖x‖ < a by linarith)

end CoulombPDE

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_Nonneg
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
namespace CoulombPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem SingularProfile.nonneg {d : ℝ} {F : Space → ℝ}
    (h : SingularProfile d F) (x : Space) (hx : x ≠ 0) : 0 ≤ F x := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  let u : Space → ℝ := fun y => -F y - δ
  have hreg (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 u y :=
    (h.regular y hy).neg.sub contDiffAt_const
  have hsub (y : Space) (hy : y ≠ 0) (hp : 0 < u y) : 0 ≤ Δ u y := by
    have hf : F y ≤ 1 := by dsimp [u] at hp; linarith
    have he : reaction d (F y) = 0 := by
      simp [reaction, max_eq_right (sub_nonpos.mpr hf)]
    change 0 ≤ Δ ((-F) - (fun _ : Space => δ)) y
    have hneg : ContDiffAt ℝ 2 (-F) y := (h.regular y hy).neg
    have hconst : ContDiffAt ℝ 2 (fun _ : Space => δ) y := contDiffAt_const
    rw [hneg.laplacian_sub hconst,
      laplacian_neg, Pi.neg_apply, laplacian_const, Pi.zero_apply, h.equation y hy, he]
    norm_num
  obtain ⟨c, hc, C, _hC, R, hR, hl, _hu⟩ := h.bounds
  have hnear : ∃ r > 0, ∀ y, y ≠ 0 → ‖y‖ ≤ r → u y ≤ 0 := by
    refine ⟨R, hR, ?_⟩
    intro y hy hr
    have hF : 0 ≤ F y := (mul_nonneg hc.le (radialPower_nonneg _ _)).trans (hl y hy hr)
    dsimp [u]
    linarith
  have hfar : ∃ r > 0, ∀ y, r ≤ ‖y‖ → u y ≤ 0 := by
    obtain ⟨r, hr, hb⟩ := h.decay δ hδ
    refine ⟨r, hr, ?_⟩
    intro y hy
    have hf := (abs_lt.mp (hb y hy)).1
    dsimp [u]
    linarith
  have hm := global_punctured_maximum_principle hreg hsub hnear hfar x hx
  dsimp [u] at hm
  linarith

theorem SingularProfile.homogeneous_lower_bound {d : ℝ} {F : Space → ℝ}
    (hd : 0 < d) (h : SingularProfile d F) (x : Space) (hx : x ≠ 0) :
    sommerfeldCoefficient d * radialPower (-2) x ≤ F x := by
  have hA := sommerfeldCoefficient_pos hd
  have hBbound (B : ℝ) (hB : 0 < B) (hBA : B < sommerfeldCoefficient d) :
      B * radialPower (-2) x ≤ F x := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    let V : Space → ℝ := B • radialPower (-2)
    let u : Space → ℝ := V - F - fun _ => δ
    have hV (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 V y :=
      contDiffAt_const.smul (radialPower_contDiffAt _ hy)
    have hreg (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 u y :=
      ((hV y hy).sub (h.regular y hy)).sub contDiffAt_const
    have hq : d * B ^ (1 / 2 : ℝ) ≤ 12 := by
      rw [← sommerfeldCoefficient_half hd]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hB.le hBA.le (by norm_num)) hd.le
    have hsub (y : Space) (hy : y ≠ 0) (hp : 0 < u y) : 0 ≤ Δ u y := by
      have hp' : F y < radialPower (-2) y * B := by
        change 0 < B * radialPower (-2) y - F y - δ at hp
        nlinarith
      have ht : max (F y - 1) 0 ≤ radialPower (-2) y * B := by
        apply max_le
        · linarith
        · exact mul_nonneg (radialPower_nonneg _ _) hB.le
      have hr : reaction d (F y) ≤ 12 * B * radialPower (-3) y := by
        calc
          reaction d (F y) ≤ d * (radialPower (-2) y * B) ^ (3 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (le_max_right _ _) ht (by norm_num)) hd.le
          _ = d * (radialPower (-3) y * (B * B ^ (1 / 2 : ℝ))) := by
            rw [radial_scaled_reaction hB.le, rpow_three_halves B hB.le]
          _ ≤ 12 * B * radialPower (-3) y := by
            nlinarith [mul_nonneg (mul_nonneg hB.le (radialPower_nonneg (-3) y))
              (sub_nonneg.mpr hq)]
      have hVF : ContDiffAt ℝ 2 (V - F) y := (hV y hy).sub (h.regular y hy)
      have hc : ContDiffAt ℝ 2 (fun _ : Space => δ) y := contDiffAt_const
      change 0 ≤ (Δ ((V - F) - fun _ : Space => δ) : Space → ℝ) y
      rw [hVF.laplacian_sub hc, (hV y hy).laplacian_sub (h.regular y hy),
        laplacian_const, Pi.zero_apply, sub_zero, h.equation y hy]
      change 0 ≤ (Δ (B • radialPower (-2)) : Space → ℝ) y - reaction d (F y)
      rw [laplacian_smul B (radialPower_contDiffAt _ hy), radial_laplacian_three _ hy]
      norm_num only [smul_eq_mul] at *
      nlinarith
    have hnear : ∀ᶠ y in 𝓝[≠] (0 : Space), u y ≤ 0 := by
      filter_upwards [(h.asymptotic hd).eventually (eventually_gt_nhds hBA),
        self_mem_nhdsWithin] with y hy hy0
      have hn : 0 < ‖y‖ ^ 4 := pow_pos (norm_pos_iff.mpr hy0) _
      have hlow : B * radialPower (-2) y ≤ F y := by
        apply (mul_le_mul_iff_right₀ hn).mp
        have he := norm_four_mul_radialPower hy0
        nlinarith
      change B * radialPower (-2) y - F y - δ ≤ 0
      linarith
    have hfar : ∃ R > 0, ∀ y, R ≤ ‖y‖ → u y ≤ 0 := by
      refine ⟨max 1 (B / δ), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
      intro y hy
      have hn : 1 ≤ ‖y‖ := (le_max_left _ _).trans hy
      have hy0 : y ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hn)
      have h4 : B / δ ≤ ‖y‖ ^ 4 :=
        ((le_max_right _ _).trans hy).trans (le_self_pow₀ hn (by norm_num))
      have hB4 : B ≤ ‖y‖ ^ 4 * δ := (div_le_iff₀ hδ).mp h4
      have hv : B * radialPower (-2) y ≤ δ := by
        have ht := mul_le_mul_of_nonneg_right hB4 (radialPower_nonneg (-2) y)
        have he := norm_four_mul_radialPower hy0
        nlinarith
      have hnonneg := h.nonneg y hy0
      change B * radialPower (-2) y - F y - δ ≤ 0
      linarith
    have hm := global_punctured_maximum_principle hreg hsub
      (deleted_eventually_to_small_ball hnear) hfar x hx
    change B * radialPower (-2) x - F x - δ ≤ 0 at hm
    linarith
  have ht : Tendsto (fun B : ℝ => B * radialPower (-2) x)
      (𝓝[<] (sommerfeldCoefficient d))
      (𝓝 (sommerfeldCoefficient d * radialPower (-2) x)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).mul_const _
  apply le_of_tendsto_of_tendsto ht tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ B in 𝓝[<] (sommerfeldCoefficient d), 0 < B from
      (eventually_gt_nhds hA).filter_mono nhdsWithin_le_nhds)] with B hBA hB
  exact hBbound B hB hBA

theorem SingularProfile.pos {d : ℝ} {F : Space → ℝ}
    (hd : 0 < d) (h : SingularProfile d F) (x : Space) (hx : x ≠ 0) : 0 < F x :=
  (mul_pos (sommerfeldCoefficient_pos hd) (radialPower_pos _ hx)).trans_le
    (h.homogeneous_lower_bound hd x hx)

end CoulombPDE

open MeasureTheory Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfDilation
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
namespace CoulombAtom

lemma tfDilation_inv {b : ℝ} (hb : b ≠ 0) (ρ : Space → ℝ) :
    tfDilation b (tfDilation b⁻¹ ρ) = ρ := by
  funext x
  simp [tfDilation, smul_smul, hb]

theorem tfEnergy_scaling {b : ℝ} (hb : 0 < b) (Z M : ℝ) :
    tfEnergy (b ^ 3 * Z) (b ^ 3 * M) = b ^ 7 * tfEnergy Z M := by
  have hs : {e | ∃ ρ : Space → ℝ, TFAdmissible (b ^ 3 * M) ρ ∧
        tfFunctional (b ^ 3 * Z) ρ = e} =
      (b ^ 7) • {e | ∃ ρ : Space → ℝ, TFAdmissible M ρ ∧ tfFunctional Z ρ = e} := by
    ext e
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      have hi : TFAdmissible M (tfDilation b⁻¹ ρ) := by
        have h := tfDilation_admissible (inv_pos.mpr hb) hρ
        simpa only [inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hb.ne'), one_mul] using h
      refine ⟨tfFunctional Z (tfDilation b⁻¹ ρ), ⟨tfDilation b⁻¹ ρ, hi, rfl⟩, ?_⟩
      change b ^ 7 * tfFunctional Z (tfDilation b⁻¹ ρ) = tfFunctional (b ^ 3 * Z) ρ
      rw [← tfDilation_functional hb Z _ hi.1, tfDilation_inv hb.ne']
    · rintro ⟨e', ⟨ρ, hρ, rfl⟩, rfl⟩
      exact ⟨tfDilation b ρ, tfDilation_admissible hb hρ, tfDilation_functional hb Z ρ hρ.1⟩
  unfold tfEnergy
  rw [hs, Real.sInf_smul_of_nonneg (pow_nonneg hb.le _)]
  rfl

theorem tfIonization_scaling {m : ℝ} (hm : 0 < m) (Z : ℝ) :
    tfIonization m Z = m ^ (7 / 3 : ℝ) * tfIonization 1 (Z / m) := by
  let b : ℝ := m ^ (1 / 3 : ℝ)
  have hb : 0 < b := Real.rpow_pos_of_pos hm _
  have hb3 : b ^ 3 = m := by
    dsimp [b]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm.le]
    norm_num
  have hb7 : b ^ 7 = m ^ (7 / 3 : ℝ) := by
    dsimp [b]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm.le]
    norm_num
  have hZ : b ^ 3 * (Z / m) = Z := by
    rw [hb3]
    field_simp
  have he (N : ℝ) : tfEnergy Z (m * N) = m ^ (7 / 3 : ℝ) * tfEnergy (Z / m) N := by
    have ht := tfEnergy_scaling hb (Z / m) N
    rw [hZ, hb3, hb7] at ht
    exact ht
  calc
    tfIonization m Z = tfEnergy Z (m * (Z / m - 1)) - tfEnergy Z (m * (Z / m)) := by
      unfold tfIonization
      congr 2 <;> field_simp
    _ = _ := by rw [he, he, tfIonization]; ring

theorem tfCharacterization_of_unit_limit {a : ℝ}
    (ha : Tendsto (tfIonization 1) atTop (𝓝 a)) : TFCharacterization a := by
  intro m hm
  have hdiv : Tendsto (fun Z : ℝ => Z / m) atTop atTop :=
    Filter.Tendsto.atTop_div_const hm tendsto_id
  have h := (ha.comp hdiv).const_mul (m ^ (7 / 3 : ℝ))
  simpa only [Function.comp_def, ← tfIonization_scaling hm, mul_comm (m ^ (7 / 3 : ℝ)) a] using h

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoulombCoercivity
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
section CoulombCoercivity

lemma graphValue_norm_sq {N : ℕ} (F : fermionGraph N) :
    ‖fermionGraphValue N F‖ ^ 2 = ∑ s : Spins N, ‖graphComponent s none F‖ ^ 2 := by
  change ‖(fermionGraphValue N F).val‖ ^ 2 = _
  exact PiLp.norm_sq_eq_of_L2 _ _

attribute [local irreducible] graphComponent graphNuclear graphPair fermionGraphValue

end CoulombCoercivity

lemma graphFormVector_admissible {N : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖ ^ 2 = 1) : FormAdmissible (graphFormVector F) := by
  refine ⟨fun s => Lp.memLp _, fun s i a => Lp.memLp _, ?_, ?_, ?_, ?_, ?_⟩
  · intro s i a φ hφ hcφ
    exact ((mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property
      (i, a)) φ hφ hcφ
  · intro π s
    exact (mem_fermionSpace_ae _).mp (fermionGraphValue N F).property π s
  · have hmass := graphValue_norm_sq F
    rw [hn] at hmass
    simpa only [lp_norm_sq, graphComponent_apply, graphFormVector] using hmass.symm
  · intro s i
    exact nuclear_integrable i (Lp.memLp _) (fun a => Lp.memLp _)
      (fun a => (mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property (i, a))
  · intro s i j hij
    exact pair_integrable i j hij (Lp.memLp _) (fun a => Lp.memLp _)
      (fun a => (mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property (i, a))

lemma graphFormVector_admissibleGraph_value {N : ℕ} (ψ : FormVector N)
    (hψ : FormAdmissible ψ) (s : Spins N) :
    (graphFormVector (admissibleGraph ψ hψ)).value s =ᵐ[volume] ψ.value s := by
  simpa only [graphFormVector, admissibleGraph, WithLp.ofLp_toLp,
    admissibleWeakGraph_value] using (hψ.1 s).coeFn_toLp

lemma graphFormVector_admissibleGraph_gradient {N : ℕ} (ψ : FormVector N)
    (hψ : FormAdmissible ψ) (s : Spins N) (i : Fin N) (a : Fin 3) :
    (graphFormVector (admissibleGraph ψ hψ)).gradient s i a =ᵐ[volume] ψ.gradient s i a := by
  simpa only [graphFormVector, admissibleGraph, WithLp.ofLp_toLp,
    admissibleWeakGraph_gradient] using (hψ.2.1 s i a).coeFn_toLp

lemma admissibleGraph_norm {N : ℕ} (ψ : FormVector N) (hψ : FormAdmissible ψ) :
    ‖fermionGraphValue N (admissibleGraph ψ hψ)‖ ^ 2 = 1 := by
  calc
    _ = ∑ s : Spins N, ∫ x, ‖(graphFormVector (admissibleGraph ψ hψ)).value s x‖ ^ 2 := by
      rw [graphValue_norm_sq]
      simp only [lp_norm_sq, graphComponent_apply, graphFormVector]
    _ = ∑ s : Spins N, ∫ x, ‖ψ.value s x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro s _
      apply integral_congr_ae
      filter_upwards [graphFormVector_admissibleGraph_value ψ hψ s] with x hx
      rw [hx]
    _ = 1 := hψ.2.2.2.2.1

lemma formEnergy_congr_ae {N : ℕ} (Z : ℝ) (ψ φ : FormVector N)
    (hv : ∀ s, ψ.value s =ᵐ[volume] φ.value s)
    (hg : ∀ s i a, ψ.gradient s i a =ᵐ[volume] φ.gradient s i a) :
    formEnergy Z ψ = formEnergy Z φ := by
  have hk : (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ∫ x, ‖ψ.gradient s i a x‖ ^ 2) =
      ∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ∫ x, ‖φ.gradient s i a x‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    apply integral_congr_ae
    filter_upwards [hg s i a] with x hx
    rw [hx]
  have hn : (∑ s : Spins N, ∑ i : Fin N, ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖) =
      ∑ s : Spins N, ∑ i : Fin N, ∫ x, ‖φ.value s x‖ ^ 2 / ‖x i‖ := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [hv s] with x hx
    rw [hx]
  have hp : (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
      if i < j then ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i - x j‖ else 0) =
      ∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
      if i < j then ∫ x, ‖φ.value s x‖ ^ 2 / ‖x i - x j‖ else 0 := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · apply integral_congr_ae
      filter_upwards [hv s] with x hx
      rw [hx]
    · rfl
  unfold formEnergy
  rw [hk, hn, hp]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_IteratedReduction
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution

lemma uniform_tail_of_sequential_joint (f : ℕ → ℕ → ℝ) (a : ℝ)
    (h : ∀ m Z : ℕ → ℕ, (∀ j, 1 ≤ m j ∧ m j < Z j) →
      Tendsto m atTop atTop →
      Tendsto (fun j => (Z j : ℝ) / (m j : ℝ)) atTop atTop →
      Tendsto (fun j => f (m j) (Z j)) atTop (𝓝 a)) :
    ∀ ε > 0, ∃ K : ℕ, ∀ m Z : ℕ, 1 ≤ m → m < Z → K ≤ m →
      (K : ℝ) ≤ (Z : ℝ) / (m : ℝ) → |f m Z - a| < ε := by
  intro ε hε
  by_contra hn
  push Not at hn
  choose m Z hm hZ hKm hKZ he using fun j : ℕ => hn (j + 1)
  have hmTop : Tendsto m atTop atTop := by
    apply tendsto_atTop_mono (fun j => (Nat.le_succ j).trans (hKm j)) tendsto_id
  have hratio : Tendsto (fun j => (Z j : ℝ) / (m j : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (fun j => ?_) tendsto_natCast_atTop_atTop
    have hj : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ j
    exact hj.trans (hKZ j)
  have hc := h m Z (fun j => ⟨hm j, hZ j⟩) hmTop hratio
  have hev : ∀ᶠ j in atTop, |f (m j) (Z j) - a| < ε :=
    (Metric.tendsto_nhds.mp hc ε hε).mono fun j hj => by simpa [Real.dist_eq] using hj
  obtain ⟨j, hj⟩ := hev.exists
  exact (not_lt_of_ge (he j)) hj

lemma eventual_Z_band_of_joint (f : ℕ → ℕ → ℝ) (a : ℝ)
    (h : ∀ m Z : ℕ → ℕ, (∀ j, 1 ≤ m j ∧ m j < Z j) →
      Tendsto m atTop atTop →
      Tendsto (fun j => (Z j : ℝ) / (m j : ℝ)) atTop atTop →
      Tendsto (fun j => f (m j) (Z j)) atTop (𝓝 a)) :
    ∀ ε > 0, ∀ᶠ m in (atTop : Filter ℕ), ∀ᶠ Z in (atTop : Filter ℕ),
      |f m Z - a| < ε := by
  intro ε hε
  obtain ⟨K, hK⟩ := uniform_tail_of_sequential_joint f a h ε hε
  filter_upwards [eventually_ge_atTop (max K 1)] with m hm
  have hm1 : 1 ≤ m := (le_max_right _ _).trans hm
  have hmK : K ≤ m := (le_max_left _ _).trans hm
  filter_upwards [eventually_ge_atTop (max (m + 1) (K * m))] with Z hZ
  apply hK m Z hm1 (Nat.lt_of_succ_le ((le_max_left _ _).trans hZ)) hmK
  apply (le_div_iff₀ (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm1 : (0 : ℝ) < m)).mpr
  exact_mod_cast (le_max_right (m + 1) (K * m)).trans hZ

lemma liminf_limsup_bounded_by_eventual {u : ℕ → ℝ} {l r : ℝ}
    (h : ∀ᶠ n in atTop, l ≤ u n ∧ u n ≤ r) :
    l ≤ liminf u atTop ∧ liminf u atTop ≤ limsup u atTop ∧ limsup u atTop ≤ r := by
  have hl : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) u := ⟨l, h.mono fun _ hh => hh.1⟩
  have hr : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) u := ⟨r, h.mono fun _ hh => hh.2⟩
  exact ⟨le_liminf_of_le hr.isCoboundedUnder_ge (h.mono fun _ hh => hh.1),
    liminf_le_limsup hr hl, limsup_le_of_le hl.isCoboundedUnder_le (h.mono fun _ hh => hh.2)⟩

theorem iteratedLimits_of_jointLimit {a : ℝ} (h : JointLimit a) : IteratedLimits a := by
  have hband := eventual_Z_band_of_joint
    (fun m Z => ionization m Z / (m : ℝ) ^ (7 / 3 : ℝ)) a h
  have main : ∀ ε > 0, ∀ᶠ m in (atTop : Filter ℕ),
      |(limsup (ionization m) atTop) / (m : ℝ) ^ (7 / 3 : ℝ) - a| < ε ∧
      |(liminf (ionization m) atTop) / (m : ℝ) ^ (7 / 3 : ℝ) - a| < ε := by
    intro ε hε
    filter_upwards [hband (ε / 2) (by positivity), eventually_ge_atTop 1] with m hm hm1
    have hw : 0 < (m : ℝ) ^ (7 / 3 : ℝ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm1) _
    have he : ∀ᶠ Z in (atTop : Filter ℕ),
        (a - ε / 2) * (m : ℝ) ^ (7 / 3 : ℝ) ≤ ionization m Z ∧
        ionization m Z ≤ (a + ε / 2) * (m : ℝ) ^ (7 / 3 : ℝ) := by
      filter_upwards [hm] with Z hZ
      obtain ⟨hl, hr⟩ := abs_lt.mp hZ
      constructor
      · apply (le_div_iff₀ hw).mp
        linarith
      · apply (div_le_iff₀ hw).mp
        linarith
    obtain ⟨hl, hm', hr⟩ := liminf_limsup_bounded_by_eventual he
    have hsL := (le_div_iff₀ hw).mpr (hl.trans hm')
    have hsR := (div_le_iff₀ hw).mpr hr
    have hiL := (le_div_iff₀ hw).mpr hl
    have hiR := (div_le_iff₀ hw).mpr (hm'.trans hr)
    constructor <;> apply abs_lt.mpr <;> constructor <;> linarith
  constructor
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    exact (main ε hε).mono fun m hm => by simpa [Real.dist_eq] using hm.1
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    exact (main ε hε).mono fun m hm => by simpa [Real.dist_eq] using hm.2


open Filter
open scoped Topology InnerProductSpace

open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_SobolevVector
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

lemma SobolevFermion.multiply {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (p : FermionMultiplier N) : SobolevFermion (multiplyForm p.toSmoothMultiplier ψ) := by
  have hw := hψ.sobolevVector.multiply p.toSmoothMultiplier
  refine ⟨hw.1, hw.2.1, hw.2.2, ?_⟩
  intro π s
  filter_upwards [hψ.2.2.2 π s] with x hx
  change (p.value (x ∘ π) : ℂ) * ψ.value (s ∘ π) (x ∘ π) =
    _ * ((p.value x : ℂ) * ψ.value s x)
  rw [p.symmetric, hx]
  ring

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_IntegratedStability
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom

theorem grid_increment_error {G d P D : ℝ → ℝ}
    (hG : DeficitSecants G d) (hP : DeficitSecants P D)
    {a h η : ℝ} (ha : 0 < a) (hh : 0 < h) {N : ℕ}
    (hclose : ∀ i ≤ N, |d (a + i * h) - D (a + i * h)| ≤ η) :
    |(G (a + N * h) - G a) - (P (a + N * h) - P a)| ≤
      h * (D (a + N * h) - D a) + N * h * η := by
  have hind : ∀ i ≤ N,
      |(G (a + i * h) - G a) - (P (a + i * h) - P a)| ≤
        h * (D (a + i * h) - D a) + i * h * η := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have hiN : i ≤ N := Nat.le_trans (Nat.le_succ i) hi
      have hix : 0 < a + i * h := by positivity
      have hxy : a + i * h < a + (i + 1 : ℕ) * h := by
        push_cast
        nlinarith
      have hsG := hG (a + i * h) (a + (i + 1 : ℕ) * h) hix hxy
      have hsP := hP (a + i * h) (a + (i + 1 : ℕ) * h) hix hxy
      have hcl := (abs_le.mp (hclose i hiN))
      have hcr := (abs_le.mp (hclose (i + 1) hi))
      have hcl' := mul_le_mul_of_nonneg_left hcl.1 hh.le
      have hcr' := mul_le_mul_of_nonneg_left hcr.2 hh.le
      have heq : a + (i + 1 : ℕ) * h - (a + i * h) = h := by
        push_cast
        ring
      rw [heq] at hsG hsP
      have hstep : |(G (a + (i + 1 : ℕ) * h) - G (a + i * h)) -
          (P (a + (i + 1 : ℕ) * h) - P (a + i * h))| ≤
          h * (D (a + (i + 1 : ℕ) * h) - D (a + i * h)) + h * η := by
        apply abs_le.mpr
        constructor <;> nlinarith [hsG.1, hsG.2, hsP.1, hsP.2]
      have htel : (G (a + (i + 1 : ℕ) * h) - G a) -
          (P (a + (i + 1 : ℕ) * h) - P a) =
          ((G (a + i * h) - G a) - (P (a + i * h) - P a)) +
          ((G (a + (i + 1 : ℕ) * h) - G (a + i * h)) -
          (P (a + (i + 1 : ℕ) * h) - P (a + i * h))) := by ring
      rw [htel]
      calc
        _ ≤ |(G (a + i * h) - G a) - (P (a + i * h) - P a)| +
            |(G (a + (i + 1 : ℕ) * h) - G (a + i * h)) -
            (P (a + (i + 1 : ℕ) * h) - P (a + i * h))| := abs_add_le _ _
        _ ≤ (h * (D (a + i * h) - D a) + i * h * η) +
            (h * (D (a + (i + 1 : ℕ) * h) - D (a + i * h)) + h * η) :=
          add_le_add (ih hiN) hstep
        _ = _ := by push_cast; ring
  exact hind N le_rfl

theorem deficit_secant_increments_tendsto {G d : ℕ → ℝ → ℝ} {P D : ℝ → ℝ}
    (hG : ∀ n, DeficitSecants (G n) (d n)) (hP : DeficitSecants P D)
    (hd : ∀ t : ℝ, 0 < t → Tendsto (fun n => d n t) atTop (𝓝 (D t)))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun n => G n b - G n a) atTop (𝓝 (P b - P a)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (2 * ((b - a) * (D b - D a)) / ε))
  have hN1 : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNpos : (0 : ℝ) < N := lt_trans zero_lt_one hN1
  have hwidth : 0 < b - a := sub_pos.mpr hab
  let h : ℝ := (b - a) / N
  let η : ℝ := ε / (2 * (b - a))
  have hh : 0 < h := div_pos hwidth hNpos
  have hη : 0 < η := div_pos hε (by positivity)
  have hxN : a + N * h = b := by dsimp [h]; field_simp; ring
  have hmesh : h * (D b - D a) < ε / 2 := by
    have hnr : 2 * ((b - a) * (D b - D a)) / ε < N :=
      (le_max_right _ _).trans_lt hN
    have hnr' := (div_lt_iff₀ hε).mp hnr
    dsimp [h]
    rw [div_mul_eq_mul_div]
    apply (div_lt_div_iff₀ hNpos (show (0 : ℝ) < 2 by norm_num)).mpr
    nlinarith
  have hηeq : (N : ℝ) * h * η = ε / 2 := by
    dsimp [h, η]
    field_simp
  have hev : ∀ i : Fin (N + 1), ∀ᶠ n in atTop,
      |d n (a + (i : ℕ) * h) - D (a + (i : ℕ) * h)| ≤ η := by
    intro i
    have hxi : 0 < a + (i : ℕ) * h := by positivity
    exact ((Metric.tendsto_nhds.mp (hd _ hxi)) η hη).mono fun n hn =>
      le_of_lt (by simpa only [Real.dist_eq] using hn)
  filter_upwards [Filter.eventually_all.mpr hev] with n hn
  rw [Real.dist_eq]
  have he := grid_increment_error (hG n) hP ha hh
    (N := N) (η := η) (fun i hi => hn ⟨i, Nat.lt_succ_iff.mpr hi⟩)
  rw [hxN, hηeq] at he
  linarith

theorem deficit_secant_energy_tendsto {G d : ℕ → ℝ → ℝ} {P D : ℝ → ℝ}
    {err : ℕ → ℝ} (hG : ∀ n, DeficitSecants (G n) (d n))
    (hP : DeficitSecants P D)
    (hd : ∀ t : ℝ, 0 < t → Tendsto (fun n => d n t) atTop (𝓝 (D t)))
    (he : Tendsto err atTop (𝓝 0))
    (hzero : ∀ v, 0 < v → ∀ᶠ n in atTop, -err n - v * d n v ≤ G n v ∧ G n v ≤ 0)
    (hPc : ContinuousAt P 0) (hP0 : P 0 = 0) (hDc : ContinuousAt D 0)
    {t : ℝ} (ht : 0 < t) : Tendsto (fun n => G n t) atTop (𝓝 (P t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hc : ContinuousAt (fun v : ℝ => |P v| + |v * D v|) 0 :=
    hPc.abs.add ((continuousAt_id.mul hDc).abs)
  have hevent : ∀ᶠ v in 𝓝 (0 : ℝ), |P v| + |v * D v| < ε / 4 := by
    have hconv : Tendsto (fun v : ℝ => |P v| + |v * D v|) (𝓝 0) (𝓝 0) := by
      simpa [hP0] using hc.tendsto
    exact hconv.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))
  obtain ⟨δ, hδ, hδevent⟩ := Metric.eventually_nhds_iff.mp hevent
  let v : ℝ := min (t / 2) (δ / 2)
  have hv : 0 < v := lt_min (by positivity) (by positivity)
  have hvt : v < t := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hvδ : dist v 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hv]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hsmall := hδevent hvδ
  have hinc := deficit_secant_increments_tendsto hG hP hd hv hvt
  have hbound : Tendsto (fun n => err n + v * d n v) atTop (𝓝 (v * D v)) := by
    simpa using he.add ((hd v hv).const_mul v)
  filter_upwards [(Metric.tendsto_nhds.mp hinc) (ε / 4) (by positivity),
    (Metric.tendsto_nhds.mp hbound) (ε / 4) (by positivity), hzero v hv] with n hn hb hz
  rw [Real.dist_eq] at hn hb ⊢
  have hGv : |G n v| ≤ err n + v * d n v := by
    rw [abs_of_nonpos hz.2]
    linarith [hz.1]
  have hbound' : err n + v * d n v < |v * D v| + ε / 4 := by
    have hb' := (abs_lt.mp hb).2
    linarith [le_abs_self (v * D v)]
  have halg : G n t - P t =
      ((G n t - G n v) - (P t - P v)) + (G n v - P v) := by ring
  rw [halg]
  have htri := abs_add_le ((G n t - G n v) - (P t - P v)) (G n v - P v)
  have hsub := abs_sub (G n v) (P v)
  linarith

theorem hasDerivAt_limitPriceEnergy {q t : ℝ} (ht : 0 < t) :
    HasDerivAt (limitPriceEnergy q) (-limitDeficit q t) t := by
  have h : HasDerivAt (fun x : ℝ => -(4 / 7 : ℝ) * q * x ^ (7 / 4 : ℝ))
      (-(4 / 7 : ℝ) * q * ((7 / 4 : ℝ) * t ^ ((7 / 4 : ℝ) - 1))) t :=
    ((Real.hasStrictDerivAt_rpow_const_of_ne ht.ne' (7 / 4 : ℝ)).hasDerivAt).const_mul _
  have he : -(4 / 7 : ℝ) * q * ((7 / 4 : ℝ) * t ^ ((7 / 4 : ℝ) - 1)) =
      -limitDeficit q t := by
    norm_num [limitDeficit]
    ring
  rw [he] at h
  exact h

theorem deficitSecants_limitPriceEnergy {q : ℝ} (hq : 0 ≤ q) :
    DeficitSecants (limitPriceEnergy q) (limitDeficit q) := by
  have hconc : ConcaveOn ℝ (Set.Ici 0) (limitPriceEnergy q) := by
    have h := ((convexOn_rpow (p := (7 / 4 : ℝ)) (by norm_num)).smul
      (c := (4 / 7 : ℝ) * q) (by positivity)).neg
    have he : (-fun x : ℝ => ((4 / 7 : ℝ) * q) • x ^ (7 / 4 : ℝ)) =
        limitPriceEnergy q := by
      funext x
      simp only [Pi.neg_apply, smul_eq_mul, limitPriceEnergy]
      ring
    rw [he] at h
    exact h
  intro v t hv hvt
  have ht : 0 < t := hv.trans hvt
  have hL := hconc.le_slope_of_hasDerivAt hv.le ht.le hvt (hasDerivAt_limitPriceEnergy ht)
  have hU := hconc.slope_le_of_hasDerivAt hv.le ht.le hvt (hasDerivAt_limitPriceEnergy hv)
  rw [slope_def_field] at hL hU
  have hL' := (le_div_iff₀ (sub_pos.mpr hvt)).mp hL
  have hU' := (div_le_iff₀ (sub_pos.mpr hvt)).mp hU
  constructor <;> nlinarith

theorem limitPriceEnergy_add {q t : ℝ} (ht : 0 < t) :
    limitPriceEnergy q t + t * limitDeficit q t = limitSectorEnergy q t := by
  have hp : t ^ (7 / 4 : ℝ) = t * t ^ (3 / 4 : ℝ) := by
    rw [show (7 / 4 : ℝ) = 1 + 3 / 4 by norm_num, Real.rpow_add ht, Real.rpow_one]
  simp only [limitPriceEnergy, limitDeficit, limitSectorEnergy, hp]
  ring

theorem continuous_limitPriceEnergy (q : ℝ) : Continuous (limitPriceEnergy q) :=
  continuous_const.mul (Real.continuous_rpow_const (by norm_num))

theorem continuous_limitDeficit (q : ℝ) : Continuous (limitDeficit q) :=
  continuous_const.mul (Real.continuous_rpow_const (by norm_num))

theorem continuous_limitSectorEnergy (q : ℝ) : Continuous (limitSectorEnergy q) :=
  continuous_const.mul (Real.continuous_rpow_const (by norm_num))

theorem limitDeficit_strictMonoOn {q : ℝ} (hq : 0 < q) :
    StrictMonoOn (limitDeficit q) (Set.Ioi 0) := by
  intro a ha b _ hab
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow ha.le hab (by norm_num)) hq

theorem limitDeficit_target {q : ℝ} (hq : 0 < q) :
    limitDeficit q (q ^ (-4 / 3 : ℝ)) = 1 := by
  rw [limitDeficit, ← Real.rpow_mul hq.le]
  norm_num
  simpa only [Real.rpow_neg_one] using mul_inv_cancel₀ hq.ne'

theorem limitSectorEnergy_target {q : ℝ} (hq : 0 < q) :
    limitSectorEnergy q (q ^ (-4 / 3 : ℝ)) = (3 / 7 : ℝ) * q ^ (-4 / 3 : ℝ) := by
  have hp : (q ^ (-4 / 3 : ℝ)) ^ (7 / 4 : ℝ) =
      q ^ (-4 / 3 : ℝ) * (q ^ (-4 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
    rw [show (7 / 4 : ℝ) = 1 + 3 / 4 by norm_num,
      Real.rpow_add (Real.rpow_pos_of_pos hq _), Real.rpow_one]
  have hD := limitDeficit_target hq
  dsimp [limitDeficit] at hD
  dsimp [limitSectorEnergy]
  rw [hp]
  calc
    _ = (3 / 7 : ℝ) * (q * (q ^ (-4 / 3 : ℝ)) ^ (3 / 4 : ℝ)) * q ^ (-4 / 3 : ℝ) := by ring
    _ = _ := by rw [hD]; ring

theorem tendsto_of_deficit_brackets {J d : ℕ → ℝ → ℝ} {F : ℕ → ℝ} {L D : ℝ → ℝ}
    {c : ℝ} (hc : 0 < c) (hD : StrictMonoOn D (Set.Ioi 0)) (hDc : D c = 1)
    (hL : ContinuousAt L c)
    (hd : ∀ t : ℝ, 0 < t → Tendsto (fun n => d n t) atTop (𝓝 (D t)))
    (hJ : ∀ t : ℝ, 0 < t → Tendsto (fun n => J n t) atTop (𝓝 (L t)))
    (hbelow : ∀ n t, 0 < t → d n t < 1 → J n t ≤ F n)
    (habove : ∀ n t, 0 < t → 1 < d n t → F n ≤ J n t) :
    Tendsto F atTop (𝓝 (L c)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδL⟩ := Metric.continuousAt_iff.mp hL (ε / 2) (by positivity)
  let η : ℝ := min (c / 2) (δ / 2)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηc : η ≤ c / 2 := min_le_left _ _
  have hηδ : η < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hminus : 0 < c - η := by linarith
  have hplus : 0 < c + η := by linarith
  have hDm : D (c - η) < 1 := by rw [← hDc]; exact hD hminus hc (by linarith)
  have hDp : 1 < D (c + η) := by rw [← hDc]; exact hD hc hplus (by linarith)
  have hLm : |L (c - η) - L c| < ε / 2 := by
    apply (show dist (L (c - η)) (L c) < ε / 2 → _ from fun h => by simpa [Real.dist_eq] using h)
    apply hδL
    simpa [Real.dist_eq, abs_of_pos hη, abs_neg] using hηδ
  have hLp : |L (c + η) - L c| < ε / 2 := by
    apply (show dist (L (c + η)) (L c) < ε / 2 → _ from fun h => by simpa [Real.dist_eq] using h)
    apply hδL
    simpa [Real.dist_eq, abs_of_pos hη] using hηδ
  filter_upwards [(hd _ hminus).eventually (gt_mem_nhds hDm),
    (hd _ hplus).eventually (lt_mem_nhds hDp),
    (Metric.tendsto_nhds.mp (hJ _ hminus)) (ε / 2) (by positivity),
    (Metric.tendsto_nhds.mp (hJ _ hplus)) (ε / 2) (by positivity)] with n hdm hdp hjm hjp
  have hfm := hbelow n _ hminus hdm
  have hfp := habove n _ hplus hdp
  rw [Real.dist_eq] at hjm hjp ⊢
  obtain ⟨hlm, hum⟩ := abs_lt.mp hLm
  obtain ⟨hlp, hup⟩ := abs_lt.mp hLp
  obtain ⟨hjmL, hjmU⟩ := abs_lt.mp hjm
  obtain ⟨hjpL, hjpU⟩ := abs_lt.mp hjp
  apply abs_lt.mpr
  constructor <;> linarith

theorem priceEnergy_secants {E : ℕ → ℝ} {lam μ : ℝ} {n k : ℕ}
    (hn : PriceMinimizes E lam n) (hk : PriceMinimizes E μ k) :
    (μ - lam) * k ≤ priceEnergy E μ - priceEnergy E lam ∧
    priceEnergy E μ - priceEnergy E lam ≤ (μ - lam) * n := by
  rw [priceEnergy_eq_of_minimizes hn, priceEnergy_eq_of_minimizes hk]
  have h₁ := hn k
  have h₂ := hk n
  constructor <;> nlinarith

theorem rpow_seven_thirds {m : ℝ} (hm : 0 < m) :
    m ^ (7 / 3 : ℝ) = m * m ^ (4 / 3 : ℝ) := by
  rw [show (7 / 3 : ℝ) = 1 + 4 / 3 by norm_num, Real.rpow_add hm, Real.rpow_one]

theorem scaledDeficit_mul {Z n : ℕ} {m : ℝ} (hm : 0 < m) :
    scaledDeficit Z n m * m ^ (7 / 3 : ℝ) = m ^ (4 / 3 : ℝ) * ((Z : ℝ) - n) := by
  rw [scaledDeficit, rpow_seven_thirds hm]
  field_simp

theorem scaledPrice_sector {E : ℕ → ℝ} {Z n : ℕ} {m t : ℝ} (hm : 0 < m)
    (hn : PriceMinimizes E (t * m ^ (4 / 3 : ℝ)) n) :
    scaledPrice E Z m t + t * scaledDeficit Z n m =
      (E n - E Z) / m ^ (7 / 3 : ℝ) := by
  rw [scaledPrice, priceEnergy_eq_of_minimizes hn, scaledDeficit, rpow_seven_thirds hm]
  field_simp
  ring

theorem scaledPrice_secants {E : ℕ → ℝ} {Z : ℕ} {m : ℝ} (hm : 0 < m)
    {N : ℝ → ℕ} (hN : ∀ t, 0 < t → PriceMinimizes E (t * m ^ (4 / 3 : ℝ)) (N t)) :
    DeficitSecants (scaledPrice E Z m) (fun t => scaledDeficit Z (N t) m) := by
  intro v t hv hvt
  have ht : 0 < t := hv.trans hvt
  have hs := priceEnergy_secants (hN v hv) (hN t ht)
  have hpos := Real.rpow_pos_of_pos hm (7 / 3 : ℝ)
  have heq : scaledPrice E Z m t - scaledPrice E Z m v =
      (priceEnergy E (t * m ^ (4 / 3 : ℝ)) - priceEnergy E (v * m ^ (4 / 3 : ℝ)) -
        (t - v) * m ^ (4 / 3 : ℝ) * Z) / m ^ (7 / 3 : ℝ) := by
    simp only [scaledPrice]
    ring
  rw [heq]
  constructor
  · apply (le_div_iff₀ hpos).mpr
    simp only [mul_assoc, scaledDeficit_mul hm]
    nlinarith [hs.1]
  · apply (div_le_iff₀ hpos).mpr
    simp only [mul_assoc, scaledDeficit_mul hm]
    nlinarith [hs.2]

theorem scaledPrice_nonpos {E : ℕ → ℝ} {Z n : ℕ} {m t : ℝ} (hm : 0 < m)
    (hn : PriceMinimizes E (t * m ^ (4 / 3 : ℝ)) n) : scaledPrice E Z m t ≤ 0 := by
  rw [scaledPrice, priceEnergy_eq_of_minimizes hn]
  apply div_nonpos_of_nonpos_of_nonneg _ (Real.rpow_nonneg hm.le _)
  have hz := hn Z
  linarith

theorem scaledPrice_limits {E : ℕ → ℕ → ℝ} {Z : ℕ → ℕ} {m : ℕ → ℝ}
    {N : ℕ → ℝ → ℕ} {q : ℝ} (hq : 0 < q) (hm : ∀ j, 0 < m j)
    (hmono : ∀ j, Antitone (E j))
    (hN : ∀ j t, 0 < t → PriceMinimizes (E j) (t * m j ^ (4 / 3 : ℝ)) (N j t))
    (hd : ∀ t, 0 < t → Tendsto (fun j => scaledDeficit (Z j) (N j t) (m j))
      atTop (𝓝 (limitDeficit q t)))
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun j => scaledPrice (E j) (Z j) (m j) t) atTop (𝓝 (limitPriceEnergy q t)) ∧
    Tendsto (fun j => (E j (N j t) - E j (Z j)) / m j ^ (7 / 3 : ℝ))
      atTop (𝓝 (limitSectorEnergy q t)) := by
  have hz : ∀ v, 0 < v → ∀ᶠ j in atTop,
      -(0 : ℝ) - v * scaledDeficit (Z j) (N j v) (m j) ≤ scaledPrice (E j) (Z j) (m j) v ∧
      scaledPrice (E j) (Z j) (m j) v ≤ 0 := by
    intro v hv
    have hD : 0 < limitDeficit q v := mul_pos hq (Real.rpow_pos_of_pos hv _)
    filter_upwards [(hd v hv).eventually (lt_mem_nhds hD)] with j hj
    have hdiff : 0 < (Z j : ℝ) - N j v := by
      simpa using (lt_div_iff₀ (hm j)).mp hj
    have hnZ : N j v ≤ Z j := by exact_mod_cast (show (N j v : ℝ) ≤ Z j by linarith)
    have hle := hmono j hnZ
    have henergy : 0 ≤ (E j (N j v) - E j (Z j)) / m j ^ (7 / 3 : ℝ) :=
      div_nonneg (sub_nonneg.mpr hle) (Real.rpow_nonneg (hm j).le _)
    rw [← scaledPrice_sector (hm j) (hN j v hv)] at henergy
    exact ⟨by linarith, scaledPrice_nonpos (hm j) (hN j v hv)⟩
  have hp := deficit_secant_energy_tendsto
    (fun j => scaledPrice_secants (hm j) (hN j)) (deficitSecants_limitPriceEnergy hq.le)
    hd tendsto_const_nhds hz (continuous_limitPriceEnergy q).continuousAt
    (by simp [limitPriceEnergy]) (continuous_limitDeficit q).continuousAt ht
  refine ⟨hp, ?_⟩
  have h := hp.add ((hd t ht).const_mul t)
  simpa only [scaledPrice_sector (hm _) (hN _ t ht), limitPriceEnergy_add ht] using h

theorem fixed_sector_limit_of_priced_deficit {E : ℕ → ℕ → ℝ} {Z m : ℕ → ℕ}
    {N : ℕ → ℝ → ℕ} {q : ℝ} (hq : 0 < q)
    (hm : ∀ j, 1 ≤ m j ∧ m j ≤ Z j) (hmono : ∀ j, Antitone (E j))
    (hN : ∀ j t, 0 < t → PriceMinimizes (E j) (t * (m j : ℝ) ^ (4 / 3 : ℝ)) (N j t))
    (hd : ∀ t, 0 < t → Tendsto (fun j => scaledDeficit (Z j) (N j t) (m j))
      atTop (𝓝 (limitDeficit q t))) :
    Tendsto (fun j => (E j (Z j - m j) - E j (Z j)) / (m j : ℝ) ^ (7 / 3 : ℝ))
      atTop (𝓝 ((3 / 7 : ℝ) * q ^ (-4 / 3 : ℝ))) := by
  have hmp : ∀ j, (0 : ℝ) < m j := fun j => by exact_mod_cast (show 0 < m j by have := (hm j).1; omega)
  have hJ : ∀ t, 0 < t → Tendsto
      (fun j => (E j (N j t) - E j (Z j)) / (m j : ℝ) ^ (7 / 3 : ℝ))
      atTop (𝓝 (limitSectorEnergy q t)) := fun t ht => (scaledPrice_limits hq hmp hmono hN hd ht).2
  have hlo : ∀ j t, 0 < t → scaledDeficit (Z j) (N j t) (m j) < 1 →
      (E j (N j t) - E j (Z j)) / (m j : ℝ) ^ (7 / 3 : ℝ) ≤
      (E j (Z j - m j) - E j (Z j)) / (m j : ℝ) ^ (7 / 3 : ℝ) := by
    intro j t _ hdj
    have hn : Z j - m j ≤ N j t := by
      have hh : (Z j : ℝ) - N j t < m j := (div_lt_one (hmp j)).mp hdj
      have hh' : (Z j - m j : ℕ) ≤ N j t := by
        apply (Nat.cast_le (α := ℝ)).mp
        rw [Nat.cast_sub (hm j).2]
        linarith
      exact hh'
    exact div_le_div_of_nonneg_right (sub_le_sub_right (hmono j hn) _) (Real.rpow_nonneg (hmp j).le _)
  have hup : ∀ j t, 0 < t → 1 < scaledDeficit (Z j) (N j t) (m j) →
      (E j (Z j - m j) - E j (Z j)) / (m j : ℝ) ^ (7 / 3 : ℝ) ≤
      (E j (N j t) - E j (Z j)) / (m j : ℝ) ^ (7 / 3 : ℝ) := by
    intro j t _ hdj
    have hn : N j t ≤ Z j - m j := by
      have hh : (m j : ℝ) < (Z j : ℝ) - N j t := (one_lt_div (hmp j)).mp hdj
      apply (Nat.cast_le (α := ℝ)).mp
      rw [Nat.cast_sub (hm j).2]
      linarith
    exact div_le_div_of_nonneg_right (sub_le_sub_right (hmono j hn) _) (Real.rpow_nonneg (hmp j).le _)
  have h := tendsto_of_deficit_brackets (Real.rpow_pos_of_pos hq (-4 / 3 : ℝ))
    (limitDeficit_strictMonoOn hq) (limitDeficit_target hq)
    (continuous_limitSectorEnergy q).continuousAt hd hJ hlo hup
  simpa only [limitSectorEnergy_target hq] using h

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_QuantumSectorNearMinimizer
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace CoulombAtom

theorem quantum_sector_near_minimizer (Z : ℝ) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖ ^ 2 = 1 ∧
      formEnergy Z (graphFormVector F) < energy Z N + ε := by
  have hex : ∃ ψ : FormVector N, FormAdmissible ψ ∧
      formEnergy Z ψ < energy Z N + ε := by
    by_cases hN : N = 0
    · subst N
      obtain ⟨ψ, hψ⟩ := formDomain_nonempty 0
      refine ⟨ψ, hψ, ?_⟩
      simpa only [formEnergy, Fin.sum_univ_zero, Finset.sum_const_zero,
        mul_zero, sub_zero, add_zero, energy, ↓reduceIte, zero_add] using hε
    · have hh : sInf {e | ∃ ψ : FormVector N, FormAdmissible ψ ∧ formEnergy Z ψ = e} <
          energy Z N + ε := by
        simpa only [energy, ite_eq_right hN] using (lt_add_of_pos_right (energy Z N) hε)
      obtain ⟨e, ⟨ψ, hψ, he⟩, he'⟩ := exists_lt_of_csInf_lt (formValues_nonempty Z N) hh
      exact ⟨ψ, hψ, he ▸ he'⟩
  obtain ⟨ψ, hψ, he⟩ := hex
  refine ⟨admissibleGraph ψ hψ, admissibleGraph_norm ψ hψ, ?_⟩
  have heq := formEnergy_congr_ae Z (graphFormVector (admissibleGraph ψ hψ)) ψ
    (graphFormVector_admissibleGraph_value ψ hψ)
    (graphFormVector_admissibleGraph_gradient ψ hψ)
  exact heq ▸ he

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_Form
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

lemma insertionTerms_disjoint {N : ℕ} {T : FormVector (N+1)} (R : ℝ)
    (hc : ∀ x (j : Fin N), R ≤ ‖x j.castSucc‖ → FormZeroAt T x)
    (he : ∀ x, ‖x (Fin.last N)‖ < R → FormZeroAt T x) :
    FormsDisjoint (insertionTerm T) := by
  have hh (k l : Fin (N+1)) (hkl : k ≠ l) (x : Configuration (N+1)) :
      FormZeroAt (insertionTerm T k) x ∨ FormZeroAt (insertionTerm T l) x := by
    by_cases hk : ‖x k‖ < R
    · left
      exact insertionTerm_zero k (he _ (by simpa only [Function.comp_apply,insertionSwap_last] using hk))
    · right
      have hne : insertionSwap l k ≠ Fin.last N := by
        intro h
        have hh := congrArg (insertionSwap l) h
        exact hkl (by simpa only [insertionSwap,Equiv.swap_apply_self,Equiv.swap_apply_right] using hh)
      obtain ⟨j,hj⟩ := Fin.exists_castSucc_eq.mpr hne
      apply insertionTerm_zero l
      apply hc _ j
      simpa only [Function.comp_apply,hj,insertionSwap,Equiv.swap_apply_self] using le_of_not_gt hk
  constructor
  · intro k l hkl s x
    rcases hh k l hkl x with hk | hl
    · exact Or.inl (hk s).1
    · exact Or.inr (hl s).1
  · intro k l hkl s i a x
    rcases hh k l hkl x with hk | hl
    · exact Or.inl ((hk s).2 i a)
    · exact Or.inr ((hl s).2 i a)

lemma tensor_insertion_disjoint {N : ℕ} (ψ : FormVector N) (φ : FormVector 1) (R : ℝ)
    (hc : ∀ x i, R ≤ ‖x i‖ → FormZeroAt ψ x)
    (he : ∀ x, ‖x 0‖ < R → FormZeroAt φ x) :
    FormsDisjoint (insertionTerm (tensorForm ψ φ)) := by
  apply insertionTerms_disjoint R
  · intro x i hx
    apply tensor_zero_left
    exact hc _ i hx
  · intro x hx
    apply tensor_zero_right
    exact he _ hx

theorem normalized_wedge_trial {N : ℕ} {ψ : FormVector N} {φ : FormVector 1}
    (hψ : FormAdmissible ψ) (hφ : FormAdmissible φ) (R : ℝ)
    (hc : ∀ x i, R ≤ ‖x i‖ → FormZeroAt ψ x)
    (he : ∀ x, ‖x 0‖ < R → FormZeroAt φ x) (Z : ℝ) :
    ∃ F : FormVector (N+1), FormAdmissible F ∧ formEnergy Z F = formEnergy Z (tensorForm ψ φ) := by
  let T := tensorForm ψ φ
  have hT := hψ.sobolevFermion.sobolevVector.tensor hφ.sobolevFermion.sobolevVector
  have hTa := tensor_coreAntisymmetric hψ.sobolevFermion φ
  have hd := tensor_insertion_disjoint ψ φ R hc he
  have hm : formMass T = 1 := by
    rw [formMass_tensor,formMass,formMass,hψ.2.2.2.2.1,hφ.2.2.2.2.1,one_mul]
  have hw := formMass_wedge hT hd
  rw [hm,mul_one] at hw
  have hp : 0 < formMass (wedgeForm T) := by rw [hw]; positivity
  refine ⟨scaleForm (Real.sqrt (formMass (wedgeForm T)))⁻¹ (wedgeForm T),
    (wedgeForm_fermion hT hTa).normalize hp,?_⟩
  rw [formEnergy_scale,formEnergy_wedge hT hd,hw,inv_pow,
    Real.sq_sqrt (le_of_lt (show (0:ℝ) < N+1 by positivity))]
  field_simp


open MeasureTheory Filter
open scoped BigOperators


lemma formNuclear_nonneg {N : ℕ} (ψ : FormVector N) : 0 ≤ formNuclear ψ := by
  apply Finset.sum_nonneg; intro s _
  apply Finset.sum_nonneg; intro i _
  exact integral_nonneg fun x => div_nonneg (sq_nonneg _) (norm_nonneg _)


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialInside
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

lemma radialCut_inner {y x : Space} {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hx : ‖x-y‖ ≤ t) :
    (radialCut y ht hb 0).value x = 1 ∧ (radialCut y ht hb 1).value x = 0 := by
  simp [radialCut, radialInside, radialOutside, radialPhase_zero ht hb hx]

end CoulombAtom

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TruncationRadius
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

lemma truncationRadius_one_le (k : ℕ) : 1 ≤ truncationRadius k := by
  unfold truncationRadius; linarith [Nat.cast_nonneg (α := ℝ) k]

lemma SobolevFermion.truncate {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ) (k : ℕ) :
    SobolevFermion (truncateForm k ψ) := hψ.multiply (truncationMultiplier N k)

lemma truncation_value_le_one {N : ℕ} (k : ℕ) (x : Configuration N) :
    |(truncationMultiplier N k).value x| ≤ 1 :=
  spatial_product_sub_bound
    (radialCut 0 (truncationRadius_pos k).le (truncationRadius_pos k))
    (radialCut_partition 0 (truncationRadius_pos k).le (truncationRadius_pos k))
    (fun _ : Fin N => 0) x Finset.univ

lemma truncation_value_one {N : ℕ} (k : ℕ) (x : Configuration N)
    (hx : ∀ i, ‖x i‖ ≤ truncationRadius k) :
    (truncationMultiplier N k).value x = 1 := by
  change (∏ i, (radialCut 0 (truncationRadius_pos k).le
    (truncationRadius_pos k) 0).value (x i)) = 1
  apply Finset.prod_eq_one
  intro i _
  exact (radialCut_inner (truncationRadius_pos k).le (truncationRadius_pos k)
    (by simpa only [sub_zero] using hx i)).1

lemma truncation_derivative_zero {N : ℕ} (k : ℕ) (x : Configuration N) (i : Fin N) (a : Fin 3)
    (hx : ‖x i‖ ≤ truncationRadius k) :
    lineDeriv ℝ (truncationMultiplier N k).value x (direction i a) = 0 := by
  change lineDeriv ℝ (spatialProductValue _ _) x (direction i a) = 0
  rw [spatialProduct_derivative]
  change _ * lineDeriv ℝ (fun z => Real.cos (radialPhase 0 (truncationRadius k)
    (truncationRadius k) z)) (x i) (spaceDirections a) = 0
  rw [radial_cos_derivative, radialPhase_zero (truncationRadius_pos k).le
    (truncationRadius_pos k) (by simpa only [sub_zero] using hx)]
  simp only [Real.sin_zero, neg_zero, zero_mul, mul_zero]

lemma truncation_derivative_bound {N : ℕ} (k : ℕ) (x : Configuration N) (i : Fin N) (a : Fin 3) :
    |lineDeriv ℝ (truncationMultiplier N k).value x (direction i a)| ≤
      Real.pi * smoothTransitionBound := by
  change |lineDeriv ℝ (spatialProductValue _ _) x (direction i a)| ≤ _
  rw [spatialProduct_derivative, abs_mul]
  have hprod := spatial_product_sub_bound
    (radialCut 0 (truncationRadius_pos k).le (truncationRadius_pos k))
    (radialCut_partition 0 (truncationRadius_pos k).le (truncationRadius_pos k))
    (fun _ : Fin N => 0) x (Finset.univ.erase i)
  apply (mul_le_mul_of_nonneg_right hprod (abs_nonneg _)).trans
  rw [one_mul]
  change |lineDeriv ℝ (fun z => Real.cos (radialPhase 0 (truncationRadius k)
    (truncationRadius k) z)) (x i) (spaceDirections a)| ≤ _
  rw [radial_cos_derivative, abs_mul, abs_neg]
  apply (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans
  rw [one_mul]
  apply (radialPhase_derivative_le 0 (truncationRadius_pos k).le (truncationRadius_pos k) (x i) a).trans
  exact div_le_self (mul_pos Real.pi_pos smoothTransitionBound_pos).le (truncationRadius_one_le k)

lemma truncation_eventually_identity {N : ℕ} (x : Configuration N) :
    ∀ᶠ k : ℕ in atTop, (truncationMultiplier N k).value x = 1 ∧
      ∀ i a, lineDeriv ℝ (truncationMultiplier N k).value x (direction i a) = 0 := by
  obtain ⟨K,hK⟩ := exists_nat_gt ‖x‖
  refine eventually_atTop.mpr ⟨K,fun k hk => ?_⟩
  have hx (i : Fin N) : ‖x i‖ ≤ truncationRadius k := by
    have hki : (K:ℝ) ≤ k := by exact_mod_cast hk
    have hi : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
    unfold truncationRadius
    linarith
  exact ⟨truncation_value_one k x hx, fun i a => truncation_derivative_zero k x i a (hx i)⟩

lemma truncateForm_eventually_identity {N : ℕ} (ψ : FormVector N) (s : Spins N)
    (x : Configuration N) :
    ∀ᶠ k : ℕ in atTop, (truncateForm k ψ).value s x = ψ.value s x ∧
      ∀ i a, (truncateForm k ψ).gradient s i a x = ψ.gradient s i a x := by
  filter_upwards [truncation_eventually_identity x] with k hk
  constructor
  · change ((truncationMultiplier N k).value x : ℂ) * _ = _
    rw [hk.1]; simp only [Complex.ofReal_one, one_mul]
  · intro i a
    change ((truncationMultiplier N k).value x : ℂ) * _ +
      Complex.ofReal (lineDeriv ℝ (truncationMultiplier N k).value x (direction i a)) * _ = _
    rw [hk.1,hk.2 i a]
    simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, add_zero]

lemma truncateForm_value_sq_le {N : ℕ} (k : ℕ) (ψ : FormVector N) (s : Spins N)
    (x : Configuration N) : ‖(truncateForm k ψ).value s x‖^2 ≤ ‖ψ.value s x‖^2 := by
  change ‖((truncationMultiplier N k).value x : ℂ) * ψ.value s x‖^2 ≤ _
  rw [scaled_norm_sq]
  have hh := truncation_value_le_one k x
  have hs : (truncationMultiplier N k).value x ^ 2 ≤ 1 := by
    nlinarith [sq_abs ((truncationMultiplier N k).value x), abs_nonneg ((truncationMultiplier N k).value x)]
  exact mul_le_of_le_one_left (sq_nonneg _) hs

lemma truncateForm_gradient_sq_le {N : ℕ} (k : ℕ) (ψ : FormVector N) (s : Spins N)
    (x : Configuration N) (i : Fin N) (a : Fin 3) :
    ‖(truncateForm k ψ).gradient s i a x‖^2 ≤
      2*‖ψ.gradient s i a x‖^2 + 2*(Real.pi*smoothTransitionBound)^2*‖ψ.value s x‖^2 := by
  have hC : 0 < Real.pi*smoothTransitionBound := mul_pos Real.pi_pos smoothTransitionBound_pos
  have hnorm : ‖(truncateForm k ψ).gradient s i a x‖ ≤
      ‖ψ.gradient s i a x‖ + (Real.pi*smoothTransitionBound)*‖ψ.value s x‖ := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) (truncation_value_le_one k x))
      (mul_le_mul_of_nonneg_right (truncation_derivative_bound k x i a) (norm_nonneg _))
  nlinarith [sq_nonneg (‖ψ.gradient s i a x‖-(Real.pi*smoothTransitionBound)*‖ψ.value s x‖),
    norm_nonneg ((truncateForm k ψ).gradient s i a x), norm_nonneg (ψ.gradient s i a x),
    norm_nonneg (ψ.value s x)]

lemma truncateForm_mass_tendsto {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ) :
    Tendsto (fun k => formMass (truncateForm k ψ)) atTop (𝓝 (formMass ψ)) := by
  unfold formMass
  apply tendsto_finsetSum
  intro s _
  apply tendsto_integral_of_dominated_convergence (fun x => ‖ψ.value s x‖^2)
  · intro k; exact ((hψ.truncate k).1 s).norm.integrable_sq.aestronglyMeasurable
  · exact (hψ.1 s).norm.integrable_sq
  · intro k
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact truncateForm_value_sq_le k ψ s x
  · exact Eventually.of_forall fun x => tendsto_const_nhds.congr'
      ((truncateForm_eventually_identity ψ s x).mono fun _ hk => by simp only [hk.1])

lemma truncateForm_kinetic_tendsto {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (s : Spins N) (i : Fin N) (a : Fin 3) :
    Tendsto (fun k => ∫ x, ‖(truncateForm k ψ).gradient s i a x‖^2) atTop
      (𝓝 (∫ x, ‖ψ.gradient s i a x‖^2)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x => 2*‖ψ.gradient s i a x‖^2 + 2*(Real.pi*smoothTransitionBound)^2*‖ψ.value s x‖^2)
  · intro k; exact ((hψ.truncate k).2.1 s i a).norm.integrable_sq.aestronglyMeasurable
  · exact ((hψ.2.1 s i a).norm.integrable_sq.const_mul 2).add
      ((hψ.1 s).norm.integrable_sq.const_mul _)
  · intro k
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact truncateForm_gradient_sq_le k ψ s x i a
  · exact Eventually.of_forall fun x => tendsto_const_nhds.congr'
      ((truncateForm_eventually_identity ψ s x).mono fun _ hk => by simp only [hk.2 i a])

lemma truncateForm_coulomb_tendsto {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (s : Spins N) (d : Configuration N → ℝ) (hd : Measurable d) (hd0 : ∀ x, 0 ≤ d x)
    (hi : Integrable (fun x => ‖ψ.value s x‖^2 / d x)) :
    Tendsto (fun k => ∫ x, ‖(truncateForm k ψ).value s x‖^2 / d x) atTop
      (𝓝 (∫ x, ‖ψ.value s x‖^2 / d x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖ψ.value s x‖^2 / d x)
  · intro k
    exact (((hψ.truncate k).1 s).norm.integrable_sq.aemeasurable.div
      hd.aemeasurable).aestronglyMeasurable
  · exact hi
  · intro k
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (hd0 x))]
      exact div_le_div_of_nonneg_right (truncateForm_value_sq_le k ψ s x) (hd0 x)
  · exact Eventually.of_forall fun x => tendsto_const_nhds.congr'
      ((truncateForm_eventually_identity ψ s x).mono fun _ hk => by simp only [hk.1])

lemma truncateForm_energy_tendsto {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (Z : ℝ) : Tendsto (fun k => formEnergy Z (truncateForm k ψ)) atTop
      (𝓝 (formEnergy Z ψ)) := by
  unfold formEnergy
  apply Tendsto.add
  · apply Tendsto.sub
    · apply Tendsto.const_mul
      apply tendsto_finsetSum; intro s _
      apply tendsto_finsetSum; intro i _
      apply tendsto_finsetSum; intro a _
      exact truncateForm_kinetic_tendsto hψ s i a
    · apply Tendsto.const_mul
      apply tendsto_finsetSum; intro s _
      apply tendsto_finsetSum; intro i _
      exact truncateForm_coulomb_tendsto hψ s (fun x => ‖x i‖)
        (measurable_pi_apply i).norm (fun _ => norm_nonneg _)
        (hψ.sobolevVector.nuclear_integrable s i)
  · apply tendsto_finsetSum; intro s _
    apply tendsto_finsetSum; intro i _
    apply tendsto_finsetSum; intro j _
    by_cases hij : i < j
    · simp only [ite_eq_left hij]
      exact truncateForm_coulomb_tendsto hψ s (fun x => ‖x i-x j‖)
        ((measurable_pi_apply i).sub (measurable_pi_apply j)).norm (fun _ => norm_nonneg _)
        (hψ.sobolevVector.pair_integrable s i j (ne_of_lt hij))
    · simp only [ite_eq_right hij]
      exact tendsto_const_nhds

lemma truncation_value_zero {N : ℕ} (k : ℕ) (x : Configuration N) (i : Fin N)
    (hx : 2*truncationRadius k ≤ ‖x i‖) : (truncationMultiplier N k).value x = 0 := by
  classical
  change (∏ j, (radialCut 0 (truncationRadius_pos k).le
    (truncationRadius_pos k) 0).value (x j)) = 0
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply (radialCut_outer (truncationRadius_pos k).le (truncationRadius_pos k) ?_).1
  simpa only [sub_zero, two_mul] using hx

lemma truncateForm_support {N : ℕ} (k : ℕ) (ψ : FormVector N) (s : Spins N)
    (x : Configuration N) (i : Fin N) (hx : 2*truncationRadius k ≤ ‖x i‖) :
    (truncateForm k ψ).value s x = 0 := by
  change ((truncationMultiplier N k).value x : ℂ) * _ = _
  rw [truncation_value_zero k x i hx]
  simp

lemma truncation_gradient_zero {N : ℕ} (k : ℕ) (x : Configuration N) (i j : Fin N)
    (a : Fin 3) (hx : 2*truncationRadius k < ‖x i‖) :
    lineDeriv ℝ (truncationMultiplier N k).value x (direction j a) = 0 := by
  have he : (truncationMultiplier N k).value =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    have hh : ∀ᶠ z : Configuration N in 𝓝 x, 2*truncationRadius k < ‖z i‖ :=
      ((continuous_apply i).norm.tendsto x).eventually (eventually_gt_nhds hx)
    exact hh.mono fun z hz => truncation_value_zero k z i hz.le
  rw [he.lineDeriv_eq (𝕜 := ℝ)]
  simp only [lineDeriv, deriv_const]

lemma truncateForm_gradient_support {N : ℕ} (k : ℕ) (ψ : FormVector N) (s : Spins N)
    (x : Configuration N) (i j : Fin N) (a : Fin 3) (hx : 2*truncationRadius k < ‖x i‖) :
    (truncateForm k ψ).gradient s j a x = 0 := by
  change ((truncationMultiplier N k).value x : ℂ) * _ +
    Complex.ofReal (lineDeriv ℝ (truncationMultiplier N k).value x (direction j a)) * _ = 0
  rw [truncation_value_zero k x i hx.le, truncation_gradient_zero k x i j a hx]
  simp

theorem admissible_compact_approximation {N : ℕ} {ψ : FormVector N}
    (hψ : FormAdmissible ψ) (Z : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∃ φ : FormVector N, FormAdmissible φ ∧
      formEnergy Z φ < formEnergy Z ψ + ε ∧
      ∀ s x i, R ≤ ‖x i‖ → φ.value s x = 0 ∧ ∀ j a, φ.gradient s j a x = 0 := by
  let φ : ℕ → FormVector N := fun k =>
    scaleForm (Real.sqrt (formMass (truncateForm k ψ)))⁻¹ (truncateForm k ψ)
  have hm := truncateForm_mass_tendsto hψ.sobolevFermion
  have hmass : formMass ψ = 1 := hψ.2.2.2.2.1
  rw [hmass] at hm
  have he : Tendsto (fun k => formEnergy Z (φ k)) atTop (𝓝 (formEnergy Z ψ)) := by
    have hh := (((Real.continuous_sqrt.tendsto 1).comp hm).inv₀ (by norm_num)).pow 2
    have hh' := hh.mul (truncateForm_energy_tendsto hψ.sobolevFermion Z)
    simpa only [φ, formEnergy_scale, Real.sqrt_one, inv_one, one_pow, one_mul, Function.comp_apply] using hh'
  have hp : ∀ᶠ k : ℕ in atTop, 0 < formMass (truncateForm k ψ) :=
    hm.eventually (eventually_gt_nhds (by norm_num : (0:ℝ) < 1))
  have hene : ∀ᶠ k : ℕ in atTop, formEnergy Z (φ k) < formEnergy Z ψ + ε :=
    he.eventually (eventually_lt_nhds (lt_add_of_pos_right _ hε))
  obtain ⟨k,hk,hke⟩ := (hp.and hene).exists
  refine ⟨3*truncationRadius k, mul_pos (by norm_num) (truncationRadius_pos k), φ k,
    (hψ.sobolevFermion.truncate k).normalize hk,hke,?_⟩
  intro s x i hx
  have hx' : 2*truncationRadius k < ‖x i‖ := by linarith [truncationRadius_pos k]
  constructor
  · change _ * (truncateForm k ψ).value s x = 0
    rw [truncateForm_support k ψ s x i hx'.le, mul_zero]
  · intro j a
    change _ * (truncateForm k ψ).gradient s j a x = 0
    rw [truncateForm_gradient_support k ψ s x i j a hx', mul_zero]

theorem quantum_sector_compact_near_minimizer (Z : ℝ) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∃ φ : FormVector N, FormAdmissible φ ∧
      formEnergy Z φ < energy Z N + ε ∧
      ∀ s x i, R ≤ ‖x i‖ → φ.value s x = 0 ∧ ∀ j a, φ.gradient s j a x = 0 := by
  obtain ⟨F,hF,he⟩ := quantum_sector_near_minimizer Z N (half_pos hε)
  obtain ⟨R,hR,φ,hφ,hq,hs⟩ := admissible_compact_approximation
    (graphFormVector_admissible F hF) Z (half_pos hε)
  exact ⟨R,hR,φ,hφ,by linarith,hs⟩

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_DiffuseSeed
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

lemma diffuseSeed_smooth (R : ℝ) : ContDiff ℝ ∞ (diffuseSeed R) :=
  (trialSeed_smooth 1).comp (R⁻¹ • ContinuousLinearMap.id ℝ (Configuration 1)).contDiff

lemma diffuseSeed_compact {R : ℝ} (hR : 0 < R) : HasCompactSupport (diffuseSeed R) :=
  (trialSeed_compact 1).comp_smul (inv_ne_zero hR.ne')

lemma diffuseRaw_sobolev (R : ℝ) (hR : 0 < R) : SobolevFermion (diffuseRaw R) := by
  refine ⟨fun _ => (diffuseSeed_smooth R).continuous.memLp_of_hasCompactSupport
    (diffuseSeed_compact hR),fun s i a => ?_,fun s i a φ hφ hcφ => ?_,?_⟩
  · exact (smooth_derivative_continuous (diffuseSeed_smooth R) _).memLp_of_hasCompactSupport
      (compact_derivative (diffuseSeed_compact hR) _)
  · exact smooth_weak_gradient (diffuseSeed_smooth R) (diffuseSeed_compact hR) hφ hcφ _
  · intro π s
    have hp : π = 1 := Subsingleton.elim _ _
    subst π
    exact Eventually.of_forall fun x => by simp [diffuseRaw,smoothForm]

lemma diffuseRaw_mass_pos {R : ℝ} (hR : 0 < R) : 0 < formMass (diffuseRaw R) := by
  have hn : diffuseSeed R (R • trialCenter 1) = 1 := by
    simp only [diffuseSeed,smul_smul,inv_mul_cancel₀ hR.ne',one_smul,trialSeed_center]
  have hi : 0 < ∫ x, ‖diffuseSeed R x‖^2 :=
    ((diffuseSeed_smooth R).continuous.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (compact_norm_sq (diffuseSeed_compact hR)) (fun x => sq_nonneg _)
      (x := R • trialCenter 1) (by rw [hn]; norm_num)
  change 0 < ∑ _s : Spins 1, ∫ x, ‖diffuseSeed R x‖^2
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_pos (Nat.cast_pos.mpr Fintype.card_pos) hi

lemma diffuseRaw_gradient (R : ℝ) (s : Spins 1) (i : Fin 1) (a : Fin 3) (x : Configuration 1) :
    (diffuseRaw R).gradient s i a x = R⁻¹ •
      (smoothForm (trialSeed 1)).gradient s i a (R⁻¹ • x) := by
  change fderiv ℝ ((trialSeed 1) ∘ ⇑(R⁻¹ • ContinuousLinearMap.id ℝ (Configuration 1))) x (direction i a) = _
  rw [fderiv_comp x ((trialSeed_smooth 1).differentiable (by simp)).differentiableAt
    (R⁻¹ • ContinuousLinearMap.id ℝ (Configuration 1)).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.fderiv,
    smul_apply,ContinuousLinearMap.id_apply,map_smul,smoothForm]

lemma diffuseRaw_mass (R : ℝ) (hR : 0 < R) :
    formMass (diffuseRaw R) = R ^ Module.finrank ℝ (Configuration 1) *
      formMass (smoothForm (trialSeed 1)) := by
  unfold formMass
  simp only [diffuseRaw,smoothForm,diffuseSeed]
  have hi := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Configuration 1))
    (fun x => ‖trialSeed 1 x‖^2) hR.le
  simp only [smul_eq_mul] at hi
  simp_rw [hi,Finset.mul_sum]

lemma diffuseRaw_kinetic (R : ℝ) (hR : 0 < R) :
    formKinetic (diffuseRaw R) = R⁻¹^2 * R ^ Module.finrank ℝ (Configuration 1) *
      formKinetic (smoothForm (trialSeed 1)) := by
  unfold formKinetic
  simp_rw [diffuseRaw_gradient,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]
  have hi (s : Spins 1) (i : Fin 1) (a : Fin 3) :=
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Configuration 1))
      (fun x => ‖(smoothForm (trialSeed 1)).gradient s i a x‖^2) hR.le
  simp only [smul_eq_mul] at hi
  simp_rw [hi,← Finset.mul_sum]
  ring

lemma diffuseOrbital_admissible {R : ℝ} (hR : 0 < R) : FormAdmissible (diffuseOrbital R) :=
  (diffuseRaw_sobolev R hR).normalize (diffuseRaw_mass_pos hR)

lemma diffuseOrbital_kinetic {R : ℝ} (hR : 0 < R) :
    formKinetic (diffuseOrbital R) = diffuseKinetic / R^2 := by
  have hmpos : 0 < formMass (smoothForm (trialSeed 1)) := by
    have hh := diffuseRaw_mass_pos (by norm_num : (0:ℝ)<1)
    rw [diffuseRaw_mass 1 (by norm_num), one_pow, one_mul] at hh
    exact hh
  rw [diffuseOrbital,formKinetic_scale,inv_pow,Real.sq_sqrt (diffuseRaw_mass_pos hR).le,
    diffuseRaw_mass R hR,diffuseRaw_kinetic R hR,diffuseKinetic]
  field_simp

lemma diffuseSeed_zero {R : ℝ} (hR : 0 < R) {x : Configuration 1} (hx : ‖x 0‖ < R) :
    diffuseSeed R x = 0 := by
  by_contra hn
  have hh := trialSeed_nucleus hn (0 : Fin 1)
  change 1 ≤ ‖R⁻¹ • x 0‖ at hh
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)] at hh
  have hl : R⁻¹ * ‖x 0‖ < 1 := by
    rw [← div_eq_inv_mul,div_lt_one hR]
    exact hx
  exact not_lt_of_ge hh hl

lemma diffuseRaw_zero {R : ℝ} (hR : 0 < R) {x : Configuration 1} (hx : ‖x 0‖ < R) :
    FormZeroAt (diffuseRaw R) x := by
  have he : diffuseSeed R =ᶠ[𝓝 x] fun _ => (0:ℂ) :=
    (((continuous_apply (0 : Fin 1)).norm.tendsto x).eventually (eventually_lt_nhds hx)).mono
      fun _ hy => diffuseSeed_zero hR hy
  intro s
  refine ⟨diffuseSeed_zero hR hx,fun i a => ?_⟩
  change fderiv ℝ (diffuseSeed R) x (direction i a) = 0
  rw [he.fderiv_eq]
  simp

lemma diffuseOrbital_zero {R : ℝ} (hR : 0 < R) {x : Configuration 1} (hx : ‖x 0‖ < R) :
    FormZeroAt (diffuseOrbital R) x := by
  intro s
  have hh := diffuseRaw_zero hR hx s
  constructor
  · change _ * (diffuseRaw R).value s x = 0
    rw [hh.1,mul_zero]
  · intro i a
    change _ * (diffuseRaw R).gradient s i a x = 0
    rw [hh.2,mul_zero]


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators


lemma tensorCross_le {N : ℕ} {ψ : FormVector N} {φ : FormVector 1}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ) {R d : ℝ} (hd : 0 < d)
    (hc : ∀ s x i, R ≤ ‖x i‖ → ψ.value s x = 0)
    (he : ∀ s x, ‖x 0‖ < R+d → φ.value s x = 0) :
    tensorCross ψ φ ≤ (N : ℝ)/d * formMass ψ * formMass φ := by
  have hT := hψ.tensor hφ
  have hi (s : Spins N) (t : Spins 1) (i : Fin N) :
      (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z i.castSucc-z (Fin.last N)‖) ≤
      d⁻¹ * (∫ x, ‖ψ.value s x‖^2) * (∫ y, ‖φ.value t y‖^2) := by
    have hn : i.castSucc ≠ Fin.last N := Fin.castSucc_ne_last i
    calc
      _ ≤ ∫ z, d⁻¹ * ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 := by
        apply integral_mono
          (pair_integrable _ _ hn (hT.1 _) (hT.2.1 _ _) (hT.2.2 _ _))
          (((hT.1 _).integrable_norm_pow (by norm_num)).const_mul d⁻¹)
        intro z
        dsimp only
        by_cases hz : (tensorForm ψ φ).value (joinLists s t) z = 0
        · simp only [hz,norm_zero,zero_pow (by norm_num : 2 ≠ 0),zero_div,mul_zero,le_refl]
        · have hz' : ψ.value s (leftList z) ≠ 0 ∧ φ.value t (rightList z) ≠ 0 := by
            simpa only [tensorForm,leftList_join,rightList_join,mul_ne_zero_iff] using hz
          have hin : ‖z i.castSucc‖ < R := lt_of_not_ge fun h => hz'.1 (hc _ _ i h)
          have hout : R+d ≤ ‖z (Fin.last N)‖ := le_of_not_gt fun h => hz'.2 (he _ _ h)
          have hg : d ≤ ‖z i.castSucc-z (Fin.last N)‖ := by
            have ht := norm_sub_norm_le (z (Fin.last N)) (z i.castSucc)
            rw [norm_sub_rev] at ht
            linarith
          rw [← div_eq_inv_mul]
          exact div_le_div_of_nonneg_left (sq_nonneg _) hd hg
      _ = _ := by
        rw [integral_const_mul]
        have hh : (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2) =
            (∫ x, ‖ψ.value s x‖^2)*(∫ y, ‖φ.value t y‖^2) := by
          simp only [tensorForm,leftList_join,rightList_join,norm_mul,mul_pow]
          exact integral_product_join (N := N) (M := 1)
            (fun x => ‖ψ.value s x‖^2) (fun y => ‖φ.value t y‖^2)
        rw [hh,mul_assoc]
  calc
    tensorCross ψ φ ≤ ∑ s : Spins N, ∑ t : Spins 1, ∑ _i : Fin N,
        d⁻¹ * (∫ x, ‖ψ.value s x‖^2) * (∫ y, ‖φ.value t y‖^2) := by
      exact Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun i _ => hi s t i
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      unfold formMass
      simp_rw [mul_assoc,← Finset.mul_sum,← Finset.sum_mul]
      ring

lemma exterior_insertion_trial {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ)
    {Z R r : ℝ} (hZ : 0 ≤ Z) (hR : 0 < R) (hr : 2*R ≤ r)
    (hc : ∀ x i, R ≤ ‖x i‖ → FormZeroAt ψ x) :
    ∃ F : FormVector (N+1), FormAdmissible F ∧
      formEnergy Z F ≤ formEnergy Z ψ + diffuseKinetic/r^2 + 2*(N : ℝ)/r := by
  have hrp : 0 < r := lt_of_lt_of_le (mul_pos (by norm_num) hR) hr
  have hφ := diffuseOrbital_admissible hrp
  obtain ⟨F,hF,hFE⟩ := normalized_wedge_trial hψ hφ R hc
    (fun x hx => diffuseOrbital_zero hrp (lt_of_lt_of_le hx (by linarith))) Z
  refine ⟨F,hF,?_⟩
  have hcross := tensorCross_le hψ.sobolevFermion.sobolevVector
    hφ.sobolevFermion.sobolevVector (R := R) (d := r/2) (half_pos hrp)
    (fun s x i hx => (hc x i hx s).1)
    (fun s x hx => (diffuseOrbital_zero hrp (lt_of_lt_of_le hx (by linarith)) s).1)
  have hmψ : formMass ψ = 1 := hψ.2.2.2.2.1
  have hmφ : formMass (diffuseOrbital r) = 1 := hφ.2.2.2.2.1
  rw [hmψ,hmφ,mul_one,mul_one] at hcross
  rw [hFE,formEnergy_tensor_one,hmψ,hmφ,mul_one,one_mul,diffuseOrbital_kinetic hrp]
  have hn := mul_nonneg hZ (formNuclear_nonneg (diffuseOrbital r))
  have hc' : (N : ℝ)/(r/2) = 2*(N : ℝ)/r := by ring
  rw [hc'] at hcross
  linarith

theorem quantum_energy_succ_le {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ) :
    energy Z (N+1) ≤ energy Z N := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨R,hR,ψ,hψ,hene,hc⟩ := quantum_sector_compact_near_minimizer Z N (half_pos hε)
  have ht : Tendsto (fun r : ℝ => diffuseKinetic/r^2 + 2*(N : ℝ)/r) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := diffuseKinetic)).div_atTop
      (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
    have hk := (tendsto_const_nhds (x := 2*(N : ℝ))).div_atTop tendsto_id
    simpa only [zero_add, id_eq] using hh.add hk
  have he : ∀ᶠ r : ℝ in atTop, diffuseKinetic/r^2 + 2*(N : ℝ)/r < ε/2 :=
    ht.eventually (eventually_lt_nhds (half_pos hε))
  obtain ⟨r,hlarge,herror⟩ := ((eventually_ge_atTop (2*R)).and he).exists
  obtain ⟨F,hF,hbound⟩ := exterior_insertion_trial hψ hZ hR hlarge
    (fun x i hx s => hc s x i hx)
  have hl := energy_le_form hZ hF
  linarith

theorem quantum_energy_antitone {Z : ℝ} (hZ : 0 ≤ Z) : Antitone (energy Z) :=
  antitone_nat_of_succ_le (quantum_energy_succ_le hZ)


open MeasureTheory Filter
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierWeakMaxGeneralBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric InnerProductSpace
open scoped Topology Convolution BigOperators Manifold

open CoulombAnalysis CoulombPDE CoulombAtom

lemma locallyIntegrable_mul_test {h φ : TFSpace → ℝ} (hh : LocallyIntegrable h)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Integrable (fun x => h x*φ x) :=
  hh.integrable_smul_right_of_hasCompactSupport hφ hcφ

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierNonlinearBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology Convolution BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

lemma WeakLaplacianLowerOn.mono_set {U V : Set TFSpace} {u h : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (hVU : V ⊆ U) : WeakLaplacianLowerOn V u h :=
  fun φ hφ hc hs hn => hw φ hφ hc (hs.trans hVU) hn

lemma WeakLaplacianLowerOn.congr_field {U : Set TFSpace} {u v h : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (he : ∀ x ∈ U, u x = v x) :
    WeakLaplacianLowerOn U v h := by
  intro φ hφ hc hs hn
  calc
    _ ≤ ∫ x, u x*Δ φ x := hw φ hφ hc hs hn
    _ = _ := integral_congr_ae (Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : Δ φ x = 0
      · rw [hx,mul_zero,mul_zero]
      · rw [he x (hs (tfLaplacian_support hφ hx))])

lemma WeakLaplacianLowerOn.source_mono_ae {U : Set TFSpace} {u h h' : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (hh : LocallyIntegrable h)
    (hh' : LocallyIntegrable h') (hle : ∀ᵐ x, x ∈ U → h' x ≤ h x) :
    WeakLaplacianLowerOn U u h' := by
  intro φ hφ hc hs hn
  apply le_trans _ (hw φ hφ hc hs hn)
  apply integral_mono_ae (locallyIntegrable_mul_test hh' hφ.continuous hc)
    (locallyIntegrable_mul_test hh hφ.continuous hc)
  filter_upwards [hle] with x hx
  by_cases hφx : φ x = 0
  · simp only [hφx,mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right (hx (hs (subset_tsupport φ hφx))) (hn x)

lemma WeakLaplacianLowerOn.source_mono {U : Set TFSpace} {u h h' : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (hh : LocallyIntegrable h)
    (hh' : LocallyIntegrable h') (hle : ∀ x ∈ U, h' x ≤ h x) :
    WeakLaplacianLowerOn U u h' := hw.source_mono_ae hh hh' (Eventually.of_forall hle)

lemma semilinear_source_locallyIntegrable {g χ u : TFSpace → ℝ} {F : ℝ → ℝ}
    (hg : LocallyIntegrable g) (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hF : Continuous F) (hu : Continuous u) :
    LocallyIntegrable (fun x => g x+χ x*F (u x)) := by
  have hχl : LocallyIntegrable χ :=
    (memLp_top_of_bound hχ.aestronglyMeasurable 1 (Eventually.of_forall hbχ)).locallyIntegrable le_top
  exact hg.add (LocallyIntegrable.mul_continuous (hF.comp hu) hχl)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_BarrierConditionalBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CoulombBarrier

lemma reaction_monotone {k : ℝ} (hk : 0 ≤ k) : Monotone (reaction k) := by
  intro s t hst
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (le_max_right _ _) (max_le_max hst le_rfl) (by norm_num))
    (by positivity)

lemma reaction_continuous (k : ℝ) : Continuous (reaction k) := by
  apply continuous_const.mul
  exact (continuous_id.max continuous_const).rpow_const (fun _ => Or.inr (by norm_num))

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierNuclearBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

lemma nuclearField_locallyIntegrable (Z : ℝ) : LocallyIntegrable (nuclearField Z) := by
  change LocallyIntegrable (fun x : TFSpace => Z*‖x‖⁻¹)
  exact newtonInverse_locallyIntegrable.smul Z

lemma clippedNuclearField_continuous (Z : ℝ) {R : ℝ} (hR : 0 < R) :
    Continuous (clippedNuclearField Z R) := by
  exact continuous_const.div (continuous_const.max continuous_norm)
    (fun x => ne_of_gt (hR.trans_le (le_max_left R ‖x‖)))

lemma weighted_clipped_reaction (Z R : ℝ) {χ : TFSpace → ℝ}
    (hχ : ∀ x, ‖x‖ < R → χ x = 0) (F : ℝ → ℝ) (t : ℝ) (x : TFSpace) :
    χ x*F (nuclearField Z x+t) = χ x*F (clippedNuclearField Z R x+t) := by
  by_cases hx : ‖x‖ < R
  · rw [hχ x hx,zero_mul,zero_mul]
  · simp only [clippedNuclearField,max_eq_right (le_of_not_gt hx),nuclearField]

lemma nuclearField_weak_laplacian (Z : ℝ) {φ : TFSpace → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, nuclearField Z x*Δ φ x) = -(4*Real.pi*Z)*φ 0 := by
  have h := tfPotential_laplacian hφ hc (0 : TFSpace)
  have he : (fun x => nuclearField Z x*Δ φ x) = fun x => Z*(Δ φ x/‖x‖) := by
    funext x
    dsimp only [nuclearField]
    ring
  rw [he,integral_const_mul]
  simp only [tfPotential,zero_sub,norm_neg] at h
  rw [h]
  ring

theorem weakNuclearLower_add_iff {U : Set TFSpace} (Z : ℝ) {u h : TFSpace → ℝ}
    (hu : LocallyIntegrable u) :
    WeakNuclearLowerOn U Z (fun x => nuclearField Z x+u x) h ↔
      WeakLaplacianLowerOn U u h := by
  have he (φ : TFSpace → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
      (∫ x, (nuclearField Z x+u x)*Δ φ x) =
        -(4*Real.pi*Z)*φ 0+(∫ x, u x*Δ φ x) := by
    simp_rw [add_mul]
    rw [integral_add
      (locallyIntegrable_mul_test (nuclearField_locallyIntegrable Z)
        (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc))
      (locallyIntegrable_mul_test hu (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc)),
      nuclearField_weak_laplacian Z hφ hc]
  constructor
  · intro hw φ hφ hc hs hn
    have ht := hw φ hφ hc hs hn
    rw [he φ hφ hc] at ht
    exact (add_le_add_iff_left _).mp ht
  · intro hw φ hφ hc hs hn
    rw [he φ hφ hc]
    exact add_le_add_right (hw φ hφ hc hs hn) _

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BoundedL1PotentialBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma bounded_coulomb_majorant {ρ : TFSpace → ℝ} {M : ℝ}
    (_hM : 0 ≤ M) (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x z : TFSpace) :
    ρ z/‖x-z‖ ≤ M*truncatedCoulomb 1 (x-z)+ρ z := by
  by_cases hd : ‖x-z‖ < 1
  · rw [truncatedCoulomb,indicator_of_mem (mem_ball_zero_iff.mpr hd)]
    have hh := mul_le_mul_of_nonneg_right (hb z) (inv_nonneg.mpr (norm_nonneg (x-z)))
    simp only [div_eq_mul_inv,one_mul] at hh ⊢
    linarith [hn z]
  · rw [truncatedCoulomb,indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hd),mul_zero,zero_add]
    have hd' : 1 ≤ ‖x-z‖ := le_of_not_gt hd
    exact (div_le_self (hn z) hd')

lemma bounded_invSquare_majorant {ρ : TFSpace → ℝ} {M : ℝ}
    (_hM : 0 ≤ M) (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x z : TFSpace) :
    ρ z*‖x-z‖⁻¹^2 ≤ M*truncatedInvSquare 1 (x-z)+ρ z := by
  by_cases hd : ‖x-z‖ < 1
  · rw [truncatedInvSquare,indicator_of_mem (mem_ball_zero_iff.mpr hd)]
    have hh := mul_le_mul_of_nonneg_right (hb z) (sq_nonneg ‖x-z‖⁻¹)
    linarith [hn z]
  · rw [truncatedInvSquare,indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hd),mul_zero,zero_add]
    have hi : ‖x-z‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (le_of_not_gt hd)
    have hi0 := inv_nonneg.mpr (norm_nonneg (x-z))
    have hs : ‖x-z‖⁻¹^2 ≤ 1 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hs (hn z)).trans_eq (mul_one _)

lemma bounded_L1_potential_integrable {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x : TFSpace) :
    Integrable (fun z => ρ z/‖x-z‖) := by
  have hk : Integrable (fun z => truncatedCoulomb 1 (x-z)) :=
    (tfSubMap_preserving x).integrable_comp (truncatedCoulomb_integrable 1).aestronglyMeasurable
      |>.mpr (truncatedCoulomb_integrable 1)
  apply ((hk.const_mul M).add hi).mono' (hm.div (measurable_const.sub measurable_id).norm).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖ρ z/‖x-z‖‖ ≤ M*truncatedCoulomb 1 (x-z)+ρ z
    rw [Real.norm_of_nonneg (div_nonneg (hn z) (norm_nonneg _))]
    exact bounded_coulomb_majorant hM hn hb x z

lemma bounded_L1_potential_difference {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x y : TFSpace) :
    |tfPotential ρ x-tfPotential ρ y| ≤ (4*Real.pi*M+∫ z, ρ z)*‖x-y‖ := by
  have hpi (w : TFSpace) := bounded_L1_potential_integrable hm hi hM hn hb w
  let A (w z : TFSpace) := M*truncatedInvSquare 1 (w-z)+ρ z
  have hk (w : TFSpace) : Integrable (fun z => truncatedInvSquare 1 (w-z)) :=
    (tfSubMap_preserving w).integrable_comp (truncatedInvSquare_integrable 1).aestronglyMeasurable
      |>.mpr (truncatedInvSquare_integrable 1)
  have hAi (w : TFSpace) : Integrable (A w) := ((hk w).const_mul M).add hi
  have hAm (w : TFSpace) : (∫ z, A w z) = 4*Real.pi*M+∫ z, ρ z := by
    dsimp only [A]
    rw [integral_add ((hk w).const_mul M) hi,integral_const_mul,integral_sub_left_eq_self,
      truncatedInvSquare_integral (by norm_num : (0:ℝ) < 1)]
    ring
  have he : (∫ z, ρ z/‖x-z‖-ρ z/‖y-z‖) = tfPotential ρ x-tfPotential ρ y :=
    integral_sub (hpi x) (hpi y)
  rw [←he]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ z, (‖x-y‖/2)*(A x z+A y z) := by
      apply integral_mono_ae ((hpi x).sub (hpi y)).abs (((hAi x).add (hAi y)).const_mul _)
      filter_upwards [volume.ae_ne x,volume.ae_ne y] with z hzx hzy
      change |ρ z/‖x-z‖-ρ z/‖y-z‖| ≤ _
      rw [div_eq_mul_inv,div_eq_mul_inv,←mul_sub,abs_mul,abs_of_nonneg (hn z)]
      calc
        _ ≤ ρ z*(‖x-y‖*(‖x-z‖⁻¹^2+‖y-z‖⁻¹^2)/2) :=
          mul_le_mul_of_nonneg_left (coulomb_inv_difference hzx hzy) (hn z)
        _ = (‖x-y‖/2)*(ρ z*‖x-z‖⁻¹^2+ρ z*‖y-z‖⁻¹^2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
          (bounded_invSquare_majorant hM hn hb x z) (bounded_invSquare_majorant hM hn hb y z)) (by positivity)
    _ = _ := by
      rw [integral_const_mul,integral_add (hAi x) (hAi y),hAm,hAm]
      ring

lemma bounded_L1_potential_lipschitz {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) :
    LipschitzWith ⟨4*Real.pi*M+∫ z, ρ z,add_nonneg (by positivity) (integral_nonneg hn)⟩ (tfPotential ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖tfPotential ρ x-tfPotential ρ y‖ ≤ (4*Real.pi*M+∫ z, ρ z)*‖x-y‖
  simpa only [Real.norm_eq_abs] using bounded_L1_potential_difference hm hi hM hn hb x y

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BoundedL1PoissonBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BoundedL1Poisson_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology ContDiff

namespace CoulombAnalysis
open CoulombAtom

lemma bounded_L1_laplacian_pair_integrable {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    {φ : TFSpace → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z : TFSpace × TFSpace => ρ z.2/‖z.1-z.2‖*Δ φ z.1) (volume.prod volume) := by
  have hΔ := tfLaplacian_continuous hφ
  have hΔc := tfLaplacian_compact hφ hc
  have hj : Measurable (fun z : TFSpace × TFSpace => ρ z.2/‖z.1-z.2‖*Δ φ z.1) :=
    ((hm.comp measurable_snd).div (measurable_fst.sub measurable_snd).norm).mul (hΔ.measurable.comp measurable_fst)
  apply (integrable_prod_iff hj.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun x => (bounded_L1_potential_integrable hm hi hM hn hb x).mul_const (Δ φ x)),?_⟩
  have hp := (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous
  have htest := CoulombBarrier.locallyIntegrable_mul_test hp.locallyIntegrable hΔ.norm hΔc.norm
  have he (x : TFSpace) : (∫ y, ‖ρ y/‖x-y‖*Δ φ x‖) = tfPotential ρ x*‖Δ φ x‖ := by
    simp_rw [norm_mul,Real.norm_of_nonneg (div_nonneg (hn _) (norm_nonneg _))]
    exact integral_mul_const _ _
  simpa only [he] using htest

theorem bounded_L1_weak_poisson {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    {φ : TFSpace → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, tfPotential ρ x*Δ φ x) = -(4*Real.pi)*(∫ x, ρ x*φ x) := by
  calc
    _ = ∫ x, ∫ y, ρ y/‖x-y‖*Δ φ x := by simp only [integral_mul_const,tfPotential]
    _ = ∫ y, ∫ x, ρ y/‖x-y‖*Δ φ x :=
      integral_integral_swap (bounded_L1_laplacian_pair_integrable hm hi hM hn hb hφ hc)
    _ = ∫ y, ρ y*tfPotential (Δ φ) y := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        change (∫ x, ρ y/‖x-y‖*Δ φ x) = ρ y*(∫ x, Δ φ x/‖y-x‖)
        rw [←integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun x => by dsimp only; rw [norm_sub_rev]; ring
    _ = _ := by
      simp_rw [tfPotential_laplacian hφ hc]
      rw [←integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by ring

end CoulombAnalysis

end Work_BoundedL1Poisson_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_FiniteProfile
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
namespace CoulombPDE

lemma FiniteProfile.compare {d Z W : ℝ} {F G : Space → ℝ}
    (hF : FiniteProfile d Z F) (hG : FiniteProfile d W G) (hd : 0 ≤ d) (hZW : Z < W)
    (x : Space) (hx : x ≠ 0) : F x ≤ G x := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  let u : Space → ℝ := fun y => F y - (G y + δ)
  have hgd (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 (G + fun _ : Space => δ) y :=
    (hG.regular y hy).add contDiffAt_const
  have hdif (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 u y := (hF.regular y hy).sub (hgd y hy)
  have hl (y : Space) (hy : y ≠ 0) (hp : 0 < u y) : 0 ≤ Δ u y := by
    have hfg : G y ≤ F y := by dsimp [u] at hp; linarith
    change 0 ≤ Δ (F - (G + fun _ : Space => δ)) y
    rw [(hF.regular y hy).laplacian_sub (hgd y hy),
      (hG.regular y hy).laplacian_add (show ContDiffAt ℝ 2 (fun _ : Space => δ) y from contDiffAt_const),
      laplacian_const, Pi.zero_apply, add_zero, hF.equation y hy, hG.equation y hy]
    exact sub_nonneg.mpr (reaction_monotone hd hfg)
  have hnear : ∃ a > 0, ∀ y, y ≠ 0 → ‖y‖ ≤ a → u y ≤ 0 := by
    obtain ⟨C, hC, a, ha, hnF⟩ := hF.nucleus
    obtain ⟨D, hD, b, hb, hnG⟩ := hG.nucleus
    refine ⟨min (min a b) ((W-Z)/(C+D+1)),
      lt_min (lt_min ha hb) (div_pos (sub_pos.mpr hZW) (by linarith)), ?_⟩
    intro y hy hr
    have hFa := (abs_le.mp (hnF y hy (hr.trans ((min_le_left _ _).trans (min_le_left _ _))))).2
    have hGa := (abs_le.mp (hnG y hy (hr.trans ((min_le_left _ _).trans (min_le_right _ _))))).1
    have hsmall := (le_div_iff₀ (show 0 < C+D+1 by linarith)).mp (hr.trans (min_le_right _ _))
    have hgap : C+D ≤ (W-Z)/‖y‖ := (le_div_iff₀ (norm_pos_iff.mpr hy)).mpr (by nlinarith [norm_nonneg y])
    rw [sub_div] at hgap
    dsimp [u]
    linarith
  have hfar : ∃ R > 0, ∀ y, R ≤ ‖y‖ → u y ≤ 0 := by
    obtain ⟨a, ha, hFa⟩ := hF.decay (δ/2) (by positivity)
    obtain ⟨b, hb, hGb⟩ := hG.decay (δ/2) (by positivity)
    refine ⟨max a b, ha.trans_le (le_max_left _ _), ?_⟩
    intro y hy
    have hf := abs_lt.mp (hFa y ((le_max_left _ _).trans hy))
    have hg := abs_lt.mp (hGb y ((le_max_right _ _).trans hy))
    dsimp [u]
    linarith
  have hh := global_punctured_maximum_principle hdif hl hnear hfar x hx
  dsimp [u] at hh
  linarith

end CoulombPDE

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfReactionCoefficient
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian

open MeasureTheory Filter Set Metric Topology
section
open CoulombAtom

namespace TFUnitData
variable {Z : ℝ} (D : TFUnitData Z)

lemma field_radial : IsRadial D.field := by
  intro x y hxy
  unfold field tfField
  rw [hxy, tfPotential_radial D.radial x y hxy]

lemma charge_equation {r : ℝ} (hr : 0 < r) (hZ : 0 < Z) :
    HasDerivAt D.charge (-r^2 * CoulombPDE.reaction tfReactionCoefficient (D.radialField r)) r := by
  have hh := D.charge_hasDerivAt hr
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  have hray : D.radialField r = tfField Z D.density (r • radialAxis) := D.radialField_ray hZ hr
  rw [radialTrace, D.euler, tfEulerDensity, ← hray]
  unfold CoulombPDE.reaction tfReactionCoefficient
  rw [Real.div_rpow (le_max_right _ _) (mul_pos (by norm_num) tfKinetic_pos).le]
  ring

lemma deriv_bound (hZ : 0 < Z) {a r : ℝ} (ha : 0 < a) (hr : a ≤ r) :
    ‖deriv D.radialField r‖ ≤ slopeCap a := by
  rw [(D.radialField_hasDerivAt (ha.trans_le hr)).deriv,
    norm_div, norm_neg, Real.norm_of_nonneg (D.charge_nonneg hZ r), Real.norm_of_nonneg (sq_nonneg r)]
  exact (div_le_div_of_nonneg_right (D.charge_le_cap hZ ha hr) (sq_nonneg r)).trans
    (div_le_div_of_nonneg_left (chargeCap_pos ha).le (sq_pos_of_pos ha) (by nlinarith))

lemma lipschitz (hZ : 0 < Z) {a : ℝ} (ha : 0 < a) :
    LipschitzOnWith ⟨slopeCap a, (slopeCap_pos ha).le⟩ D.radialField (Ici a) := by
  apply (convex_Ici a).lipschitzOnWith_of_nnnorm_deriv_le
    (fun r hr => (D.radialField_hasDerivAt (ha.trans_le hr)).differentiableAt)
  exact fun r hr => D.deriv_bound hZ ha hr

end TFUnitData
end

open MeasureTheory Filter Set Metric Topology

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_WeakPositiveComparisonBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_WeakPositiveComparison_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

open CoulombAtom

theorem weak_subharmonic_positive_ball {u : Space → ℝ} {R : ℝ}
    (hR : 0 < R) (hu : ContinuousOn u (closedBall 0 R))
    (hb : ∀ x : Space, ‖x‖ = R → u x ≤ 0)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 R ∩ {x | 0 < u x} → (∀ x, 0 ≤ g x) →
      0 ≤ ∫ x, u x*Δ g x) : ∀ x ∈ closedBall (0 : Space) R, u x ≤ 0 := by
  intro x hx
  by_contra! hux
  let e := u x/(2*(R^2+1))
  have he : 0 < e := div_pos hux (by positivity)
  have heq : e*(2*(R^2+1)) = u x := div_mul_cancel₀ _ (by positivity)
  let w : Space → ℝ := fun z => u z+e*(‖z‖^2-R^2)
  have hwcont : ContinuousOn w (closedBall 0 R) :=
    hu.add (continuousOn_const.mul ((continuous_norm.pow 2).continuousOn.sub continuousOn_const))
  have hwx : 0 < w x := by
    dsimp only [w]
    nlinarith [sq_nonneg ‖x‖,mul_nonneg he.le (sq_nonneg ‖x‖),sq_nonneg R]
  obtain ⟨y,hy,hmax⟩ := (isCompact_closedBall (0 : Space) R).exists_isMaxOn ⟨x,hx⟩ hwcont
  have hwy : 0 < w y := hwx.trans_le (hmax hx)
  have hyi : y ∈ ball (0 : Space) R := by
    have hyR : ‖y‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hy
    by_contra hn
    have heqR : ‖y‖ = R := le_antisymm hyR (le_of_not_gt (by simpa only [mem_ball,dist_zero_right] using hn))
    have hub := hb y heqR
    dsimp only [w] at hwy
    rw [heqR,sub_self,mul_zero,add_zero] at hwy
    exact (not_lt_of_ge hub) hwy
  have huyp : 0 < u y := by
    have hyR : ‖y‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hy
    have hsq := pow_le_pow_left₀ (norm_nonneg y) hyR 2
    have hneg := mul_nonpos_of_nonneg_of_nonpos he.le (sub_nonpos.mpr hsq)
    dsimp only [w] at hwy
    linarith
  have hyn : closedBall (0 : Space) R ∈ 𝓝 y :=
    mem_of_superset (isOpen_ball.mem_nhds hyi) ball_subset_closedBall
  have hnb : ball (0 : Space) R ∩ {z | 0 < u z} ∈ 𝓝 y :=
    inter_mem (isOpen_ball.mem_nhds hyi)
      ((hu.continuousAt hyn).preimage_mem_nhds (Ioi_mem_nhds huyp))
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hnb
  have hsub : closedBall y (r/2) ⊆ ball (0 : Space) R ∩ {z | 0 < u z} :=
    (closedBall_subset_ball (half_lt_self hr)).trans hrs
  apply weak_laplacian_no_positive_at_max_local
    (hwcont.mono (hsub.trans (inter_subset_left.trans ball_subset_closedBall)))
    (half_pos hr) (mul_pos (by norm_num : (0:ℝ) < 6) he)
  · intro z hz
    exact hmax (ball_subset_closedBall (hsub (ball_subset_closedBall hz)).1)
  · intro g hg hcg hs hn
    have hs' : tsupport g ⊆ ball (0 : Space) R ∩ {z | 0 < u z} :=
      hs.trans (ball_subset_closedBall.trans hsub)
    have hui := continuousOn_mul_integrable_support (isCompact_closedBall (0 : Space) R)
      hu (tfLaplacian_continuous hg)
      ((tfLaplacian_support hg).trans (hs'.trans (inter_subset_left.trans ball_subset_closedBall)))
    change 6*e*(∫ z, g z) ≤ ∫ z, (u z+e*(‖z‖^2-R^2))*Δ g z
    rw [quadratic_weak_pairing hg hcg hui]
    linarith only [hw g hg hcg hs' hn]

end Work_WeakPositiveComparison_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierTowerBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierSourceTower_barrier_scope

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators Topology

open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterKernel masterWidth scaledRealPacket

lemma outerCoefficient_measurable (R : ℝ) : Measurable (outerCoefficient R) :=
  Measurable.ite (measurableSet_le measurable_const continuous_norm.measurable)
    measurable_const measurable_const

lemma outerCoefficient_bound (R : ℝ) (x : TFSpace) : ‖outerCoefficient R x‖ ≤ 1 := by
  unfold outerCoefficient
  split_ifs <;> norm_num

lemma outerCoefficient_nonneg (R : ℝ) (x : TFSpace) : 0 ≤ outerCoefficient R x := by
  unfold outerCoefficient
  split_ifs <;> norm_num

lemma outerCoefficient_zero (R : ℝ) (x : TFSpace) (hx : ‖x‖ < R) :
    outerCoefficient R x = 0 := ite_eq_right (not_le_of_gt hx)

end Work_BarrierSourceTower_barrier_scope

open Set Filter Laplacian InnerProductSpace
open scoped Topology

open CoulombPDE

lemma outerBarrier_bounds {B r : ℝ} (hB : 0 ≤ B) (hr : 0 < r)
    {x : Space} (hx : r ≤ ‖x‖) :
    (7*B/8)/‖x‖^4 ≤ outerBarrier B r x ∧ outerBarrier B r x ≤ B/‖x‖^4 := by
  have hd : 0 < ‖x‖ := hr.trans_le hx
  have hq0 : 0 ≤ r/(8*‖x‖) := by positivity
  have hq1 : r/(8*‖x‖) ≤ 1/8 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hb : 0 ≤ B/‖x‖^4 := by positivity
  unfold outerBarrier
  constructor
  · calc
      _ = (B/‖x‖^4)*(7/8) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hb
  · calc
      _ ≤ (B/‖x‖^4)*1 := mul_le_mul_of_nonneg_left (by linarith) hb
      _ = _ := mul_one _

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierOuterWeakBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierOuterWeak_barrier_scope

open Set Filter MeasureTheory Laplacian Metric InnerProductSpace
open scoped Topology ContDiff

open CoulombAnalysis

lemma WeakNuclearLowerOn.congr_field {U : Set TFSpace} {Z : ℝ} {u v h : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn U Z u h) (he : ∀ x ∈ U, u x = v x) :
    WeakNuclearLowerOn U Z v h := by
  intro φ hφ hc hs hn
  calc
    _ ≤ ∫ x, u x*Δ φ x := hw φ hφ hc hs hn
    _ = _ := integral_congr_ae (ae_of_all _ fun x => by
      dsimp only
      by_cases hx : Δ φ x = 0
      · simp only [hx,mul_zero]
      · rw [he x (hs (tfLaplacian_support hφ hx))])

lemma WeakNuclearLowerOn.congr_source {U : Set TFSpace} {Z : ℝ} {u h h' : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn U Z u h) (he : ∀ x ∈ U, h x = h' x) :
    WeakNuclearLowerOn U Z u h' := by
  intro φ hφ hc hs hn
  have hh : (∫ x, h' x*φ x) = ∫ x, h x*φ x := by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : φ x = 0
    · simp only [hx,mul_zero]
    · rw [he x (hs (subset_tsupport φ hx))]
  rw [hh]
  exact hw φ hφ hc hs hn

end Work_BarrierOuterWeak_barrier_scope

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology ContDiff

open CoulombAnalysis

lemma nuclear_source_locallyIntegrable (Z k : ℝ) {r : ℝ} (hr : 0 < r)
    {g χ u : TFSpace → ℝ} (hg : LocallyIntegrable g) (hχ : Measurable χ)
    (hbχ : ∀ x, ‖χ x‖ ≤ 1) (hzero : ∀ x, ‖x‖ < r → χ x = 0)
    (hu : Continuous u) :
    LocallyIntegrable (fun x => g x+χ x*reaction k (nuclearField Z x+u x)) := by
  simp_rw [weighted_clipped_reaction Z r hzero]
  exact semilinear_source_locallyIntegrable hg hχ hbχ (reaction_continuous k)
    ((clippedNuclearField_continuous Z hr).add hu)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma innerSource_locallyIntegrable {μ p : TFSpace → ℝ}
    (hμ : LocallyIntegrable μ) (hp : LocallyIntegrable p) (R : ℝ) :
    LocallyIntegrable (innerSource R μ p) := by
  have hi := hμ.indicator (s := {x : TFSpace | ‖x‖ < R})
    (isOpen_lt continuous_norm continuous_const).measurableSet
  exact (hi.sub hp).smul (4*Real.pi)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierQuantitativeStepBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom CoulombAnalysis

theorem monotone_reaction_comparison_ball {u v L χ : TFSpace → ℝ}
    {f : ℝ → ℝ} {R c lam : ℝ} (hR : 0 < R) (hc : 0 ≤ c) (hlam : 0 ≤ lam)
    (hL : ∀ x, 0 ≤ L x) (hχ : ∀ x, 0 ≤ χ x) (hf : Monotone f)
    (hcont : ContinuousOn (fun x => u x-v x-L x) (closedBall 0 R))
    (hb : ∀ x : TFSpace, ‖x‖ = R → u x-v x-L x ≤ c)
    (hw : WeakLaplacianLowerOn (ball 0 R) (fun x => u x-v x-L x)
      (fun x => χ x*(f (u x)-f (v x-lam)))) :
    ∀ x ∈ closedBall (0 : TFSpace) R, u x-v x-L x ≤ c := by
  have hcmp := weak_subharmonic_positive_ball hR (hcont.sub continuousOn_const)
    (fun x hx => sub_nonpos.mpr (hb x hx)) (fun g hg hcg hs hn => ?_)
  · intro x hx
    exact sub_nonpos.mp (hcmp x hx)
  · have hs' : tsupport g ⊆ ball (0 : TFSpace) R := hs.trans inter_subset_left
    have hu := continuousOn_mul_integrable_support (isCompact_closedBall (0 : TFSpace) R)
      hcont (tfLaplacian_continuous hg)
      ((tfLaplacian_support hg).trans (hs'.trans ball_subset_closedBall))
    have hgi : Integrable (Δ g) :=
      (tfLaplacian_continuous hg).integrable_of_hasCompactSupport (tfLaplacian_compact hg hcg)
    have he : (∫ x, (u x-v x-L x-c)*Δ g x) = ∫ x, (u x-v x-L x)*Δ g x := by
      calc
        _ = ∫ x, (u x-v x-L x)*Δ g x-c*Δ g x := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by ring
        _ = _ := by
          rw [integral_sub hu (hgi.const_mul c),integral_const_mul,compact_laplacian_mass hg hcg,mul_zero,sub_zero]
    change 0 ≤ ∫ x, (u x-v x-L x-c)*Δ g x
    rw [he]
    apply le_trans _ (hw g hg hcg hs' hn)
    apply integral_nonneg
    intro x
    by_cases hx : g x = 0
    · simp only [hx,mul_zero,Pi.zero_apply,le_refl]
    · have hpos := (hs (subset_tsupport g hx)).2
      have hvu : v x-lam ≤ u x := by
        change 0 < u x-v x-L x-c at hpos
        linarith [hL x]
      exact mul_nonneg (mul_nonneg (hχ x) (sub_nonneg.mpr (hf hvu))) (hn x)

theorem WeakLaplacianLowerOn.add_bounded_L1_potential
    {U : Set TFSpace} {u h ρ : TFSpace → ℝ}
    (hu : LocallyIntegrable u) (hh : LocallyIntegrable h)
    (hw : WeakLaplacianLowerOn U u h) (hm : Measurable ρ) (hi : Integrable ρ)
    {M : ℝ} (hM : 0 ≤ M) (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M) (b : ℝ) :
    WeakLaplacianLowerOn U (fun x => u x+b*tfPotential ρ x)
      (fun x => h x-b*(4*Real.pi)*ρ x) := by
  intro g hg hcg hs hgn
  have hΔ := tfLaplacian_continuous hg
  have hcΔ := tfLaplacian_compact hg hcg
  have hui := locallyIntegrable_mul_test hu hΔ hcΔ
  have hhi := locallyIntegrable_mul_test hh hg.continuous hcg
  have hρi := locallyIntegrable_mul_test hi.locallyIntegrable hg.continuous hcg
  have hpi := locallyIntegrable_mul_test
    (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous.locallyIntegrable hΔ hcΔ
  have hleft : (∫ x, (h x-b*(4*Real.pi)*ρ x)*g x) =
      (∫ x, h x*g x)-b*(4*Real.pi)*(∫ x, ρ x*g x) := by
    calc
      _ = ∫ x, h x*g x-(b*(4*Real.pi))*(ρ x*g x) := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by ring
      _ = _ := by
        rw [integral_sub hhi (hρi.const_mul (b*(4*Real.pi))),integral_const_mul]
  have hright : (∫ x, (u x+b*tfPotential ρ x)*Δ g x) =
      (∫ x, u x*Δ g x)-b*(4*Real.pi)*(∫ x, ρ x*g x) := by
    simp_rw [add_mul,mul_assoc]
    rw [integral_add hui (hpi.const_mul b),integral_const_mul,
      bounded_L1_weak_poisson hm hi hM hn hb hg hcg]
    ring
  rw [hleft,hright]
  exact sub_le_sub_right (hw g hg hcg hs hgn) _

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierTransferPoissonBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

theorem barrier_transfer_weak {a ρ p q : TFSpace → ℝ} {Z k r S lam M P Q : ℝ}
    (hr : 0 < r) (ha : Continuous a)
    (hρm : Measurable ρ) (hρi : Integrable ρ) (hM : 0 ≤ M)
    (hρn : ∀ x, 0 ≤ ρ x) (hρb : ∀ x, ρ x ≤ M)
    (hpm : Measurable p) (hpi : Integrable p) (hP : 0 ≤ P)
    (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ P)
    (hqm : Measurable q) (hqi : Integrable q) (hQ : 0 ≤ Q)
    (hqn : ∀ x, 0 ≤ q x) (hqb : ∀ x, q x ≤ Q)
    (hw : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource r ρ p x+outerCoefficient r x*reaction k (nuclearField Z x+a x)))
    (hd : ∀ x ∈ ball (0 : TFSpace) S, r ≤ ‖x‖ →
      4*Real.pi*ρ x ≤ reaction k (nuclearField Z x-tfPotential ρ x-lam)+4*Real.pi*q x) :
    WeakLaplacianLowerOn (ball 0 S) (fun x => a x+tfPotential ρ x-tfPotential (fun y => p y+q y) x)
      (fun x => outerCoefficient r x*(reaction k (nuclearField Z x+a x)-
        reaction k (nuclearField Z x-tfPotential ρ x-lam))) := by
  let χ := outerCoefficient r
  let U : TFSpace → ℝ := fun x => nuclearField Z x+a x
  let F : TFSpace → ℝ := fun x => nuclearField Z x-tfPotential ρ x-lam
  let h : TFSpace → ℝ := fun x => innerSource r ρ p x+χ x*reaction k (U x)
  let e : TFSpace → ℝ := fun x => p x+q x
  have hem : Measurable e := hpm.add hqm
  have hei : Integrable e := hpi.add hqi
  have heN : ∀ x, 0 ≤ e x := fun x => add_nonneg (hpn x) (hqn x)
  have heB : ∀ x, e x ≤ P+Q := fun x => add_le_add (hpb x) (hqb x)
  have hePQ : 0 ≤ P+Q := add_nonneg hP hQ
  have hpot := (bounded_L1_potential_lipschitz hρm hρi hM hρn hρb).continuous
  have hhs : LocallyIntegrable h := nuclear_source_locallyIntegrable Z k hr
    (innerSource_locallyIntegrable hρi.locallyIntegrable hpi.locallyIntegrable r)
    (outerCoefficient_measurable r) (outerCoefficient_bound r) (outerCoefficient_zero r) ha
  have hzero : LocallyIntegrable (fun _ : TFSpace => (0 : ℝ)) := locallyIntegrable_zero
  have hUr : LocallyIntegrable (fun x => χ x*reaction k (U x)) := by
    simpa only [zero_add] using nuclear_source_locallyIntegrable Z k hr hzero
      (outerCoefficient_measurable r) (outerCoefficient_bound r) (outerCoefficient_zero r) ha
  have hFr : LocallyIntegrable (fun x => χ x*reaction k (F x)) := by
    have hfr₀ : LocallyIntegrable (fun x => χ x*reaction k
        (nuclearField Z x+(-tfPotential ρ x-lam))) := by
      simpa only [zero_add,Pi.sub_apply,Pi.neg_apply,χ] using nuclear_source_locallyIntegrable Z k hr hzero
        (outerCoefficient_measurable r) (outerCoefficient_bound r) (outerCoefficient_zero r)
        (hpot.neg.sub continuous_const)
    have heq : (fun x => χ x*reaction k (nuclearField Z x+(-tfPotential ρ x-lam))) =
        (fun x => χ x*reaction k (F x)) := by
      funext x
      congr 1
      dsimp only [F]
      congr 1
      ring
    rwa [heq] at hfr₀
  have htarget : LocallyIntegrable (fun x => χ x*(reaction k (U x)-reaction k (F x))) := by
    convert hUr.sub hFr using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp only [Pi.sub_apply,mul_sub]
  have hbase := (weakNuclearLower_add_iff Z ha.locallyIntegrable).mp hw
  have hw₁ := hbase.add_bounded_L1_potential ha.locallyIntegrable hhs hρm hρi hM hρn hρb 1
  have hu₁ : LocallyIntegrable (fun x => a x+1*tfPotential ρ x) :=
    (ha.add (continuous_const.mul hpot)).locallyIntegrable
  have hh₁ : LocallyIntegrable (fun x => h x-1*(4*Real.pi)*ρ x) :=
    hhs.sub (hρi.locallyIntegrable.smul (1*(4*Real.pi)))
  have hw₂ := hw₁.add_bounded_L1_potential hu₁ hh₁ hem hei hePQ heN heB (-1)
  have hh₂ : LocallyIntegrable (fun x => (h x-1*(4*Real.pi)*ρ x)-(-1)*(4*Real.pi)*e x) :=
    hh₁.sub (hei.locallyIntegrable.smul ((-1)*(4*Real.pi)))
  have hs := (hw₂.mono_set (subset_univ (ball (0 : TFSpace) S))).source_mono hh₂ htarget
    (fun x hx => ?_)
  · apply hs.congr_field
    intro x _
    simp only [one_mul,neg_one_mul]
    rfl
  · by_cases hxr : ‖x‖ < r
    · dsimp only [χ,h,e,innerSource,outerCoefficient]
      rw [ite_eq_left hxr,ite_eq_right (not_le_of_gt hxr)]
      nlinarith [Real.pi_pos,mul_nonneg Real.pi_pos.le (hqn x)]
    · have hc := hd x hx (le_of_not_gt hxr)
      dsimp only [χ,h,e,innerSource,outerCoefficient]
      rw [ite_eq_right hxr,ite_eq_left (le_of_not_gt hxr)]
      change 1*(reaction k (U x)-reaction k (F x)) ≤
        (4*Real.pi*(0-p x)+1*reaction k (U x)-1*(4*Real.pi)*ρ x)-(-1)*(4*Real.pi)*(p x+q x)
      change 4*Real.pi*ρ x ≤ reaction k (F x)+4*Real.pi*q x at hc
      linarith

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RotationShellBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology

namespace CoulombAtom

lemma rotation_integral_inverse {f : SpatialRotation → ℝ} (hf : Continuous f) :
    (∫ g, f g⁻¹ ∂rotationMeasure) = ∫ g, f g ∂rotationMeasure := by
  have hi : Integrable (fun q : SpatialRotation × SpatialRotation => f (q.1⁻¹*q.2))
      (rotationMeasure.prod rotationMeasure) :=
    (hf.comp (continuous_fst.inv.mul continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_univ (subset_univ _))
  have hx (x : SpatialRotation) : (∫ y, f (x⁻¹*y) ∂rotationMeasure) = ∫ y, f y ∂rotationMeasure :=
    rotation_integral_left f x⁻¹
  have hy (y : SpatialRotation) : (∫ x, f (x⁻¹*y) ∂rotationMeasure) = ∫ x, f x⁻¹ ∂rotationMeasure := by
    rw [←rotation_integral_left (fun x => f (x⁻¹*y)) y]
    simp only [mul_inv_rev,inv_mul_cancel_right]
  calc
    _ = ∫ y, ∫ x, f (x⁻¹*y) ∂rotationMeasure ∂rotationMeasure := by
      simp only [hy,integral_const,probReal_univ,smul_eq_mul,one_mul]
    _ = ∫ x, ∫ y, f (x⁻¹*y) ∂rotationMeasure ∂rotationMeasure := integral_integral_swap hi.swap
    _ = _ := by simp only [hx,integral_const,probReal_univ,smul_eq_mul,one_mul]

lemma rotate_inv_rotate (g : SpatialRotation) (p : Space) :
    rotate g⁻¹ (rotate g p) = p := by
  rw [←rotate_mul,inv_mul_cancel,rotate_one]

lemma rotate_kernel_inverse (g : SpatialRotation) (p z : Space) :
    ‖rotate g p-z‖ = ‖p-rotate g⁻¹ z‖ := by
  rw [←(rotate g⁻¹).norm_map (rotate g p-z),(rotate g⁻¹).map_sub,rotate_inv_rotate]

lemma rotation_kernel_inner (p z : Space) (hz : ‖z‖ < ‖p‖) :
    (∫ g : SpatialRotation, 1/‖rotate g p-z‖ ∂rotationMeasure) = 1/‖p‖ := by
  simp_rw [rotate_kernel_inverse]
  have hc : Continuous (fun g : SpatialRotation => rotate g z) :=
    continuous_subtype_val.clm_apply continuous_const
  have hn (g : SpatialRotation) : ‖p-rotate g z‖ ≠ 0 := by
    intro he
    have he' := sub_eq_zero.mp (norm_eq_zero.mp he)
    have hh : ‖p‖ = ‖z‖ := by rw [he',(rotate g).norm_map]
    linarith
  have hfi : Continuous (fun g : SpatialRotation => (1:ℝ)/‖p-rotate g z‖) :=
    continuous_const.div (continuous_const.sub hc).norm hn
  rw [rotation_integral_inverse hfi]
  exact rotation_kernel_newton z p hz

theorem rotation_kernel_shell (p z : Space) (h : ‖z‖ ≠ ‖p‖) :
    (∫ g : SpatialRotation, 1/‖rotate g p-z‖ ∂rotationMeasure) =
      1/max ‖p‖ ‖z‖ := by
  rcases lt_or_gt_of_ne h with hz | hz
  · rw [max_eq_left hz.le]
    exact rotation_kernel_inner p z hz
  · rw [max_eq_right hz.le]
    simp_rw [norm_sub_rev (rotate _ p) z]
    exact rotation_kernel_newton p z hz

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_SphericalMeanFieldBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma potential_rotation_integrable {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (p : Space) :
    Integrable (fun g : SpatialRotation => tfPotential ρ (rotate g p)) rotationMeasure :=
  ((bounded_L1_potential_lipschitz hm hi hM hn hb).continuous.comp
    (continuous_subtype_val.clm_apply continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_univ (subset_univ _))

lemma rotation_density_kernel_measurable {ρ : Space → ℝ}
    (hm : Measurable ρ) (p : Space) :
    Measurable (fun q : SpatialRotation × Space => ρ q.2/‖rotate q.1 p-q.2‖) := by
  have hg : Continuous (fun q : SpatialRotation × Space => rotate q.1 p) :=
    continuous_subtype_val.fst'.clm_apply continuous_const
  exact (hm.comp measurable_snd).div (hg.sub continuous_snd).norm.measurable

lemma rotation_density_kernel_normIntegral {ρ : Space → ℝ}
    (hn : ∀ z, 0 ≤ ρ z) (p : Space) (g : SpatialRotation) :
    (∫ z : Space, ‖ρ z/‖rotate g p-z‖‖) = tfPotential ρ (rotate g p) := by
  change (∫ z : Space, ‖ρ z/‖rotate g p-z‖‖) = ∫ z : Space, ρ z/‖rotate g p-z‖
  exact integral_congr_ae (ae_of_all _ (fun z => Real.norm_of_nonneg
    (div_nonneg (hn z) (norm_nonneg _))))

lemma rotation_density_kernel_integrable {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (p : Space) :
    Integrable (fun q : SpatialRotation × Space => ρ q.2/‖rotate q.1 p-q.2‖)
      (rotationMeasure.prod volume) := by
  refine (integrable_prod_iff (μ := rotationMeasure) (ν := volume)
    (rotation_density_kernel_measurable hm p).aestronglyMeasurable).mpr ⟨?_,?_⟩
  · exact ae_of_all _ (fun g => bounded_L1_potential_integrable hm hi hM hn hb (rotate g p))
  · have he : (fun g : SpatialRotation => ∫ z : Space, ‖ρ z/‖rotate g p-z‖‖) =
        fun g => tfPotential ρ (rotate g p) :=
      funext (rotation_density_kernel_normIntegral hn p)
    rw [he]
    exact potential_rotation_integrable hm hi hM hn hb p

theorem sphereMean_potential {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (p : Space) :
    sphereMean (tfPotential ρ) p = ∫ z, ρ z/max ‖p‖ ‖z‖ := by
  have hs : ∀ᵐ z : Space, ‖z‖ ≠ ‖p‖ := by
    apply ae_iff.mpr
    have he : {a : Space | ¬ ‖a‖ ≠ ‖p‖} = sphere (0:Space) ‖p‖ := by
      ext a
      simp only [mem_ofPred_eq,not_not,mem_sphere,dist_zero_right]
    rw [he]
    exact Measure.addHaar_sphere volume (0:Space) ‖p‖
  calc
    _ = ∫ g : SpatialRotation, ∫ z : Space, ρ z/‖rotate g p-z‖ ∂volume ∂rotationMeasure := rfl
    _ = ∫ z : Space, ∫ g : SpatialRotation, ρ z/‖rotate g p-z‖ ∂rotationMeasure :=
      integral_integral_swap (rotation_density_kernel_integrable hm hi hM hn hb p)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hs] with z hz
      rw [show (fun g : SpatialRotation => ρ z/‖rotate g p-z‖) =
        fun g => ρ z*(1/‖rotate g p-z‖) by funext g; ring,
        integral_const_mul,rotation_kernel_shell p z hz,mul_one_div]

lemma density_shell_integrable {ρ : Space → ℝ} (hm : Measurable ρ) (hi : Integrable ρ)
    (hn : ∀ z, 0 ≤ ρ z) {p : Space} (hp : p ≠ 0) :
    Integrable (fun z => ρ z/max ‖p‖ ‖z‖) := by
  apply (hi.div_const ‖p‖).mono' (hm.div (measurable_const.max measurable_norm)).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖ρ z/max ‖p‖ ‖z‖‖ ≤ ρ z/‖p‖
    rw [Real.norm_of_nonneg (div_nonneg (hn z) (le_max_of_le_left (norm_nonneg p)))]
    exact div_le_div_of_nonneg_left (hn z) (norm_pos_iff.mpr hp) (le_max_left _ _)

theorem sphereMean_field_bracket {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (Z : ℝ) {p : Space} (hp : p ≠ 0) :
    0 ≤ sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p-(Z-∫ z, ρ z)/‖p‖ ∧
    sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p-(Z-∫ z, ρ z)/‖p‖ ≤
      (∫ z in {z : Space | ‖p‖ < ‖z‖}, ρ z)/‖p‖ := by
  have hp0 := norm_pos_iff.mpr hp
  have hsh := density_shell_integrable hm hi hn hp
  have hrem := (hi.div_const ‖p‖).sub hsh
  have he : sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p-(Z-∫ z, ρ z)/‖p‖ =
      ∫ z, ρ z/‖p‖-ρ z/max ‖p‖ ‖z‖ := by
    have hf : sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p =
        Z/‖p‖-sphereMean (tfPotential ρ) p := by
      unfold sphereMean
      simp only [(rotate _).norm_map]
      rw [integral_sub (integrable_const _) (potential_rotation_integrable hm hi hM hn hb p)]
      simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    rw [hf,sphereMean_potential hm hi hM hn hb p,
      integral_sub (hi.div_const _) hsh,integral_div]
    ring
  rw [he]
  have hnrem (z : Space) : 0 ≤ ρ z/‖p‖-ρ z/max ‖p‖ ‖z‖ :=
    sub_nonneg.mpr (div_le_div_of_nonneg_left (hn z) hp0 (le_max_left _ _))
  refine ⟨integral_nonneg hnrem,?_⟩
  let T : Set Space := {z | ‖p‖ < ‖z‖}
  have hT : MeasurableSet T := measurableSet_lt measurable_const measurable_norm
  have ht := (hi.indicator hT).div_const ‖p‖
  have hbrem (z : Space) : ρ z/‖p‖-ρ z/max ‖p‖ ‖z‖ ≤ T.indicator ρ z/‖p‖ := by
    by_cases hz : z ∈ T
    · rw [indicator_of_mem hz]
      exact sub_le_self _ (div_nonneg (hn z) (le_max_of_le_left (norm_nonneg p)))
    · have hzr : ‖z‖ ≤ ‖p‖ := le_of_not_gt hz
      rw [indicator_of_notMem hz,max_eq_left hzr,sub_self,zero_div]
  calc
    _ ≤ ∫ z, T.indicator ρ z/‖p‖ := integral_mono hrem ht hbrem
    _ = _ := by rw [integral_div,integral_indicator hT]

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpOrdinaryCapBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma ae_off_norm_sphere (p : Space) : ∀ᵐ z : Space, ‖z‖ ≠ ‖p‖ := by
  apply ae_iff.mpr
  have he : {a : Space | ¬ ‖a‖ ≠ ‖p‖} = sphere (0:Space) ‖p‖ := by
    ext a
    simp only [mem_ofPred_eq,not_not,mem_sphere,dist_zero_right]
  rw [he]
  exact Measure.addHaar_sphere volume (0:Space) ‖p‖

lemma rotation_kernel_integrable_off_sphere (p z : Space) (hp : p ≠ 0)
    (hz : ‖z‖ ≠ ‖p‖) :
    Integrable (fun g : SpatialRotation => (1:ℝ)/‖rotate g p-z‖) rotationMeasure := by
  by_contra hn
  have he := rotation_kernel_shell p z hz
  rw [integral_undef hn] at he
  have hm : 0 < max ‖p‖ ‖z‖ := (norm_pos_iff.mpr hp).trans_le (le_max_left _ _)
  exact (ne_of_gt (one_div_pos.mpr hm)) he.symm

lemma L1_rotation_density_kernel_integrable {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {p : Space} (hp : p ≠ 0) :
    Integrable (fun q : SpatialRotation × Space => ρ q.2/‖rotate q.1 p-q.2‖)
      (rotationMeasure.prod volume) := by
  have hme : AEStronglyMeasurable
      (fun q : Space × SpatialRotation => ρ q.1/‖rotate q.2 p-q.1‖)
      (volume.prod rotationMeasure) :=
    ((rotation_density_kernel_measurable hm p).comp measurable_swap).aestronglyMeasurable
  have hh : Integrable (fun q : Space × SpatialRotation => ρ q.1/‖rotate q.2 p-q.1‖)
      (volume.prod rotationMeasure) := by
    apply (integrable_prod_iff hme).mpr
    constructor
    · filter_upwards [ae_off_norm_sphere p] with z hz
      simpa only [mul_one_div] using (rotation_kernel_integrable_off_sphere p z hp hz).const_mul (ρ z)
    · apply (density_shell_integrable hm hi hn hp).congr
      filter_upwards [ae_off_norm_sphere p] with z hz
      change ρ z/max ‖p‖ ‖z‖ = ∫ g : SpatialRotation, ‖ρ z/‖rotate g p-z‖‖ ∂rotationMeasure
      simp_rw [Real.norm_of_nonneg (div_nonneg (hn z) (norm_nonneg _))]
      simp_rw [show ∀ g : SpatialRotation, ρ z/‖rotate g p-z‖ =
        ρ z*((1:ℝ)/‖rotate g p-z‖) by intro g; ring]
      rw [integral_const_mul,rotation_kernel_shell p z hz,mul_one_div]
  exact hh.swap

lemma L1_potential_rotation_integrable {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {p : Space} (hp : p ≠ 0) :
    Integrable (fun g : SpatialRotation => tfPotential ρ (rotate g p)) rotationMeasure :=
  (L1_rotation_density_kernel_integrable hm hi hn hp).integral_prod_left

theorem L1_sphereMean_potential {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {p : Space} (hp : p ≠ 0) :
    sphereMean (tfPotential ρ) p = ∫ z, ρ z/max ‖p‖ ‖z‖ := by
  calc
    _ = ∫ g : SpatialRotation, ∫ z : Space, ρ z/‖rotate g p-z‖ ∂volume ∂rotationMeasure := rfl
    _ = ∫ z : Space, ∫ g : SpatialRotation, ρ z/‖rotate g p-z‖ ∂rotationMeasure :=
      integral_integral_swap (L1_rotation_density_kernel_integrable hm hi hn hp)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_off_norm_sphere p] with z hz
      rw [show (fun g : SpatialRotation => ρ z/‖rotate g p-z‖) =
        fun g => ρ z*(1/‖rotate g p-z‖) by funext g; ring,
        integral_const_mul,rotation_kernel_shell p z hz,mul_one_div]

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CorrectedFieldCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set Metric
open scoped Topology
noncomputable section
namespace CoulombAnalysis
open CoulombAtom

lemma finite_L1_tail_decay {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    {R : ι → ℝ} (hR : Tendsto R F atTop) {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hn : ∀ x, 0 ≤ ρ x) :
    Tendsto (fun i => ∫ x in {x : Space | R i < ‖x‖}, ρ x) F (𝓝 0) := by
  have hh := tendsto_integral_filter_of_dominated_convergence (l := F)
    (F := fun i => {x : Space | R i < ‖x‖}.indicator ρ) (f := fun _ : Space => (0:ℝ)) ρ
    (Eventually.of_forall (fun i => (hm.indicator (measurableSet_lt measurable_const measurable_norm)).aestronglyMeasurable))
    (Eventually.of_forall (fun i => ae_of_all _ (fun x => by
      by_cases hx : R i < ‖x‖
      · rw [indicator_of_mem (show x ∈ {x : Space | R i < ‖x‖} from hx), Real.norm_of_nonneg (hn x)]
      · rw [indicator_of_notMem (show x ∉ {x : Space | R i < ‖x‖} from hx),norm_zero]; exact hn x))) hi
    (ae_of_all _ (fun x => ?_))
  · simpa only [integral_indicator (measurableSet_lt measurable_const measurable_norm),integral_zero] using hh
  · apply tendsto_const_nhds.congr'
    filter_upwards [hR.eventually_ge_atTop ‖x‖] with i hi
    exact (indicator_of_notMem (show x ∉ {x : Space | R i < ‖x‖} from not_lt.mpr hi) ρ).symm

lemma potential_sphereMean_mass_le {e : Space → ℝ} (hm : Measurable e)
    (hi : Integrable e) (hn : ∀ x, 0 ≤ e x) {p : Space} (hp : p ≠ 0) :
    sphereMean (tfPotential e) p ≤ (∫ x, e x)/‖p‖ := by
  rw [L1_sphereMean_potential hm hi hn hp, ←integral_div]
  exact integral_mono (density_shell_integrable hm hi hn hp) (hi.div_const _) (fun z =>
    div_le_div_of_nonneg_left (hn z) (norm_pos_iff.mpr hp) (le_max_left _ _))

theorem corrected_field_charge {ρ e : Space → ℝ} {Z M r : ℝ}
    (hr : 0 < r) (hm : Measurable ρ) (hi : Integrable ρ) (hM : 0 ≤ M)
    (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M)
    (hem : Measurable e) (hei : Integrable e) (hen : ∀ x, 0 ≤ e x)
    (hfield : ∀ x, r ≤ ‖x‖ → 0 ≤ Z/‖x‖-tfPotential ρ x+tfPotential e x) :
    (∫ x, ρ x)-Z ≤ ∫ x, e x := by
  have hR : Tendsto (fun n : ℕ => (n:ℝ)+r+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_atTop_add_const_right atTop r tendsto_natCast_atTop_atTop)
  have hlim := (finite_L1_tail_decay hR hm hi hn).const_add (∫ x, e x)
  have hbound (R : ℝ) (hR : r ≤ R) :
      (∫ x, ρ x)-Z ≤ (∫ x, e x)+(∫ x in {x : Space | R < ‖x‖}, ρ x) := by
    have hRp : 0 < R := hr.trans_le hR
    obtain ⟨p,hpR⟩ := exists_norm_eq (E := Space) hRp.le
    have hp : p ≠ 0 := norm_pos_iff.mp (hpR ▸ hRp)
    have hf : Integrable (fun g : SpatialRotation => Z/‖rotate g p‖-tfPotential ρ (rotate g p)) rotationMeasure := by
      simp only [(rotate _).norm_map]
      exact (integrable_const _).sub (L1_potential_rotation_integrable hm hi hn hp)
    have hfe := hf.add (L1_potential_rotation_integrable hem hei hen hp)
    have hnon : 0 ≤ ∫ g : SpatialRotation, Z/‖rotate g p‖-tfPotential ρ (rotate g p)+tfPotential e (rotate g p) ∂rotationMeasure :=
      integral_nonneg (fun g : SpatialRotation =>
      hfield (rotate g p) (by simpa only [(rotate _).norm_map,hpR] using hR))
    rw [integral_add hf (L1_potential_rotation_integrable hem hei hen hp)] at hnon
    change 0 ≤ sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p+sphereMean (tfPotential e) p at hnon
    have hρ := (sphereMean_field_bracket hm hi hM hn hb Z hp).2
    have he := potential_sphereMean_mass_le hem hei hen hp
    rw [hpR] at hρ he
    have hh : ((∫ x, ρ x)-Z) / R ≤ ((∫ x, e x)+(∫ x in {x : Space | R < ‖x‖}, ρ x))/R := by
      rw [sub_div,add_div]
      rw [sub_div] at hρ
      linarith
    exact (div_le_div_iff_of_pos_right hRp).mp hh
  have hh := ge_of_tendsto hlim (Eventually.of_forall (fun n : ℕ => hbound ((n:ℝ)+r+1) (by linarith [show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n])))
  simpa only [add_zero] using hh
end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LaplacianCompDilation
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombPDE

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma laplacian_comp_dilation {f : E → ℝ} (a : ℝ) (x : E)
    (hf : ContDiffAt ℝ 2 f (a • x)) : Δ (fun y => f (a • y)) x = a^2 * Δ f (a • x) := by
  have hc : ContDiffAt ℝ 2 (fun y => f (a • y)) x := hf.comp x (contDiffAt_id.const_smul a)
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [← second_deriv_line hc]
  have he : (fun t : ℝ => f (a • (x + t • (stdOrthonormalBasis ℝ E) i))) =
      (fun t : ℝ => f (a • x + t • (a • (stdOrthonormalBasis ℝ E) i))) := by
    funext t
    simp only [smul_add, smul_smul, mul_comm]
  rw [he, second_deriv_line hf]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

end

open Filter Set Metric Topology InnerProductSpace Laplacian

lemma compare_subsolution_finite {d Z W : ℝ} {L G : Space → ℝ}
    (hd : 0 ≤ d) (hW : 0 < W) (hZW : Z < W) (hG : FiniteProfile d W G)
    (hreg : ∀ x, x ≠ 0 → ContDiffAt ℝ 2 L x)
    (hpde : ∀ x, x ≠ 0 → reaction d (L x) ≤ Δ L x)
    (hnear : ∃ C > 0, ∃ a > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ a → L x ≤ Z/‖x‖ + C)
    (hfar : ∀ ε > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → L x ≤ ε)
    (x : Space) (hx : x ≠ 0) : L x ≤ G x := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  let u : Space → ℝ := fun y => L y - (G y + δ)
  have hgd (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 (G + fun _ : Space => δ) y :=
    (hG.regular y hy).add contDiffAt_const
  have hud (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 u y := (hreg y hy).sub (hgd y hy)
  have hul (y : Space) (hy : y ≠ 0) (hp : 0 < u y) : 0 ≤ Δ u y := by
    have hlg : G y ≤ L y := by dsimp [u] at hp; linarith
    change 0 ≤ Δ (L - (G + fun _ : Space => δ)) y
    rw [(hreg y hy).laplacian_sub (hgd y hy),
      (hG.regular y hy).laplacian_add (show ContDiffAt ℝ 2 (fun _ : Space => δ) y from contDiffAt_const),
      laplacian_const, Pi.zero_apply, add_zero, hG.equation y hy]
    linarith [reaction_monotone hd hlg, hpde y hy]
  have hn : ∃ a > 0, ∀ y, y ≠ 0 → ‖y‖ ≤ a → u y ≤ 0 := by
    obtain ⟨C, hC, a, ha, hL⟩ := hnear
    obtain ⟨D, hD, b, hb, hG'⟩ := hG.nucleus
    refine ⟨min (min a b) ((W-Z)/(C+D+1)),
      lt_min (lt_min ha hb) (div_pos (sub_pos.mpr hZW) (by linarith)), ?_⟩
    intro y hy hr
    have hl := hL y hy (hr.trans ((min_le_left _ _).trans (min_le_left _ _)))
    have hg := (abs_le.mp (hG' y hy (hr.trans ((min_le_left _ _).trans (min_le_right _ _))))).1
    have hsmall := (le_div_iff₀ (show 0 < C+D+1 by linarith)).mp (hr.trans (min_le_right _ _))
    have hgap : C+D ≤ (W-Z)/‖y‖ := (le_div_iff₀ (norm_pos_iff.mpr hy)).mpr (by nlinarith [norm_nonneg y])
    rw [sub_div] at hgap
    dsimp [u]
    linarith
  have hf : ∃ R > 0, ∀ y, R ≤ ‖y‖ → u y ≤ 0 := by
    obtain ⟨R, hR, hb⟩ := hfar (δ/2) (by positivity)
    refine ⟨R, hR, fun y hy => ?_⟩
    have hz : y ≠ 0 := norm_pos_iff.mp (hR.trans_le hy)
    dsimp [u]
    linarith [hb y hy, hG.nonneg hW y hz]
  have hh := global_punctured_maximum_principle hud hul hn hf x hx
  dsimp [u] at hh
  linarith

lemma reaction_shiftedDilation {a : ℝ} (ha : 0 < a) (d v : ℝ) :
    reaction d (a^4*v + (1-a^4)) = a^6 * reaction d v := by
  unfold reaction
  rw [show a^4*v+(1-a^4)-1 = a^4*(v-1) by ring]
  rw [show max (a^4*(v-1)) 0 = a^4 * max (v-1) 0 by
    rw [mul_max_of_nonneg _ _ (pow_nonneg ha.le _), mul_zero]]
  rw [Real.mul_rpow (pow_nonneg ha.le _) (le_max_right _ _)]
  have hp : (a^4)^(3/2:ℝ) = a^6 := by
    rw [← Real.rpow_natCast a 4, ← Real.rpow_mul ha.le]
    norm_num
  rw [hp]
  ring

lemma FiniteProfile.shifted_dilation_regular {d Z : ℝ} {F : Space → ℝ}
    (hF : FiniteProfile d Z F) {a : ℝ} (ha : 0 < a) (x : Space) (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (shiftedDilation a F) x := by
  have hax : a • x ≠ 0 := smul_ne_zero ha.ne' hx
  exact (((hF.regular _ hax).comp x (contDiffAt_id.const_smul a)).const_smul (a^4)).add contDiffAt_const

lemma FiniteProfile.shifted_dilation_equation {d Z : ℝ} {F : Space → ℝ}
    (hF : FiniteProfile d Z F) {a : ℝ} (ha : 0 < a) (x : Space) (hx : x ≠ 0) :
    Δ (shiftedDilation a F) x = reaction d (shiftedDilation a F x) := by
  have hax : a • x ≠ 0 := smul_ne_zero ha.ne' hx
  have hc : ContDiffAt ℝ 2 (fun y : Space => F (a • y)) x :=
    (hF.regular _ hax).comp x (contDiffAt_id.const_smul a)
  have hs : Δ (fun y : Space => (a^4) • F (a • y)) x =
      (a^4) • Δ (fun y : Space => F (a • y)) x := laplacian_smul (a^4) hc
  change (Δ ((fun y : Space => (a^4) • F (a • y)) + (fun _ : Space => 1-a^4)) : Space → ℝ) x = _
  rw [(hc.const_smul (a^4)).laplacian_add
    (show ContDiffAt ℝ 2 (fun _ : Space => 1-a^4) x from contDiffAt_const),
    hs, laplacian_const, Pi.zero_apply, add_zero,
    laplacian_comp_dilation a x (hF.regular _ hax), hF.equation _ hax]
  rw [shiftedDilation, reaction_shiftedDilation ha]
  simp only [smul_eq_mul]
  ring

lemma FiniteProfile.shifted_dilation_near {d Z : ℝ} {F : Space → ℝ}
    (hF : FiniteProfile d Z F) {a : ℝ} (ha : 0 < a) :
    ∃ C > 0, ∃ b > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ b → shiftedDilation a F x ≤ a^3*Z/‖x‖ + C := by
  obtain ⟨C, hC, b, hb, hn⟩ := hF.nucleus
  refine ⟨a^4*C+2, by positivity, b/a, div_pos hb ha, ?_⟩
  intro x hx hxb
  have hnorm : ‖a • x‖ = a*‖x‖ := by rw [norm_smul, Real.norm_of_nonneg ha.le]
  have hax : a • x ≠ 0 := smul_ne_zero ha.ne' hx
  have htt : ‖a • x‖ ≤ b := by rw [hnorm]; nlinarith [(le_div_iff₀ ha).mp hxb]
  have hh := (abs_le.mp (hn _ hax htt)).2
  rw [hnorm] at hh
  have hi := mul_le_mul_of_nonneg_left hh (pow_nonneg ha.le 4)
  have he : a^4 * (Z/(a*‖x‖)) = a^3*Z/‖x‖ := by field_simp
  unfold shiftedDilation
  rw [mul_sub, he] at hi
  nlinarith [pow_nonneg ha.le 4]

lemma FiniteProfile.shifted_dilation_far {d Z : ℝ} {F : Space → ℝ}
    (hF : FiniteProfile d Z F) {a : ℝ} (ha : 1 ≤ a) :
    ∀ ε > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → shiftedDilation a F x ≤ ε := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  intro ε hε
  obtain ⟨R, hR, hb⟩ := hF.decay (ε/a^4) (by positivity)
  refine ⟨R/a, div_pos hR ha0, ?_⟩
  intro x hx
  have hh : R ≤ ‖a • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg ha0.le]
    nlinarith [(div_le_iff₀ ha0).mp hx]
  have hf := (abs_lt.mp (hb _ hh)).2
  have hg := (lt_div_iff₀ (pow_pos ha0 4)).mp hf
  have hp : 1 ≤ a^4 := one_le_pow₀ ha
  unfold shiftedDilation
  nlinarith

end CoulombPDE

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierTransferBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

theorem barrier_transfer_ball {a ρ p q : TFSpace → ℝ} {Z k r S lam M P Q c : ℝ}
    (hr : 0 < r) (hS : 0 < S) (hlam : 0 ≤ lam) (hk : 0 ≤ k) (hc : 0 ≤ c)
    (ha : Continuous a)
    (hρm : Measurable ρ) (hρi : Integrable ρ) (hM : 0 ≤ M)
    (hρn : ∀ x, 0 ≤ ρ x) (hρb : ∀ x, ρ x ≤ M)
    (hpm : Measurable p) (hpi : Integrable p) (hP : 0 ≤ P)
    (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ P)
    (hqm : Measurable q) (hqi : Integrable q) (hQ : 0 ≤ Q)
    (hqn : ∀ x, 0 ≤ q x) (hqb : ∀ x, q x ≤ Q)
    (hw : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource r ρ p x+outerCoefficient r x*reaction k (nuclearField Z x+a x)))
    (hd : ∀ x ∈ ball (0 : TFSpace) S, r ≤ ‖x‖ →
      4*Real.pi*ρ x ≤ reaction k (nuclearField Z x-tfPotential ρ x-lam)+4*Real.pi*q x)
    (hb : ∀ x : TFSpace, ‖x‖ = S → a x+tfPotential ρ x ≤ c) :
    ∀ x ∈ closedBall (0 : TFSpace) S,
      nuclearField Z x+a x ≤ nuclearField Z x-tfPotential ρ x+
        tfPotential (fun y => p y+q y) x+c := by
  let e : TFSpace → ℝ := fun x => p x+q x
  have hm : Measurable e := hpm.add hqm
  have hi : Integrable e := hpi.add hqi
  have hn : ∀ x, 0 ≤ e x := fun x => add_nonneg (hpn x) (hqn x)
  have hB : ∀ x, e x ≤ P+Q := fun x => add_le_add (hpb x) (hqb x)
  have heN (x : TFSpace) : 0 ≤ tfPotential e x := tfPotential_nonneg (ae_of_all _ hn) x
  have hp := (bounded_L1_potential_lipschitz hρm hρi hM hρn hρb).continuous
  have he := (bounded_L1_potential_lipschitz hm hi (add_nonneg hP hQ) hn hB).continuous
  have hcont : ContinuousOn (fun x => (nuclearField Z x+a x)-
      (nuclearField Z x-tfPotential ρ x)-tfPotential e x) (closedBall 0 S) := by
    convert ((ha.add hp).sub he).continuousOn using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp only [Pi.sub_apply,Pi.add_apply]
    ring
  have hw' : WeakLaplacianLowerOn (ball 0 S)
      (fun x => (nuclearField Z x+a x)-(nuclearField Z x-tfPotential ρ x)-tfPotential e x)
      (fun x => outerCoefficient r x*(reaction k (nuclearField Z x+a x)-
        reaction k (nuclearField Z x-tfPotential ρ x-lam))) := by
    apply (barrier_transfer_weak hr ha hρm hρi hM hρn hρb
      hpm hpi hP hpn hpb hqm hqi hQ hqn hqb hw hd).congr_field
    intro x _
    ring
  have hcmp := monotone_reaction_comparison_ball hS hc hlam heN
    (outerCoefficient_nonneg r) (reaction_monotone hk) hcont (fun x hx => ?_) hw'
  · intro x hx
    have hh := hcmp x hx
    dsimp only [e] at hh
    linarith
  · linarith [hb x hx,heN x]

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_NuclearDilationBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombPDE

lemma nuclearField_dilation {b : ℝ} (hb : 0 < b) (Z : ℝ) (x : TFSpace) :
    b^4*nuclearField Z (b • x) = nuclearField (b^3*Z) x := by
  simp only [nuclearField,norm_smul,Real.norm_of_nonneg hb.le]
  field_simp

lemma weakNuclearLower_dilation {b Z : ℝ} (hb : 0 < b) {u h : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn univ Z u h) :
    WeakNuclearLowerOn univ (b^3*Z) (fun x => b^4*u (b • x)) (tfDilation b h) := by
  intro φ hφ hc _ hn
  let ψ : TFSpace → ℝ := fun x => φ (b⁻¹ • x)
  have hψ : ContDiff ℝ 2 ψ := hφ.comp (contDiff_id.const_smul b⁻¹)
  have hcψ : HasCompactSupport ψ := hc.comp_smul (inv_ne_zero hb.ne')
  have hi := mul_le_mul_of_nonneg_left
    (hw ψ hψ hcψ (subset_univ _) (fun x => hn _)) (pow_nonneg hb.le 3)
  have heh : (∫ x, tfDilation b h x*φ x) = b^3*(∫ x, h x*ψ x) := by
    have he : (fun x => tfDilation b h x*φ x) =
        fun x => b^6*((fun y => h y*ψ y) (b • x)) := by
      funext x
      simp only [tfDilation,ψ,smul_smul,inv_mul_cancel₀ hb.ne',one_smul]
      ring
    rw [he,integral_const_mul,Measure.integral_comp_smul_of_nonneg volume
      (fun y => h y*ψ y) b (hR := hb.le)]
    rw [show Module.finrank ℝ TFSpace = 3 from space_finrank]
    simp only [smul_eq_mul]
    change b^6*((b^3)⁻¹*(∫ y, h y*ψ y)) = _
    field_simp
  have heu : (∫ x, b^4*u (b • x)*Δ φ x) = b^3*(∫ x, u x*Δ ψ x) := by
    have he : (fun x => u x*Δ ψ x) =
        fun x => (b⁻¹)^2*((fun y => u (b • y)*Δ φ y) (b⁻¹ • x)) := by
      funext x
      rw [show Δ ψ x = (b⁻¹)^2*Δ φ (b⁻¹ • x) from
        laplacian_comp_dilation b⁻¹ x hφ.contDiffAt]
      simp only [smul_smul,mul_inv_cancel₀ hb.ne',one_smul]
      ring
    rw [he,integral_const_mul,Measure.integral_comp_smul_of_nonneg volume
      (fun y => u (b • y)*Δ φ y) b⁻¹ (hR := (inv_pos.mpr hb).le)]
    have hel : (fun x => b^4*u (b • x)*Δ φ x) =
        fun x => b^4*(u (b • x)*Δ φ x) := by funext x; ring
    rw [hel,integral_const_mul]
    rw [show Module.finrank ℝ TFSpace = 3 from space_finrank]
    simp only [smul_eq_mul]
    change b^4*(∫ x, u (b • x)*Δ φ x) =
      b^3*((b⁻¹)^2*(((b⁻¹)^3)⁻¹*(∫ y, u (b • y)*Δ φ y)))
    field_simp
  rw [heh,heu]
  have hz : ψ 0 = φ 0 := by simp [ψ]
  rw [hz] at hi
  calc
    _ = b^3*(-(4*Real.pi*Z)*φ 0+(∫ x, h x*ψ x)) := by ring
    _ ≤ _ := hi

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierDilationBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierDilation_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma reaction_dilation {b : ℝ} (hb : 0 < b) (k t : ℝ) :
    reaction k (b^4*t) = b^6*reaction k t := by
  have hm : max (b^4*t) 0 = b^4*max t 0 := by
    rw [mul_max_of_nonneg _ _ (pow_nonneg hb.le 4),mul_zero]
  have hp : (b^4)^(3/2:ℝ) = b^6 := by
    rw [←Real.rpow_natCast b 4,←Real.rpow_mul hb.le]
    norm_num [Real.rpow_natCast]
  rw [reaction,hm,Real.mul_rpow (pow_nonneg hb.le 4) (le_max_right _ _),hp,reaction]
  ring

lemma innerSource_dilation {b : ℝ} (hb : 0 < b) (r : ℝ) (μ p : TFSpace → ℝ)
    (x : TFSpace) : tfDilation b (innerSource r μ p) x =
      innerSource (r/b) (tfDilation b μ) (tfDilation b p) x := by
  have he : ‖b • x‖ < r ↔ ‖x‖ < r/b := by
    rw [norm_smul,Real.norm_of_nonneg hb.le,lt_div_iff₀ hb,mul_comm]
  simp only [tfDilation,innerSource,he]
  split_ifs <;> ring

lemma outerCoefficient_dilation {b : ℝ} (hb : 0 < b) (r : ℝ) (x : TFSpace) :
    outerCoefficient r (b • x) = outerCoefficient (r/b) x := by
  have he : r ≤ ‖b • x‖ ↔ r/b ≤ ‖x‖ := by
    rw [norm_smul,Real.norm_of_nonneg hb.le,div_le_iff₀ hb,mul_comm]
  simp only [outerCoefficient,he]

lemma outerBarrier_dilation {b : ℝ} (hb : 0 < b) (B r : ℝ) (x : TFSpace) :
    b^4*outerBarrier B r (b • x) = outerBarrier B (r/b) x := by
  simp only [outerBarrier,norm_smul,Real.norm_of_nonneg hb.le]
  field_simp

theorem barrier_weak_dilation {b Z k r : ℝ} (hb : 0 < b)
    {a μ p : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource r μ p x+outerCoefficient r x*reaction k (nuclearField Z x+a x))) :
    WeakNuclearLowerOn univ (b^3*Z)
      (fun x => nuclearField (b^3*Z) x+b^4*a (b • x))
      (fun x => innerSource (r/b) (tfDilation b μ) (tfDilation b p) x+
        outerCoefficient (r/b) x*reaction k (nuclearField (b^3*Z) x+b^4*a (b • x))) := by
  have hh := weakNuclearLower_dilation hb hw
  have hf (x : TFSpace) : b^4*(nuclearField Z (b • x)+a (b • x)) =
      nuclearField (b^3*Z) x+b^4*a (b • x) := by
    rw [mul_add,nuclearField_dilation hb]
  apply (hh.congr_field (fun x _ => hf x)).congr_source
  intro x _
  change b^6*(innerSource r μ p (b • x)+
    outerCoefficient r (b • x)*reaction k (nuclearField Z (b • x)+a (b • x))) = _
  rw [mul_add,←show tfDilation b (innerSource r μ p) x = b^6*innerSource r μ p (b • x) from rfl,
    innerSource_dilation hb,outerCoefficient_dilation hb]
  rw [←hf, reaction_dilation hb]
  ring

end CoulombBarrier

end Work_BarrierDilation_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma local_coulomb_majorant {ρ : TFSpace → ℝ} {x : TFSpace} {b L : ℝ}
    (hb : 0 < b) (hn : ∀ z, 0 ≤ ρ z)
    (hlocal : ∀ z, ‖x-z‖ < b → ρ z ≤ L) (z : TFSpace) :
    ρ z/‖x-z‖ ≤ L*truncatedCoulomb b (x-z)+ρ z/b := by
  by_cases hz : ‖x-z‖ < b
  · rw [truncatedCoulomb,indicator_of_mem (mem_ball_zero_iff.mpr hz)]
    have hh := mul_le_mul_of_nonneg_right (hlocal z hz) (inv_nonneg.mpr (norm_nonneg (x-z)))
    simp only [div_eq_mul_inv,one_mul] at hh ⊢
    linarith [mul_nonneg (hn z) (inv_pos.mpr hb).le]
  · rw [truncatedCoulomb,indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hz),mul_zero,zero_add]
    exact div_le_div_of_nonneg_left (hn z) hb (le_of_not_gt hz)

lemma local_bounded_potential_integrable {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    (hi : Integrable ρ) {x : TFSpace} {b L : ℝ} (hb : 0 < b)
    (hn : ∀ z, 0 ≤ ρ z) (hlocal : ∀ z, ‖x-z‖ < b → ρ z ≤ L) :
    Integrable (fun z => ρ z/‖x-z‖) := by
  have hk : Integrable (fun z => truncatedCoulomb b (x-z)) :=
    (tfSubMap_preserving x).integrable_comp (truncatedCoulomb_integrable b).aestronglyMeasurable
      |>.mpr (truncatedCoulomb_integrable b)
  apply ((hk.const_mul L).add (hi.div_const b)).mono'
    (hm.div (measurable_const.sub measurable_id).norm).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖ρ z / ‖x-z‖‖ ≤ L*truncatedCoulomb b (x-z)+ρ z/b
    rw [Real.norm_of_nonneg (div_nonneg (hn z) (norm_nonneg _))]
    exact local_coulomb_majorant hb hn hlocal z

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CorrectionPotentialSmallBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom

lemma bounded_compact_mass_le {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    {L S : ℝ} (_hL : 0 ≤ L) (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ L)
    (hs : ∀ z, S < ‖z‖ → ρ z = 0) :
    Integrable ρ ∧ (∫ z, ρ z) ≤ volume.real (closedBall (0:TFSpace) S)*L := by
  have hmajor : ∀ z, ρ z ≤ (closedBall (0:TFSpace) S).indicator (fun _ => L) z := by
    intro z
    by_cases hz : ‖z‖ ≤ S
    · rw [indicator_of_mem (mem_closedBall_zero_iff.mpr hz)]
      exact hb z
    · rw [indicator_of_notMem (by simpa only [mem_closedBall_zero_iff] using hz),hs z (lt_of_not_ge hz)]
  have hI : Integrable ((closedBall (0:TFSpace) S).indicator (fun _ => L)) :=
    (integrableOn_const (C := L) measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
  have hρ : Integrable ρ := hI.mono' hm.aestronglyMeasurable (ae_of_all _ fun z => by
    simpa only [Real.norm_of_nonneg (hn z)] using hmajor z)
  refine ⟨hρ,(integral_mono hρ hI hmajor).trans_eq ?_⟩
  rw [integral_indicator measurableSet_closedBall,setIntegral_const,smul_eq_mul]

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom

lemma annularApproximationError_measurable (l a S : ℝ) :
    Measurable (annularApproximationError l a S) :=
  (measurable_const.div (measurable_norm.pow_const 6)).indicator
    ((measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const))

lemma annularApproximationError_nonneg (l a S : ℝ) (x : TFSpace) :
    0 ≤ annularApproximationError l a S x :=
  indicator_nonneg (fun _ _ => div_nonneg (by positivity) (by positivity)) _

lemma annularApproximationError_support (l a S : ℝ) (x : TFSpace) (hx : S < ‖x‖) :
    annularApproximationError l a S x = 0 :=
  indicator_of_notMem (fun h => (not_le.mpr hx) h.2) _

lemma annularApproximationError_bound {l a S : ℝ} (hl : 0 < l) (ha : 1/(2*l) ≤ a)
    (x : TFSpace) : annularApproximationError l a S x ≤ 64*l⁻¹^2 := by
  by_cases hx : a ≤ ‖x‖ ∧ ‖x‖ ≤ S
  · rw [annularApproximationError,indicator_of_mem (show x ∈ {x : TFSpace | a ≤ ‖x‖ ∧ ‖x‖ ≤ S} from hx)]
    have hnear : 0 < 1/(2*l) := by positivity
    calc
      _ ≤ l⁻¹^8/(1/(2*l))^6 := div_le_div_of_nonneg_left (by positivity)
        (pow_pos hnear 6) (pow_le_pow_left₀ hnear.le (ha.trans hx.1) 6)
      _ = _ := by field_simp [hl.ne']; ring
  · rw [annularApproximationError,indicator_of_notMem (show x ∉ {x : TFSpace | a ≤ ‖x‖ ∧ ‖x‖ ≤ S} from hx)]
    positivity

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_ScaledBarrierCorrectionBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfDilation_measurable {b : ℝ} {ρ : TFSpace → ℝ} (hm : Measurable ρ) :
    Measurable (tfDilation b ρ) :=
  measurable_const.mul (hm.comp (continuous_const_smul b).measurable)

lemma tfDilation_integrable {b : ℝ} (hb : 0 < b) {ρ : TFSpace → ℝ}
    (hi : Integrable ρ) : Integrable (tfDilation b ρ) :=
  (hi.comp_smul hb.ne').const_mul _

lemma tfDilation_nonneg {b : ℝ} {ρ : TFSpace → ℝ} (hn : ∀ x, 0 ≤ ρ x) :
    ∀ x, 0 ≤ tfDilation b ρ x := fun x => mul_nonneg (by positivity) (hn _)

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_SelectedBarrierTransferBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma scaled_barrier_eq {s : ℝ} (hs : 0 < s) (Z : ℝ)
    (a : TFSpace → ℝ) (x : TFSpace) :
    s^4*(nuclearField Z (s • x)+a (s • x)) =
      nuclearField (s^3*Z) x+s^4*a (s • x) := by
  rw [mul_add,nuclearField_dilation hs]

lemma scaled_barrier_lower {s r B Z : ℝ} (hs : 0 < s) {a : TFSpace → ℝ}
    (hlo : ∀ y, r ≤ ‖y‖ → outerBarrier B r y ≤ nuclearField Z y+a y) :
    ∀ x, r/s ≤ ‖x‖ → outerBarrier B (r/s) x ≤
      nuclearField (s^3*Z) x+s^4*a (s • x) := by
  intro x hx
  have hy : r ≤ ‖s • x‖ := by
    rw [norm_smul,Real.norm_of_nonneg hs.le]
    exact ((div_le_iff₀ hs).mp hx).trans_eq (mul_comm _ _)
  have ht := mul_le_mul_of_nonneg_left (hlo (s • x) hy) (pow_nonneg hs.le 4)
  rwa [outerBarrier_dilation hs,scaled_barrier_eq hs] at ht

lemma scaled_barrier_upper {s r C Z : ℝ} (hs : 0 < s) {a : TFSpace → ℝ}
    (hup : ∀ y, r ≤ ‖y‖ → nuclearField Z y+a y ≤ C/‖y‖^4) :
    ∀ x, r/s ≤ ‖x‖ → nuclearField (s^3*Z) x+s^4*a (s • x) ≤ C/‖x‖^4 := by
  intro x hx
  have hy : r ≤ ‖s • x‖ := by
    rw [norm_smul,Real.norm_of_nonneg hs.le]
    exact ((div_le_iff₀ hs).mp hx).trans_eq (mul_comm _ _)
  have ht := mul_le_mul_of_nonneg_left (hup (s • x) hy) (pow_nonneg hs.le 4)
  rw [scaled_barrier_eq hs] at ht
  have hh : s^4*(C/‖s • x‖^4) = C/‖x‖^4 := by
    rw [norm_smul,Real.norm_of_nonneg hs.le]
    field_simp
  exact ht.trans_eq hh

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FullSpectral
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom

instance fermionSpace_nontrivial (N : ℕ) : Nontrivial (fermionSpace N) := by
  obtain ⟨ψ, hψ⟩ := formDomain_nonempty N
  let x : fermionSpace N := fermionGraphValue N (admissibleGraph ψ hψ)
  have hx : x ≠ 0 := by
    intro hz
    have hn := admissibleGraph_norm ψ hψ
    change ‖x‖ ^ 2 = 1 at hn
    simp [hz] at hn
  exact ⟨⟨x, 0, hx⟩⟩

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfIncreasingData
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
namespace CoulombAnalysis
open CoulombAtom

lemma tfIncreasingField_monotone {r : ℝ} (hr : 0 < r) : Monotone (fun n => tfIncreasingField n r) := by
  intro n m hnm
  rcases hnm.eq_or_lt with h | h
  · subst h; rfl
  · have hh := ((tfIncreasingData n).finiteProfile (by positivity)).compare
      ((tfIncreasingData m).finiteProfile (by positivity)) tfReactionCoefficient_pos.le
      (show (n:ℝ)+1 < m+1 by exact_mod_cast Nat.add_lt_add_right h 1)
      (r • radialAxis) (TFUnitData.ray_ne_zero hr)
    rwa [← (tfIncreasingData n).radialField_ray (by positivity) hr,
      ← (tfIncreasingData m).radialField_ray (by positivity) hr] at hh

lemma tfIncreasingField_bounded {r : ℝ} (hr : 0 < r) :
    BddAbove (range (fun n => tfIncreasingField n r)) := by
  refine ⟨1 + CoulombPDE.sommerfeldCoefficient tfReactionCoefficient / r^4, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (tfIncreasingData n).radialField_upper (by positivity) hr

lemma tfIncreasingField_le {r : ℝ} (hr : 0 < r) (n : ℕ) :
    tfIncreasingField n r ≤ tfInfiniteRadial r := le_ciSup (tfIncreasingField_bounded hr) n

lemma tfInfiniteRadial_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ tfInfiniteRadial r :=
  ((tfIncreasingData 0).radialField_nonneg (by positivity) hr).trans (tfIncreasingField_le hr 0)

lemma tfIncreasingField_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => tfIncreasingField n r) atTop (𝓝 (tfInfiniteRadial r)) := by
  exact tendsto_atTop_ciSup (tfIncreasingField_monotone hr) (tfIncreasingField_bounded hr)

lemma tfInfiniteRadial_upper {r : ℝ} (hr : 0 < r) :
    tfInfiniteRadial r ≤ 1 + CoulombPDE.sommerfeldCoefficient tfReactionCoefficient / r^4 := by
  apply ciSup_le
  exact fun n => (tfIncreasingData n).radialField_upper (by positivity) hr

lemma tfInfiniteRadial_far_bound {a r : ℝ} (ha : 0 < a) (hr : a ≤ r) :
    tfInfiniteRadial r ≤ TFUnitData.chargeCap a / r := by
  apply ciSup_le
  exact fun n => (tfIncreasingData n).radialField_far_bound (by positivity) ha hr

lemma tfInfiniteRadial_lipschitz {a : ℝ} (ha : 0 < a) :
    LipschitzOnWith ⟨TFUnitData.slopeCap a, (TFUnitData.slopeCap_pos ha).le⟩ tfInfiniteRadial (Ici a) := by
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro x hx y hy
  apply le_of_tendsto ((tfIncreasingField_tendsto (ha.trans_le hx)).sub
    (tfIncreasingField_tendsto (ha.trans_le hy))).norm
  exact Eventually.of_forall fun n => ((tfIncreasingData n).lipschitz (by positivity) ha).norm_sub_le hx hy

lemma tfInfiniteRadial_continuous {r : ℝ} (hr : 0 < r) : ContinuousAt tfInfiniteRadial r := by
  apply (tfInfiniteRadial_lipschitz (show 0 < r/2 by positivity)).continuousOn.continuousAt
  exact Ici_mem_nhds (by linarith)

lemma positive_uIcc {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : t ∈ uIcc a b) : 0 < t :=
  (lt_min ha hb).trans_le ht.1

lemma positive_uIoc {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : t ∈ uIoc a b) : 0 < t :=
  (lt_min ha hb).trans ht.1

lemma tf_reaction_continuous : Continuous (CoulombPDE.reaction tfReactionCoefficient) := by
  unfold CoulombPDE.reaction
  exact continuous_const.mul (((continuous_id.sub continuous_const).max continuous_const).rpow_const
    (fun _ => Or.inr (by norm_num)))

lemma tf_reaction_nonneg (v : ℝ) : 0 ≤ CoulombPDE.reaction tfReactionCoefficient v := by
  unfold CoulombPDE.reaction
  exact mul_nonneg tfReactionCoefficient_pos.le (Real.rpow_nonneg (le_max_right _ _) _)

lemma tfFluxSource_continuous {r : ℝ} (hr : 0 < r) : ContinuousAt tfFluxSource r :=
  (continuousAt_id.pow 2).mul (tf_reaction_continuous.continuousAt.comp (tfInfiniteRadial_continuous hr))

lemma tfFiniteSource_continuous (n : ℕ) {r : ℝ} (hr : 0 < r) : ContinuousAt (tfFiniteSource n) r :=
  (continuousAt_id.pow 2).mul (tf_reaction_continuous.continuousAt.comp
    ((tfIncreasingData n).radialField_hasDerivAt hr).continuousAt)

lemma tfFluxSource_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable tfFluxSource volume a b :=
  (show ContinuousOn tfFluxSource (uIcc a b) from
    fun _ ht => (tfFluxSource_continuous (positive_uIcc ha hb ht)).continuousWithinAt).intervalIntegrable

lemma tfFiniteSource_intervalIntegrable (n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (tfFiniteSource n) volume a b :=
  (show ContinuousOn (tfFiniteSource n) (uIcc a b) from
    fun _ ht => (tfFiniteSource_continuous n (positive_uIcc ha hb ht)).continuousWithinAt).intervalIntegrable

lemma tfFiniteSource_integral_tendsto {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n => ∫ t in a..b, tfFiniteSource n t) atTop (𝓝 (∫ t in a..b, tfFluxSource t)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence tfFluxSource
  · exact Eventually.of_forall fun n =>
      (show ContinuousOn (tfFiniteSource n) (uIoc a b) from fun _ ht =>
        (tfFiniteSource_continuous n (positive_uIoc ha hb ht)).continuousWithinAt).aestronglyMeasurable measurableSet_Ioc
  · refine Eventually.of_forall fun n => Eventually.of_forall fun t ht => ?_
    rw [tfFiniteSource, Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (tf_reaction_nonneg _))]
    exact mul_le_mul_of_nonneg_left (CoulombPDE.reaction_monotone tfReactionCoefficient_pos.le
      (tfIncreasingField_le (positive_uIoc ha hb ht) n)) (sq_nonneg t)
  · exact tfFluxSource_intervalIntegrable ha hb
  · refine Eventually.of_forall fun t ht => ?_
    exact tendsto_const_nhds.mul (tf_reaction_continuous.continuousAt.tendsto.comp
      (tfIncreasingField_tendsto (positive_uIoc ha hb ht)))

lemma tfIncreasingCharge_integral (n : ℕ) {r : ℝ} (hr : 0 < r) :
    tfIncreasingCharge n r = tfIncreasingCharge n 1 - ∫ t in (1:ℝ)..r, tfFiniteSource n t := by
  have hd (t : ℝ) (ht : t ∈ uIcc (1:ℝ) r) :
      HasDerivAt (fun x => -tfIncreasingCharge n x) (tfFiniteSource n t) t := by
    convert ((tfIncreasingData n).charge_equation (positive_uIcc zero_lt_one hr ht) (by positivity)).neg using 1 <;> (try rfl)
    unfold tfFiniteSource tfIncreasingField
    ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (tfFiniteSource_intervalIntegrable n zero_lt_one hr)
  change (∫ t in (1:ℝ)..r, tfFiniteSource n t) = -(tfIncreasingCharge n r) - -(tfIncreasingCharge n 1) at hh
  linarith

lemma tfIncreasingCharge_subseq_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => tfIncreasingCharge (tfChargeAnchor.index n) r) atTop (𝓝 (tfInfiniteCharge r)) := by
  have hh := tfChargeAnchor.limit.sub
    ((tfFiniteSource_integral_tendsto zero_lt_one hr).comp tfChargeAnchor.strict.tendsto_atTop)
  exact hh.congr (fun n => (tfIncreasingCharge_integral _ hr).symm)

lemma tfInfiniteCharge_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt tfInfiniteCharge (-tfFluxSource r) r := by
  exact (intervalIntegral.integral_hasDerivAt_right (tfFluxSource_intervalIntegrable zero_lt_one hr)
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi (fun _ ht => tfFluxSource_continuous ht) r hr)
    (tfFluxSource_continuous hr)).const_sub _

lemma tfInfiniteSlope_continuous {r : ℝ} (hr : 0 < r) : ContinuousAt tfInfiniteSlope r :=
  (tfInfiniteCharge_hasDerivAt hr).continuousAt.neg.div (continuousAt_id.pow 2) (pow_ne_zero _ hr.ne')

lemma tfFiniteSlope_continuous (n : ℕ) {r : ℝ} (hr : 0 < r) : ContinuousAt (tfFiniteSlope n) r :=
  ((tfIncreasingData n).charge_hasDerivAt hr).continuousAt.neg.div (continuousAt_id.pow 2) (pow_ne_zero _ hr.ne')

lemma tfInfiniteSlope_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable tfInfiniteSlope volume a b :=
  (show ContinuousOn tfInfiniteSlope (uIcc a b) from
    fun _ ht => (tfInfiniteSlope_continuous (positive_uIcc ha hb ht)).continuousWithinAt).intervalIntegrable

lemma tfFiniteSlope_intervalIntegrable (n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (tfFiniteSlope n) volume a b :=
  (show ContinuousOn (tfFiniteSlope n) (uIcc a b) from
    fun _ ht => (tfFiniteSlope_continuous n (positive_uIcc ha hb ht)).continuousWithinAt).intervalIntegrable

lemma tfFiniteSlope_integral_subseq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n => ∫ t in a..b, tfFiniteSlope (tfChargeAnchor.index n) t) atTop
      (𝓝 (∫ t in a..b, tfInfiniteSlope t)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => TFUnitData.slopeCap (min a b))
  · exact Eventually.of_forall fun n =>
      (show ContinuousOn (tfFiniteSlope (tfChargeAnchor.index n)) (uIoc a b) from fun _ ht =>
        (tfFiniteSlope_continuous _ (positive_uIoc ha hb ht)).continuousWithinAt).aestronglyMeasurable measurableSet_Ioc
  · refine Eventually.of_forall fun n => Eventually.of_forall fun t ht => ?_
    have hh := (tfIncreasingData (tfChargeAnchor.index n)).deriv_bound (by positivity) (lt_min ha hb) ht.1.le
    rwa [((tfIncreasingData (tfChargeAnchor.index n)).radialField_hasDerivAt (positive_uIoc ha hb ht)).deriv] at hh
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun t ht => ?_
    exact (tfIncreasingCharge_subseq_tendsto (positive_uIoc ha hb ht)).neg.div tendsto_const_nhds
      (pow_ne_zero _ (positive_uIoc ha hb ht).ne')

lemma tfInfiniteRadial_integral {r : ℝ} (hr : 0 < r) :
    tfInfiniteRadial r = tfInfiniteRadial 1 + ∫ t in (1:ℝ)..r, tfInfiniteSlope t := by
  have hi (n : ℕ) : (∫ t in (1:ℝ)..r, tfFiniteSlope n t) = tfIncreasingField n r - tfIncreasingField n 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => (tfIncreasingData n).radialField_hasDerivAt (positive_uIcc zero_lt_one hr ht))
      (tfFiniteSlope_intervalIntegrable n zero_lt_one hr)
  have hl := ((tfIncreasingField_tendsto hr).sub (tfIncreasingField_tendsto zero_lt_one)).comp
    tfChargeAnchor.strict.tendsto_atTop
  have he := tendsto_nhds_unique (tfFiniteSlope_integral_subseq zero_lt_one hr)
    (hl.congr (fun n => (hi _).symm))
  linarith

lemma tfInfiniteRadial_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt tfInfiniteRadial (tfInfiniteSlope r) r := by
  have hh := (intervalIntegral.integral_hasDerivAt_right (tfInfiniteSlope_intervalIntegrable zero_lt_one hr)
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi (fun _ ht => tfInfiniteSlope_continuous ht) r hr)
    (tfInfiniteSlope_continuous hr)).const_add (tfInfiniteRadial 1)
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with t ht
  exact tfInfiniteRadial_integral ht

lemma tfInfiniteCharge_contDiffOn : ContDiffOn ℝ 1 tfInfiniteCharge (Ioi 0) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun r hr => (tfInfiniteCharge_hasDerivAt hr).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_zero]
  apply ContinuousOn.congr (f := fun r => -tfFluxSource r)
    (fun r hr => (tfFluxSource_continuous hr).neg.continuousWithinAt)
  exact fun r hr => (tfInfiniteCharge_hasDerivAt hr).deriv

lemma tfInfiniteRadial_contDiffOn : ContDiffOn ℝ 2 tfInfiniteRadial (Ioi 0) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun r hr => (tfInfiniteRadial_hasDerivAt hr).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  apply ContDiffOn.congr (f := tfInfiniteSlope)
    (tfInfiniteCharge_contDiffOn.neg.div (contDiffOn_id.pow 2) (fun r hr => pow_ne_zero _ hr.ne'))
  exact fun r hr => (tfInfiniteRadial_hasDerivAt hr).deriv

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfInfiniteField
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
namespace CoulombAnalysis

lemma tfInfinite_sqrt_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t => tfInfiniteRadial (Real.sqrt t))
      (-tfInfiniteCharge (Real.sqrt s) / (2 * (Real.sqrt s)^3)) s := by
  have hh := (tfInfiniteRadial_hasDerivAt (Real.sqrt_pos.mpr hs)).comp s (Real.hasDerivAt_sqrt hs.ne')
  convert hh using 1 <;> (try rfl)
  unfold tfInfiniteSlope
  field_simp [Real.sqrt_ne_zero'.mpr hs]

lemma tfInfinite_sqrt_second {s : ℝ} (hs : 0 < s) :
    deriv (deriv (fun t => tfInfiniteRadial (Real.sqrt t))) s =
      CoulombPDE.reaction tfReactionCoefficient (tfInfiniteRadial (Real.sqrt s)) / (4 * (Real.sqrt s)^2) +
        3 * tfInfiniteCharge (Real.sqrt s) / (4 * (Real.sqrt s)^5) := by
  have he : deriv (fun t => tfInfiniteRadial (Real.sqrt t)) =ᶠ[𝓝 s]
      fun t => -tfInfiniteCharge (Real.sqrt t) / (2 * (Real.sqrt t)^3) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact (tfInfinite_sqrt_hasDerivAt ht).deriv
  rw [he.deriv_eq]
  have hm := (tfInfiniteCharge_hasDerivAt (Real.sqrt_pos.mpr hs)).comp s (Real.hasDerivAt_sqrt hs.ne')
  have ht := ((Real.hasDerivAt_sqrt hs.ne').pow 3).const_mul 2
  have hh := hm.neg.div ht (by
    change 2 * Real.sqrt s ^ 3 ≠ 0
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (Real.sqrt_ne_zero'.mpr hs)))
  change HasDerivAt (fun t => -tfInfiniteCharge (Real.sqrt t) / (2 * (Real.sqrt t)^3)) _ s at hh
  rw [hh.deriv]
  simp only [Pi.pow_apply, Pi.neg_apply, Function.comp_apply, tfFluxSource]
  field_simp [Real.sqrt_ne_zero'.mpr hs]
  ring

lemma tfInfiniteField_classical {x : TFSpace} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 tfInfiniteField x ∧
      Δ tfInfiniteField x = CoulombPDE.reaction tfReactionCoefficient (tfInfiniteField x) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let g : ℝ → ℝ := fun s => tfInfiniteRadial (Real.sqrt s)
  have hg : ContDiffAt ℝ 2 g (‖x‖ ^ 2) := by
    have hrp := tfInfiniteRadial_contDiffOn.contDiffAt (Ioi_mem_nhds hn)
    have hrp' : ContDiffAt ℝ 2 tfInfiniteRadial (Real.sqrt (‖x‖ ^ 2)) := by
      rwa [Real.sqrt_sq (norm_nonneg x)]
    exact hrp'.comp (‖x‖ ^ 2) (Real.contDiffAt_sqrt (pow_ne_zero _ hn.ne'))
  have he : tfInfiniteField = (fun y : TFSpace => g (‖y‖ ^ 2)) := by
    funext y
    simp [tfInfiniteField, g, Real.sqrt_sq (norm_nonneg y)]
  have hfull : ContDiffAt ℝ 2 (fun y : TFSpace => g (‖y‖ ^ 2)) x :=
    ContDiffAt.comp (g := g) (f := fun y : TFSpace => ‖y‖ ^ 2) x hg (contDiff_norm_sq ℝ).contDiffAt
  refine ⟨he ▸ hfull, ?_⟩
  rw [he, CoulombPDE.laplacian_norm_sq_comp hg]
  dsimp only [g]
  rw [(tfInfinite_sqrt_hasDerivAt (sq_pos_of_pos hn)).deriv,
    tfInfinite_sqrt_second (sq_pos_of_pos hn), Real.sqrt_sq (norm_nonneg x)]
  have hdim : Module.finrank ℝ TFSpace = 3 := by simp [TFSpace]
  rw [hdim]
  norm_num only [Nat.cast_ofNat]
  field_simp [hn.ne']
  ring

lemma tfInfiniteField_decay : ∀ ε > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → |tfInfiniteField x| < ε := by
  intro ε hε
  refine ⟨max 1 (2 * TFUnitData.chargeCap 1 / ε), lt_max_of_lt_left zero_lt_one, ?_⟩
  intro x hx
  have h1 : 1 ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hn : 0 < ‖x‖ := zero_lt_one.trans_le h1
  change |tfInfiniteRadial ‖x‖| < ε
  rw [abs_of_nonneg (tfInfiniteRadial_nonneg hn)]
  apply (tfInfiniteRadial_far_bound zero_lt_one h1).trans_lt
  apply (div_lt_iff₀ hn).mpr
  have hh := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hx)
  have hc := TFUnitData.chargeCap_pos zero_lt_one
  nlinarith

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfInfiniteFieldDominatesDilation
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.fermionSpace_nontrivial _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian

lemma tfInfiniteField_dominates_dilation {a : ℝ} (ha : 1 ≤ a) (x : TFSpace) (hx : x ≠ 0) :
    CoulombPDE.shiftedDilation a (tfIncreasingData 0).field x ≤ tfInfiniteField x := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  obtain ⟨n, hn⟩ := exists_nat_gt (a^3)
  have hw : a^3 * ((0:ℝ)+1) < (n:ℝ)+1 := by nlinarith
  have hF := (tfIncreasingData 0).finiteProfile (by positivity)
  have hh := CoulombPDE.compare_subsolution_finite tfReactionCoefficient_pos.le (by positivity) hw
    ((tfIncreasingData n).finiteProfile (by positivity))
    (hF.shifted_dilation_regular ha0)
    (fun y hy => (hF.shifted_dilation_equation ha0 y hy).ge)
    (by simpa only [Nat.cast_zero] using hF.shifted_dilation_near ha0) (hF.shifted_dilation_far ha) x hx
  apply hh.trans
  rw [← (tfIncreasingData n).radialField_eq (by positivity) hx]
  exact tfIncreasingField_le (norm_pos_iff.mpr hx) n

lemma tf_first_field_large : ∃ (r₀ : ℝ), 0 < r₀ ∧ 2 ≤ (tfIncreasingData 0).field (r₀ • radialAxis) := by
  obtain ⟨C, hC, a, ha, hn⟩ := ((tfIncreasingData 0).finiteProfile (by positivity)).nucleus
  let r₀ := min a (1/(C+2))
  have hr : 0 < r₀ := lt_min ha (div_pos zero_lt_one (by linarith))
  refine ⟨r₀, hr, ?_⟩
  have hh := (abs_le.mp (hn (r₀ • radialAxis) (TFUnitData.ray_ne_zero hr)
    (by rw [TFUnitData.ray_norm hr]; exact min_le_left _ _))).1
  rw [TFUnitData.ray_norm hr] at hh
  have ht := (le_div_iff₀ (show 0 < C+2 by linarith)).mp (show r₀ ≤ 1/(C+2) from min_le_right _ _)
  have hi : C+2 ≤ 1/r₀ := (le_div_iff₀ hr).mpr (by nlinarith)
  norm_num at hh
  rw [one_div] at hi
  linarith

lemma tfInfiniteField_singular_lower : ∃ c > 0, ∃ R > 0,
    ∀ x, x ≠ 0 → ‖x‖ ≤ R → c * CoulombPDE.radialPower (-2) x ≤ tfInfiniteField x := by
  obtain ⟨r₀, hr, hb⟩ := tf_first_field_large
  refine ⟨r₀^4, pow_pos hr _, r₀, hr, ?_⟩
  intro x hx hxr
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let a := r₀/‖x‖
  have ha : 1 ≤ a := (one_le_div hn).mpr hxr
  have he : ‖a • x‖ = ‖r₀ • radialAxis‖ := by
    rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans ha), TFUnitData.ray_norm hr]
    exact div_mul_cancel₀ _ hn.ne'
  have hval := (tfIncreasingData 0).field_radial _ _ he
  have hc := tfInfiniteField_dominates_dilation ha x hx
  rw [CoulombPDE.shiftedDilation, hval] at hc
  have hp : a^4 ≤ tfInfiniteField x := by nlinarith [pow_nonneg (zero_le_one.trans ha) 4]
  have ht : a^4 = r₀^4 * CoulombPDE.radialPower (-2) x := by
    have hmul := CoulombPDE.norm_four_mul_radialPower hx
    dsimp [a]
    rw [div_pow, div_eq_iff (pow_ne_zero _ hn.ne')]
    calc
      r₀^4 = r₀^4 * (‖x‖^4 * CoulombPDE.radialPower (-2) x) := by rw [hmul, mul_one]
      _ = _ := by ring
  rwa [ht] at hp

theorem tfInfiniteField_singularProfile : CoulombPDE.SingularProfile tfReactionCoefficient tfInfiniteField := by
  refine ⟨fun _ hx => (tfInfiniteField_classical hx).1,
    fun _ hx => (tfInfiniteField_classical hx).2, tfInfiniteField_decay, ?_⟩
  obtain ⟨c, hc, R, hR, hl⟩ := tfInfiniteField_singular_lower
  let A := CoulombPDE.sommerfeldCoefficient tfReactionCoefficient
  have hA : 0 < A := CoulombPDE.sommerfeldCoefficient_pos tfReactionCoefficient_pos
  refine ⟨c, hc, A+1, by linarith, min R 1, lt_min hR zero_lt_one,
    fun x hx hr => hl x hx (hr.trans (min_le_left _ _)), ?_⟩
  intro x hx hr
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu := tfInfiniteRadial_upper hn
  have hmul := CoulombPDE.norm_four_mul_radialPower hx
  have hpow : ‖x‖^4 ≤ 1 := by
    exact pow_le_one₀ (norm_nonneg x) (hr.trans (min_le_right _ _))
  have hrp := CoulombPDE.radialPower_pos (-2) hx
  have hlow : 1 ≤ CoulombPDE.radialPower (-2) x := by nlinarith
  have he : A / ‖x‖^4 = A * CoulombPDE.radialPower (-2) x := by
    apply (div_eq_iff (pow_ne_zero _ hn.ne')).mpr
    nlinarith
  change tfInfiniteField x ≤ 1 + A / ‖x‖^4 at hu
  rw [he] at hu
  nlinarith


open MeasureTheory Filter Set Metric Topology
section
open CoulombAtom

lemma TFUnitData.exterior_field {Z r : ℝ} (D : TFUnitData Z) (hZ : 0 < Z)
    (hr : tfSupportRadius ≤ r) : D.radialField r = (Z-D.mass)/r := by
  have hr0 : 0 < r := (zero_lt_one.trans tfSupportRadius_gt_one).trans_le hr
  rw [D.radialField_ray hZ hr0, TFUnitData.field, tfField]
  rw [tfPotential_newton_exterior_closed D.admissible.2.1 (tfAdmissible_memLp D.admissible)
    D.radial (zero_lt_one.trans tfSupportRadius_gt_one)
    (fun y hy => le_of_not_gt (fun hh => hy (D.uniform_support hZ y hh.le)))
    (by rw [TFUnitData.ray_norm hr0]; exact hr)]
  rw [D.admissible.2.2.1, TFUnitData.ray_norm hr0, sub_div]

lemma TFUnitData.radialField_le_infinite {Z r : ℝ} (D : TFUnitData Z)
    (hZ : 0 < Z) (hr : 0 < r) : D.radialField r ≤ tfInfiniteRadial r := by
  obtain ⟨n, hn⟩ := exists_nat_gt Z
  have hh := (D.finiteProfile hZ).compare ((tfIncreasingData n).finiteProfile (by positivity))
    tfReactionCoefficient_pos.le (show Z < (n:ℝ)+1 by linarith)
    (r • radialAxis) (TFUnitData.ray_ne_zero hr)
  rw [← D.radialField_ray hZ hr, ← (tfIncreasingData n).radialField_ray (by positivity) hr] at hh
  exact hh.trans (tfIncreasingField_le hr n)

lemma tfRealRadial_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun Z => tfRealRadial Z r) atTop (𝓝 (tfInfiniteRadial r)) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨n, hn⟩ := (eventually_atTop.1 ((tendsto_order.1 (tfIncreasingField_tendsto hr)).1 a ha))
    filter_upwards [eventually_gt_atTop ((n:ℝ)+1)] with Z hZ
    have hZ0 : 0 < Z := (by positivity : (0:ℝ) < n+1).trans hZ
    rw [tfRealRadial, dite_eq_left hZ0]
    have hh := ((tfIncreasingData n).finiteProfile (by positivity)).compare
      ((tfUnitData Z hZ0).finiteProfile hZ0) tfReactionCoefficient_pos.le hZ
      (r • radialAxis) (TFUnitData.ray_ne_zero hr)
    rw [← (tfIncreasingData n).radialField_ray (by positivity) hr,
      ← (tfUnitData Z hZ0).radialField_ray hZ0 hr] at hh
    exact (hn n le_rfl).trans_le hh
  · intro a ha
    filter_upwards [eventually_gt_atTop (0:ℝ)] with Z hZ
    rw [tfRealRadial, dite_eq_left hZ]
    exact ((tfUnitData Z hZ).radialField_le_infinite hZ hr).trans_lt ha

lemma tfResidualCharge_pos : 0 < tfResidualCharge := by
  have hr := zero_lt_one.trans tfSupportRadius_gt_one
  have hp := tfInfiniteField_singularProfile.pos tfReactionCoefficient_pos
    (tfSupportRadius • radialAxis) (TFUnitData.ray_ne_zero hr)
  rw [tfInfiniteField, TFUnitData.ray_norm hr] at hp
  exact mul_pos hr hp

lemma TFUnitData.deficit_eq {Z : ℝ} (D : TFUnitData Z) (hZ : 0 < Z) :
    Z-D.mass = tfSupportRadius * D.radialField tfSupportRadius := by
  rw [D.exterior_field hZ le_rfl]
  exact (mul_div_cancel₀ _ (zero_lt_one.trans tfSupportRadius_gt_one).ne').symm

theorem tf_unit_deficit_tendsto : Tendsto tfUnitDeficit atTop (𝓝 tfResidualCharge) := by
  have ht := (tfRealRadial_tendsto (zero_lt_one.trans tfSupportRadius_gt_one)).const_mul tfSupportRadius
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with Z hZ
  rw [tfRealRadial, tfUnitDeficit, dite_eq_left hZ, dite_eq_left hZ]
  exact ((tfUnitData Z hZ).deficit_eq hZ).symm

lemma tfUnitDeficit_nonneg (Z : ℝ) : 0 ≤ tfUnitDeficit Z := by
  unfold tfUnitDeficit
  split_ifs with hZ
  · exact sub_nonneg.mpr ((tfUnitData Z hZ).mass_le_charge hZ)
  · exact le_rfl

lemma tfUnitDeficit_le (Z : ℝ) : tfUnitDeficit Z ≤ TFUnitData.chargeCap 1 := by
  by_cases hZ : 0 < Z
  · rw [tfUnitDeficit, dite_eq_left hZ, (tfUnitData Z hZ).deficit_eq hZ]
    have hh := (tfUnitData Z hZ).radialField_far_bound hZ (show (0:ℝ) < 1 by norm_num)
      tfSupportRadius_gt_one.le
    have hr := zero_lt_one.trans tfSupportRadius_gt_one
    calc
      _ ≤ tfSupportRadius * (TFUnitData.chargeCap 1 / tfSupportRadius) := mul_le_mul_of_nonneg_left hh hr.le
      _ = _ := mul_div_cancel₀ _ hr.ne'
  · rw [tfUnitDeficit, dite_eq_right hZ]
    exact (TFUnitData.chargeCap_pos (show (0:ℝ) < 1 by norm_num)).le

end

open MeasureTheory Filter Set Metric Topology

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_TFPriceData
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.fermionSpace_nontrivial _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
namespace CoulombAnalysis
open CoulombAtom

lemma tfPriceLength_three {μ : ℝ} (hμ : 0 < μ) : tfPriceLength μ ^ 3 = μ^(3/4:ℝ) := by
  rw [tfPriceLength, ← Real.rpow_natCast _ 3, ← Real.rpow_mul hμ.le]
  norm_num

lemma tfPriceData_mass {Z μ : ℝ} (hZ : 0 < Z) (hμ : 0 < μ) :
    (tfPriceData hZ hμ).mass = tfPriceLength μ ^ 3 *
      (tfUnitData (Z/tfPriceLength μ ^ 3) (div_pos hZ (pow_pos (tfPriceLength_pos hμ) _))).mass := by
  unfold tfPriceData
  rfl

lemma tfPriceData_deficit {Z μ : ℝ} (hZ : 0 < Z) (hμ : 0 < μ) :
    Z-(tfPriceData hZ hμ).mass = μ^(3/4:ℝ)*tfUnitDeficit (Z/μ^(3/4:ℝ)) := by
  calc
    Z-(tfPriceData hZ hμ).mass = tfPriceLength μ ^ 3 * tfUnitDeficit (Z/tfPriceLength μ ^ 3) := by
      rw [tfPriceData_mass, tfUnitDeficit,
        dite_eq_left (div_pos hZ (pow_pos (tfPriceLength_pos hμ) _)), mul_sub,
        mul_div_cancel₀ _ (pow_pos (tfPriceLength_pos hμ) 3).ne']
    _ = _ := by rw [tfPriceLength_three hμ]

lemma tfPriceData_deficit_bounds {Z μ : ℝ} (hZ : 0 < Z) (hμ : 0 < μ) :
    0 ≤ Z-(tfPriceData hZ hμ).mass ∧
      Z-(tfPriceData hZ hμ).mass ≤ TFUnitData.chargeCap 1 * μ^(3/4:ℝ) := by
  rw [tfPriceData_deficit hZ hμ]
  exact ⟨mul_nonneg (Real.rpow_nonneg hμ.le _) (tfUnitDeficit_nonneg _),
    by rw [mul_comm (TFUnitData.chargeCap 1)]; exact mul_le_mul_of_nonneg_left (tfUnitDeficit_le _) (Real.rpow_nonneg hμ.le (3/4:ℝ))⟩

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfBallFunctionalConvex
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.fermionSpace_nontrivial _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
section
open CoulombAtom

lemma tfBallFunctional_convex (R Z η : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ConvexOn ℝ univ (tfBallFunctional R T Z η) := by
  refine ⟨convex_univ, ?_⟩
  intro f _ g _ a b ha hb hab
  have hn : ‖a • f + b • g‖ ≤ a*‖f‖ + b*‖g‖ := by
    simpa only [norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb] using norm_add_le (a • f) (b • g)
  have hk := (Real.rpow_le_rpow (norm_nonneg _) hn (by norm_num : (0:ℝ) ≤ 5/3)).trans
    ((convexOn_rpow (by norm_num : (1:ℝ) ≤ 5/3)).2 (norm_nonneg f) (norm_nonneg g) ha hb hab)
  have hd := mul_nonneg (mul_nonneg ha hb) (tfCoulombL_nonneg R (f-g))
  have he : a * tfCoulombL R f f + b * tfCoulombL R g g -
      tfCoulombL R (a • f+b • g) (a • f+b • g) = a*b*tfCoulombL R (f-g) (f-g) := by
    simp only [map_smul, map_add, map_sub, smul_apply, add_apply, sub_apply, smul_eq_mul]
    rw [tfCoulombL_symmetric R g f]
    have := hab
    nlinarith [show (a+b-1)*tfCoulombL R f f = 0 by rw [hab]; ring,
      show (a+b-1)*tfCoulombL R g g = 0 by rw [hab]; ring]
  have hh := mul_le_mul_of_nonneg_left hk hT
  rw [← he] at hd
  unfold tfBallFunctional
  simp only [map_smul, map_add, smul_apply, add_apply, smul_eq_mul] at hd hh ⊢
  nlinarith

lemma tfAdmissible_extension {M R : ℝ} {ρ : TFSpace → ℝ} (hρ : TFAdmissible M ρ)
    (hs : ∀ x, R ≤ ‖x‖ → ρ x = 0) :
    ∃ f : TFLp (ballMeasure R), NonnegDensity f ∧ tfExtension R f =ᵐ[volume] ρ := by
  obtain ⟨f, hf, he⟩ := tfAdmissible_truncate hρ R
  refine ⟨f, hf, he.trans (Eventually.of_forall fun x => ?_)⟩
  by_cases hx : ‖x‖ < R
  · rw [indicator_of_mem (show x ∈ ball (0:TFSpace) R by simpa using hx)]
  · rw [indicator_of_notMem (show x ∉ ball (0:TFSpace) R by simpa using hx), hs x (le_of_not_gt hx)]

lemma tfExtension_add_smul (R : ℝ) (a b : ℝ) (f g : TFLp (ballMeasure R)) :
    tfExtension R (a • f+b • g) =ᵐ[volume] fun x => a*tfExtension R f x+b*tfExtension R g x := by
  have he := (Lp.coeFn_add (a • f) (b • g)).trans
    (((Lp.coeFn_smul a f).add (Lp.coeFn_smul b g)).mono fun _ h => h)
  have he' := (ae_restrict_iff' measurableSet_ball).mp he
  filter_upwards [he'] with x hx
  by_cases hxb : x ∈ ball (0:TFSpace) R
  · simpa only [tfExtension, indicator_of_mem hxb, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hx hxb
  · simp only [tfExtension, indicator_of_notMem hxb, mul_zero, add_zero]

lemma tf_compact_mix {M N : ℝ} {ρ σ : TFSpace → ℝ}
    (hρ : TFAdmissible M ρ) (hσ : TFAdmissible N σ)
    (hρs : ∃ R > 0, ∀ x, R ≤ ‖x‖ → ρ x = 0)
    (hσs : ∃ R > 0, ∀ x, R ≤ ‖x‖ → σ x = 0)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (Z : ℝ) :
    TFAdmissible (a*M+b*N) (fun x => a*ρ x+b*σ x) ∧
    tfFunctional Z (fun x => a*ρ x+b*σ x) ≤ a*tfFunctional Z ρ+b*tfFunctional Z σ := by
  obtain ⟨R, _hR, hRs⟩ := hρs
  obtain ⟨S, _hS, hSs⟩ := hσs
  obtain ⟨f, hf, hef⟩ := tfAdmissible_extension hρ (R := max R S)
    (fun x hx => hRs x ((le_max_left _ _).trans hx))
  obtain ⟨g, hg, heg⟩ := tfAdmissible_extension hσ (R := max R S)
    (fun x hx => hSs x ((le_max_right _ _).trans hx))
  have hn := nonnegDensity_add (nonnegDensity_smul hf ha) (nonnegDensity_smul hg hb)
  have hem : tfExtension (max R S) (a • f+b • g) =ᵐ[volume] (fun x => a*ρ x+b*σ x) := by
    filter_upwards [tfExtension_add_smul (max R S) a b f g, hef, heg] with x hm hx hy
    rw [hm, hx, hy]
  have hmass : (∫ x, tfExtension (max R S) (a • f+b • g) x) = a*M+b*N := by
    rw [integral_congr_ae hem, integral_add (hρ.2.1.const_mul a) (hσ.2.1.const_mul b),
      integral_const_mul, integral_const_mul, hρ.2.2.1, hσ.2.2.1]
  constructor
  · have hh := tfAdmissible_congr (tfExtension_admissible hn) hem
    rwa [hmass] at hh
  · have hh := (tfBallFunctional_convex (max R S) Z 0 tfKinetic_pos.le).2
      (mem_univ f) (mem_univ g) ha hb hab
    rw [← tfExtension_functional hn Z 0, ← tfExtension_functional hf Z 0,
      ← tfExtension_functional hg Z 0] at hh
    simpa only [zero_mul, add_zero, smul_eq_mul, tfFunctional_congr_ae Z hem,
      tfFunctional_congr_ae Z hef, tfFunctional_congr_ae Z heg] using hh

lemma tf_compact_mass_exists {M : ℝ} (hM : 0 ≤ M) :
    ∃ ρ : TFSpace → ℝ, TFAdmissible M ρ ∧
      (∃ R > 0, ∀ x, R ≤ ‖x‖ → ρ x = 0) := by
  let v : ℝ := (ballMeasure 1).real univ
  have hv : 0 < v := by
    apply ENNReal.toReal_pos
    · change (volume.restrict (ball (0:TFSpace) 1)) univ ≠ 0
      rw [Measure.restrict_apply_univ]
      exact ne_of_gt (isOpen_ball.measure_pos volume ⟨0, mem_ball_self (by norm_num)⟩)
    · exact ne_of_lt (measure_lt_top (ballMeasure 1) univ)
  let c := M/v
  have hc : 0 ≤ c := div_nonneg hM hv.le
  let hm : MemLp (fun _ : TFSpace => c) (5/3) (ballMeasure 1) := memLp_const c
  let f : TFLp (ballMeasure 1) := hm.toLp (fun _ => c)
  have hf : NonnegDensity f := hm.coeFn_toLp.mono (fun _ hx => hx ▸ hc)
  have he : tfExtension 1 f =ᵐ[volume] (ball (0:TFSpace) 1).indicator (fun _ => c) := by
    have hh := (ae_restrict_iff' measurableSet_ball).mp hm.coeFn_toLp
    filter_upwards [hh] with x hx
    by_cases hxb : x ∈ ball (0:TFSpace) 1
    · simpa only [tfExtension, indicator_of_mem hxb] using hx hxb
    · simp only [tfExtension, indicator_of_notMem hxb]
  have hvint : (∫ x, tfExtension 1 f x) = M := by
    rw [integral_congr_ae he, integral_indicator measurableSet_ball, integral_const]
    change v*c = M
    exact mul_div_cancel₀ _ hv.ne'
  refine ⟨tfExtension 1 f, ?_, 1, by norm_num, fun x hx => ?_⟩
  · have hh := tfExtension_admissible hf
    rwa [hvint] at hh
  · exact indicator_of_notMem (show x ∉ ball (0:TFSpace) 1 by simpa using not_lt.mpr hx) f

end

open MeasureTheory Filter Set Metric Topology
section
open CoulombAtom

lemma tfEnergy_class_nonempty {M : ℝ} (hM : 0 ≤ M) (Z : ℝ) :
    {e | ∃ ρ, TFAdmissible M ρ ∧ tfFunctional Z ρ = e}.Nonempty := by
  obtain ⟨ρ, hρ, _⟩ := tf_compact_mass_exists hM
  exact ⟨_, ρ, hρ, rfl⟩

lemma tfEnergy_class_bddBelow {Z : ℝ} (hZ : 0 < Z) (M : ℝ) :
    BddBelow {e | ∃ ρ, TFAdmissible M ρ ∧ tfFunctional Z ρ = e} := by
  let D := tfUnitData Z hZ
  refine ⟨tfFunctional Z D.density + D.mass - M, ?_⟩
  rintro e ⟨ρ, hρ, rfl⟩
  have hh := D.minimal M ρ hρ
  linarith

lemma tfEnergy_le_trial {Z M : ℝ} (hZ : 0 < Z) {ρ : TFSpace → ℝ}
    (hρ : TFAdmissible M ρ) : tfEnergy Z M ≤ tfFunctional Z ρ :=
  csInf_le (tfEnergy_class_bddBelow hZ M) ⟨ρ, hρ, rfl⟩

lemma tfPriceDeficit_eq {Z μ : ℝ} (hZ : 0 < Z) (hμ : 0 < μ) :
    tfPriceDeficit Z μ = Z-(tfPriceData hZ hμ).mass :=
  (tfPriceData_deficit hZ hμ).symm

lemma tfPriceValue_eq {Z μ : ℝ} (hZ : 0 < Z) (hμ : 0 < μ) :
    tfPriceValue Z μ = tfFunctional Z (tfPriceData hZ hμ).density - μ*tfPriceDeficit Z μ := by
  rw [tfPriceValue, dite_eq_left hZ, dite_eq_left hμ, tfPriceDeficit_eq hZ hμ]; ring

lemma tfPriceValue_le_trial {Z μ M : ℝ} (hZ : 0 < Z) (hμ : 0 < μ)
    {ρ : TFSpace → ℝ} (hρ : TFAdmissible M ρ) :
    tfPriceValue Z μ ≤ tfFunctional Z ρ + μ*(M-Z) := by
  have hh := (tfPriceData hZ hμ).minimal M ρ hρ
  rw [tfPriceValue_eq hZ hμ, tfPriceDeficit_eq hZ hμ]
  linarith

lemma tfPriceValue_le_energy {Z μ M : ℝ} (hZ : 0 < Z) (hμ : 0 < μ) (hM : 0 ≤ M) :
    tfPriceValue Z μ ≤ tfEnergy Z M + μ*(M-Z) := by
  have hh : tfPriceValue Z μ - μ*(M-Z) ≤ tfEnergy Z M := by
    apply le_csInf (tfEnergy_class_nonempty hM Z)
    rintro e ⟨ρ, hρ, rfl⟩
    linarith [tfPriceValue_le_trial hZ hμ hρ]
  linarith

lemma tfPriceValue_secant {Z μ ν : ℝ} (hZ : 0 < Z) (hμ : 0 < μ) (hν : 0 < ν) :
    tfPriceValue Z μ ≤ tfPriceValue Z ν - (μ-ν)*tfPriceDeficit Z ν := by
  have hh := tfPriceValue_le_trial hZ hμ (tfPriceData hZ hν).admissible
  rw [tfPriceValue_eq hZ hν, tfPriceDeficit_eq hZ hν]
  linarith

lemma tfPriceDeficit_zero_tendsto {Z : ℝ} (hZ : 0 < Z) :
    Tendsto (tfPriceDeficit Z) (𝓝[>] 0) (𝓝 0) := by
  have hc : Tendsto (fun μ : ℝ => TFUnitData.chargeCap 1 * μ^(3/4:ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have hk : Continuous (fun μ : ℝ => TFUnitData.chargeCap 1 * μ^(3/4:ℝ)) :=
      continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr (by norm_num)))
    have hh : Tendsto (fun μ : ℝ => TFUnitData.chargeCap 1 * μ^(3/4:ℝ))
        (𝓝[>] 0) (𝓝 (TFUnitData.chargeCap 1 * (0:ℝ)^(3/4:ℝ))) :=
      hk.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using hh
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with μ hμ
    rw [tfPriceDeficit_eq hZ hμ]
    exact (tfPriceData_deficit_bounds hZ hμ).1
  · filter_upwards [self_mem_nhdsWithin] with μ hμ
    rw [tfPriceDeficit_eq hZ hμ]
    exact (tfPriceData_deficit_bounds hZ hμ).2

lemma tfPriceValue_zero_tendsto {Z : ℝ} (hZ : 0 < Z) :
    Tendsto (tfPriceValue Z) (𝓝[>] 0) (𝓝 (tfEnergy Z Z)) := by
  obtain ⟨σ, hσ, hσs⟩ := tf_compact_mass_exists (by linarith : 0 ≤ 2*Z)
  let B := tfFunctional Z σ
  have hlower (μ : ℝ) (hμ : 0 < μ) :
      tfEnergy Z Z - (tfPriceDeficit Z μ / Z)*(B-tfEnergy Z Z) - μ*tfPriceDeficit Z μ ≤ tfPriceValue Z μ := by
    let P := tfPriceData hZ hμ
    let d := tfPriceDeficit Z μ
    have hd : 0 ≤ d := by dsimp [d]; rw [tfPriceDeficit_eq hZ hμ]; exact (tfPriceData_deficit_bounds hZ hμ).1
    have he : P.mass = Z-d := by dsimp [P, d]; rw [tfPriceDeficit_eq hZ hμ]; ring
    have hp : 0 < Z+d := by linarith
    let a := Z/(Z+d)
    let b := d/(Z+d)
    have hab : a+b=1 := by dsimp [a,b]; rw [← add_div, div_self hp.ne']
    have hm : a*P.mass+b*(2*Z)=Z := by rw [he]; dsimp [a,b]; field_simp; ring
    obtain ⟨hmix, hmixE⟩ := tf_compact_mix P.admissible hσ P.compact hσs
      (div_nonneg hZ.le hp.le) (div_nonneg hd hp.le) hab Z
    rw [hm] at hmix
    have hle := (tfEnergy_le_trial hZ hmix).trans hmixE
    have heF : tfFunctional Z P.density = tfPriceValue Z μ + μ*d := by
      rw [tfPriceValue_eq hZ hμ]; dsimp [P, d]; ring
    rw [heF] at hle
    have hle' := mul_le_mul_of_nonneg_left hle hp.le
    have hea : (Z+d)*a=Z := by dsimp [a]; exact mul_div_cancel₀ _ hp.ne'
    have heb : (Z+d)*b=d := by dsimp [b]; exact mul_div_cancel₀ _ hp.ne'
    rw [mul_add, ← mul_assoc, ← mul_assoc, hea, heb] at hle'
    change tfEnergy Z Z - (d/Z)*(B-tfEnergy Z Z)-μ*d ≤ tfPriceValue Z μ
    apply (mul_le_mul_iff_right₀ hZ).mp
    calc
      _ = (Z+d)*tfEnergy Z Z-d*B-Z*μ*d := by field_simp; ring
      _ ≤ Z * tfPriceValue Z μ := by dsimp [B]; nlinarith [hle']
  have hd := tfPriceDeficit_zero_tendsto hZ
  have hμ : Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hl : Tendsto (fun μ => tfEnergy Z Z - (tfPriceDeficit Z μ/Z)*(B-tfEnergy Z Z) - μ*tfPriceDeficit Z μ)
      (𝓝[>] 0) (𝓝 (tfEnergy Z Z)) := by
    simpa using (tendsto_const_nhds.sub ((hd.div_const Z).mul_const (B-tfEnergy Z Z))).sub (hμ.mul hd)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with μ hμ
    exact hlower μ hμ
  · filter_upwards [self_mem_nhdsWithin] with μ hμ
    simpa using tfPriceValue_le_energy hZ hμ hZ.le

lemma tfPriceValue_zero_bounds {Z μ : ℝ} (hZ : 0 < Z) (hμ : 0 < μ) :
    -μ*tfPriceDeficit Z μ ≤ tfPriceValue Z μ-tfEnergy Z Z ∧
      tfPriceValue Z μ-tfEnergy Z Z ≤ 0 := by
  have hh : tfEnergy Z Z ≤ tfPriceValue Z μ + μ*tfPriceDeficit Z μ := by
    apply le_of_tendsto (tfPriceValue_zero_tendsto hZ)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hμ)] with ν hν hνμ
    change 0 < ν at hν
    have hs := tfPriceValue_secant hZ hν hμ
    have hd := (tfPriceData_deficit_bounds hZ hμ).1
    rw [← tfPriceDeficit_eq hZ hμ] at hd
    nlinarith
  exact ⟨by linarith, by have := tfPriceValue_le_energy hZ hμ hZ.le; linarith⟩

end

open Filter
open scoped Topology

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_GridIncrementError
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
namespace CoulombAnalysis
open CoulombAtom

private theorem grid_increment_error {G d P D : ℝ → ℝ}
    (hG : DeficitSecants G d) (hP : DeficitSecants P D)
    {a h η : ℝ} (ha : 0 < a) (hh : 0 < h) {N : ℕ}
    (hclose : ∀ i ≤ N, |d (a + i * h) - D (a + i * h)| ≤ η) :
    |(G (a + N * h) - G a) - (P (a + N * h) - P a)| ≤
      h * (D (a + N * h) - D a) + N * h * η := by
  have hind : ∀ i ≤ N,
      |(G (a + i * h) - G a) - (P (a + i * h) - P a)| ≤
        h * (D (a + i * h) - D a) + i * h * η := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have hiN : i ≤ N := Nat.le_trans (Nat.le_succ i) hi
      have hix : 0 < a + i * h := by positivity
      have hxy : a + i * h < a + (i + 1 : ℕ) * h := by
        push_cast
        nlinarith
      have hsG := hG (a + i * h) (a + (i + 1 : ℕ) * h) hix hxy
      have hsP := hP (a + i * h) (a + (i + 1 : ℕ) * h) hix hxy
      have hcl := (abs_le.mp (hclose i hiN))
      have hcr := (abs_le.mp (hclose (i + 1) hi))
      have hcl' := mul_le_mul_of_nonneg_left hcl.1 hh.le
      have hcr' := mul_le_mul_of_nonneg_left hcr.2 hh.le
      have heq : a + (i + 1 : ℕ) * h - (a + i * h) = h := by
        push_cast
        ring
      rw [heq] at hsG hsP
      have hstep : |(G (a + (i + 1 : ℕ) * h) - G (a + i * h)) -
          (P (a + (i + 1 : ℕ) * h) - P (a + i * h))| ≤
          h * (D (a + (i + 1 : ℕ) * h) - D (a + i * h)) + h * η := by
        apply abs_le.mpr
        constructor <;> nlinarith [hsG.1, hsG.2, hsP.1, hsP.2]
      have htel : (G (a + (i + 1 : ℕ) * h) - G a) -
          (P (a + (i + 1 : ℕ) * h) - P a) =
          ((G (a + i * h) - G a) - (P (a + i * h) - P a)) +
          ((G (a + (i + 1 : ℕ) * h) - G (a + i * h)) -
          (P (a + (i + 1 : ℕ) * h) - P (a + i * h))) := by ring
      rw [htel]
      calc
        _ ≤ |(G (a + i * h) - G a) - (P (a + i * h) - P a)| +
            |(G (a + (i + 1 : ℕ) * h) - G (a + i * h)) -
            (P (a + (i + 1 : ℕ) * h) - P (a + i * h))| := abs_add_le _ _
        _ ≤ (h * (D (a + i * h) - D a) + i * h * η) +
            (h * (D (a + (i + 1 : ℕ) * h) - D (a + i * h)) + h * η) :=
          add_le_add (ih hiN) hstep
        _ = _ := by push_cast; ring
  exact hind N le_rfl

theorem deficit_secant_increments_tendsto_filter {ι : Type*} {l : Filter ι} {G d : ι → ℝ → ℝ} {P D : ℝ → ℝ}
    (hG : ∀ n, DeficitSecants (G n) (d n)) (hP : DeficitSecants P D)
    (hd : ∀ t : ℝ, 0 < t → Tendsto (fun n => d n t) l (𝓝 (D t)))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun n => G n b - G n a) l (𝓝 (P b - P a)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (2 * ((b - a) * (D b - D a)) / ε))
  have hN1 : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNpos : (0 : ℝ) < N := lt_trans zero_lt_one hN1
  have hwidth : 0 < b - a := sub_pos.mpr hab
  let h : ℝ := (b - a) / N
  let η : ℝ := ε / (2 * (b - a))
  have hh : 0 < h := div_pos hwidth hNpos
  have hη : 0 < η := div_pos hε (by positivity)
  have hxN : a + N * h = b := by dsimp [h]; field_simp; ring
  have hmesh : h * (D b - D a) < ε / 2 := by
    have hnr : 2 * ((b - a) * (D b - D a)) / ε < N :=
      (le_max_right _ _).trans_lt hN
    have hnr' := (div_lt_iff₀ hε).mp hnr
    dsimp [h]
    rw [div_mul_eq_mul_div]
    apply (div_lt_div_iff₀ hNpos (show (0 : ℝ) < 2 by norm_num)).mpr
    nlinarith
  have hηeq : (N : ℝ) * h * η = ε / 2 := by
    dsimp [h, η]
    field_simp
  have hev : ∀ i : Fin (N + 1), ∀ᶠ n in l,
      |d n (a + (i : ℕ) * h) - D (a + (i : ℕ) * h)| ≤ η := by
    intro i
    have hxi : 0 < a + (i : ℕ) * h := by positivity
    exact ((Metric.tendsto_nhds.mp (hd _ hxi)) η hη).mono fun n hn =>
      le_of_lt (by simpa only [Real.dist_eq] using hn)
  filter_upwards [Filter.eventually_all.mpr hev] with n hn
  rw [Real.dist_eq]
  have he := grid_increment_error (hG n) hP ha hh
    (N := N) (η := η) (fun i hi => hn ⟨i, Nat.lt_succ_iff.mpr hi⟩)
  rw [hxN, hηeq] at he
  linarith

theorem deficit_secant_energy_tendsto_filter {ι : Type*} {l : Filter ι} {G d : ι → ℝ → ℝ} {P D : ℝ → ℝ}
    {err : ι → ℝ} (hG : ∀ n, DeficitSecants (G n) (d n))
    (hP : DeficitSecants P D)
    (hd : ∀ t : ℝ, 0 < t → Tendsto (fun n => d n t) l (𝓝 (D t)))
    (he : Tendsto err l (𝓝 0))
    (hzero : ∀ v, 0 < v → ∀ᶠ n in l, -err n - v * d n v ≤ G n v ∧ G n v ≤ 0)
    (hPc : ContinuousAt P 0) (hP0 : P 0 = 0) (hDc : ContinuousAt D 0)
    {t : ℝ} (ht : 0 < t) : Tendsto (fun n => G n t) l (𝓝 (P t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hc : ContinuousAt (fun v : ℝ => |P v| + |v * D v|) 0 :=
    hPc.abs.add ((continuousAt_id.mul hDc).abs)
  have hevent : ∀ᶠ v in 𝓝 (0 : ℝ), |P v| + |v * D v| < ε / 4 := by
    have hconv : Tendsto (fun v : ℝ => |P v| + |v * D v|) (𝓝 0) (𝓝 0) := by
      simpa [hP0] using hc.tendsto
    exact hconv.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))
  obtain ⟨δ, hδ, hδevent⟩ := Metric.eventually_nhds_iff.mp hevent
  let v : ℝ := min (t / 2) (δ / 2)
  have hv : 0 < v := lt_min (by positivity) (by positivity)
  have hvt : v < t := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hvδ : dist v 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hv]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hsmall := hδevent hvδ
  have hinc := deficit_secant_increments_tendsto_filter hG hP hd hv hvt
  have hbound : Tendsto (fun n => err n + v * d n v) l (𝓝 (v * D v)) := by
    simpa using he.add ((hd v hv).const_mul v)
  filter_upwards [(Metric.tendsto_nhds.mp hinc) (ε / 4) (by positivity),
    (Metric.tendsto_nhds.mp hbound) (ε / 4) (by positivity), hzero v hv] with n hn hb hz
  rw [Real.dist_eq] at hn hb ⊢
  have hGv : |G n v| ≤ err n + v * d n v := by
    rw [abs_of_nonpos hz.2]
    linarith [hz.1]
  have hbound' : err n + v * d n v < |v * D v| + ε / 4 := by
    have hb' := (abs_lt.mp hb).2
    linarith [le_abs_self (v * D v)]
  have halg : G n t - P t =
      ((G n t - G n v) - (P t - P v)) + (G n v - P v) := by ring
  rw [halg]
  have htri := abs_add_le ((G n t - G n v) - (P t - P v)) (G n v - P v)
  have hsub := abs_sub (G n v) (P v)
  linarith

theorem priced_energy_limits_filter {ι : Type*} {l : Filter ι} {G d : ι → ℝ → ℝ} {err : ι → ℝ} {q : ℝ}
    (hq : 0 ≤ q) (hG : ∀ n, DeficitSecants (G n) (d n))
    (hd : ∀ t : ℝ, 0 < t → Tendsto (fun n => d n t) l (𝓝 (limitDeficit q t)))
    (he : Tendsto err l (𝓝 0))
    (hzero : ∀ n v, 0 < v → -err n - v * d n v ≤ G n v ∧ G n v ≤ 0)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => G n t) l (𝓝 (limitPriceEnergy q t)) ∧
    Tendsto (fun n => G n t + t * d n t) l (𝓝 (limitSectorEnergy q t)) := by
  have hprice := deficit_secant_energy_tendsto_filter hG (deficitSecants_limitPriceEnergy hq)
    hd he (fun v hv => Eventually.of_forall fun n => hzero n v hv) (continuous_limitPriceEnergy q).continuousAt
    (by simp [limitPriceEnergy]) (continuous_limitDeficit q).continuousAt ht
  exact ⟨hprice, by simpa only [limitPriceEnergy_add ht] using hprice.add ((hd t ht).const_mul t)⟩

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfCenteredPrice
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.fermionSpace_nontrivial _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
namespace CoulombAnalysis
open CoulombAtom

lemma tfPriceDeficit_tendsto {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun Z => tfPriceDeficit Z μ) atTop (𝓝 (limitDeficit tfResidualCharge μ)) := by
  have ht : Tendsto (fun Z : ℝ => Z/μ^(3/4:ℝ)) atTop atTop :=
    tendsto_id.atTop_div_const (Real.rpow_pos_of_pos hμ _)
  simpa only [tfPriceDeficit, limitDeficit, Function.comp_def, mul_comm (μ^(3/4:ℝ))] using
    (tf_unit_deficit_tendsto.comp ht).const_mul (μ^(3/4:ℝ))

lemma tfPriceDeficit_of_nonpos {Z μ : ℝ} (hZ : Z ≤ 0) (hμ : 0 < μ) :
    tfPriceDeficit Z μ = 0 := by
  have hz : ¬0 < Z/μ^(3/4:ℝ) := not_lt.mpr (div_nonpos_of_nonpos_of_nonneg hZ (Real.rpow_nonneg hμ.le _))
  simp only [tfPriceDeficit, tfUnitDeficit, dite_eq_right hz, mul_zero]

lemma tfCenteredPrice_secants (Z : ℝ) : DeficitSecants (tfCenteredPrice Z) (tfPriceDeficit Z) := by
  intro v t hv hvt
  have ht := hv.trans hvt
  by_cases hZ : 0 < Z
  · simp only [tfCenteredPrice, ite_eq_left hZ]
    have htv := tfPriceValue_secant hZ ht hv
    have hvt := tfPriceValue_secant hZ hv ht
    constructor <;> linarith
  · simp only [tfCenteredPrice, ite_eq_right hZ, tfPriceDeficit_of_nonpos (le_of_not_gt hZ) hv,
      tfPriceDeficit_of_nonpos (le_of_not_gt hZ) ht, mul_zero, sub_self, le_refl, and_self]

lemma tfCenteredPrice_bounds (Z μ : ℝ) (hμ : 0 < μ) :
    -μ*tfPriceDeficit Z μ ≤ tfCenteredPrice Z μ ∧ tfCenteredPrice Z μ ≤ 0 := by
  by_cases hZ : 0 < Z
  · simpa only [tfCenteredPrice, ite_eq_left hZ] using tfPriceValue_zero_bounds hZ hμ
  · simp [tfCenteredPrice, hZ, tfPriceDeficit_of_nonpos (le_of_not_gt hZ) hμ]

theorem tf_priced_energy_limits {t : ℝ} (ht : 0 < t) :
    Tendsto (fun Z => tfPriceValue Z t-tfEnergy Z Z) atTop (𝓝 (limitPriceEnergy tfResidualCharge t)) ∧
    Tendsto (fun Z => tfPriceValue Z t-tfEnergy Z Z+t*tfPriceDeficit Z t) atTop
      (𝓝 (limitSectorEnergy tfResidualCharge t)) := by
  have hh := priced_energy_limits_filter (l := (atTop : Filter ℝ)) (err := fun _ => 0)
    tfResidualCharge_pos.le tfCenteredPrice_secants (fun _ ht => tfPriceDeficit_tendsto ht)
    tendsto_const_nhds (fun Z v hv => by
      simpa only [neg_zero, zero_sub, neg_mul] using tfCenteredPrice_bounds Z v hv) ht
  constructor
  · apply hh.1.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with Z hZ
    simp [tfCenteredPrice, hZ]
  · apply hh.2.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with Z hZ
    simp [tfCenteredPrice, hZ]

lemma tfIonization_le_priced_max {Z u v : ℝ} (hZ : 0 < Z) (hu : 0 < u) (hv : 0 < v)
    (hdu : tfPriceDeficit Z u < 1) (hdv : 1 < tfPriceDeficit Z v) :
    tfIonization 1 Z ≤ max
      (tfPriceValue Z u-tfEnergy Z Z+u*tfPriceDeficit Z u)
      (tfPriceValue Z v-tfEnergy Z Z+v*tfPriceDeficit Z v) := by
  let P := tfPriceData hZ hu
  let Q := tfPriceData hZ hv
  let d := tfPriceDeficit Z u
  let e := tfPriceDeficit Z v
  have he : 0 < e-d := by dsimp [d,e]; linarith
  let a := (e-1)/(e-d)
  let b := (1-d)/(e-d)
  have ha : 0 ≤ a := div_nonneg (by dsimp [e]; linarith) he.le
  have hb : 0 ≤ b := div_nonneg (by dsimp [d]; linarith) he.le
  have hab : a+b=1 := by dsimp [a,b]; rw [← add_div]; convert div_self he.ne' using 1; ring
  have hP : P.mass=Z-d := by dsimp [P,d]; rw [tfPriceDeficit_eq hZ hu]; ring
  have hQ : Q.mass=Z-e := by dsimp [Q,e]; rw [tfPriceDeficit_eq hZ hv]; ring
  have hm : a*P.mass+b*Q.mass=Z-1 := by rw [hP,hQ]; dsimp [a,b]; field_simp; ring
  obtain ⟨hx, hxe⟩ := tf_compact_mix P.admissible Q.admissible P.compact Q.compact ha hb hab Z
  rw [hm] at hx
  have hle := (tfEnergy_le_trial hZ hx).trans hxe
  have h1 : tfFunctional Z P.density = tfPriceValue Z u+u*d := by rw [tfPriceValue_eq hZ hu]; dsimp [P,d]; ring
  have h2 : tfFunctional Z Q.density = tfPriceValue Z v+v*e := by rw [tfPriceValue_eq hZ hv]; dsimp [Q,e]; ring
  rw [h1,h2] at hle
  let A := tfPriceValue Z u-tfEnergy Z Z+u*d
  let B := tfPriceValue Z v-tfEnergy Z Z+v*e
  have hmax : a*A+b*B ≤ max A B := by
    calc
      _ ≤ a*max A B+b*max A B := add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
      _ = _ := by rw [← add_mul, hab, one_mul]
  have hmulte : (a+b)*tfEnergy Z Z = tfEnergy Z Z := by rw [hab, one_mul]
  change tfEnergy Z (Z-1)-tfEnergy Z Z ≤ max A B
  dsimp [A,B] at hmax ⊢
  nlinarith

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_ActualTFCoefficient
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
namespace CoulombAnalysis
open CoulombAtom

lemma actualTFCoefficient_pos : 0 < actualTFCoefficient :=
  mul_pos (by norm_num) (Real.rpow_pos_of_pos tfResidualCharge_pos _)

theorem tf_actual_unit_limit : Tendsto (tfIonization 1) atTop (𝓝 actualTFCoefficient) := by
  let q := tfResidualCharge
  let c := q^(-4/3:ℝ)
  have hq : 0 < q := tfResidualCharge_pos
  have hc : 0 < c := Real.rpow_pos_of_pos hq _
  have hDc : limitDeficit q c = 1 := limitDeficit_target hq
  have hLc : limitSectorEnergy q c = actualTFCoefficient := limitSectorEnergy_target hq
  have hlow : Tendsto (fun Z => tfPriceValue Z c-tfEnergy Z Z+c) atTop (𝓝 actualTFCoefficient) := by
    have hh := (tf_priced_energy_limits hc).1.add_const c
    have he : limitPriceEnergy q c+c = actualTFCoefficient := by
      rw [← hLc, ← limitPriceEnergy_add hc, hDc, mul_one]
    change Tendsto _ atTop (𝓝 (limitPriceEnergy q c+c)) at hh
    rwa [he] at hh
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [eventually_gt_atTop (1:ℝ), hlow.eventually (lt_mem_nhds ha)] with Z hZ hl
    have hh := tfPriceValue_le_energy (zero_lt_one.trans hZ) hc (by linarith : 0 ≤ Z-1)
    unfold tfIonization
    linarith
  · intro a ha
    have hcont := (continuous_limitSectorEnergy q).continuousAt (x := c)
    obtain ⟨δ, hδ, hδL⟩ := Metric.continuousAt_iff.mp hcont ((a-actualTFCoefficient)/2) (by linarith)
    let η := min (c/2) (δ/2)
    have hη : 0 < η := lt_min (by positivity) (by positivity)
    have hηc : η ≤ c/2 := min_le_left _ _
    have hηδ : η < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hm : 0 < c-η := by linarith
    have hp : 0 < c+η := by linarith
    have hDm : limitDeficit q (c-η) < 1 := by
      rw [← hDc]; exact (limitDeficit_strictMonoOn hq) hm hc (by linarith)
    have hDp : 1 < limitDeficit q (c+η) := by
      rw [← hDc]; exact (limitDeficit_strictMonoOn hq) hc hp (by linarith)
    have hLm : limitSectorEnergy q (c-η) < a := by
      have hh := hδL (show dist (c-η) c < δ by simpa [Real.dist_eq, abs_of_pos hη] using hηδ)
      rw [Real.dist_eq, hLc] at hh
      have := (abs_lt.mp hh).2
      linarith
    have hLp : limitSectorEnergy q (c+η) < a := by
      have hh := hδL (show dist (c+η) c < δ by simpa [Real.dist_eq, abs_of_pos hη] using hηδ)
      rw [Real.dist_eq, hLc] at hh
      have := (abs_lt.mp hh).2
      linarith
    filter_upwards [eventually_gt_atTop (0:ℝ),
      (tfPriceDeficit_tendsto hm).eventually (gt_mem_nhds hDm),
      (tfPriceDeficit_tendsto hp).eventually (lt_mem_nhds hDp),
      (tf_priced_energy_limits hm).2.eventually (gt_mem_nhds hLm),
      (tf_priced_energy_limits hp).2.eventually (gt_mem_nhds hLp)] with Z hZ hdm hdp hjm hjp
    exact (tfIonization_le_priced_max hZ hm hp hdm hdp).trans_lt (max_lt hjm hjp)

theorem tf_actual_characterization : TFCharacterization actualTFCoefficient :=
  tfCharacterization_of_unit_limit tf_actual_unit_limit

end CoulombAnalysis

open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_ActualUpperDeficitBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Filter Set
open scoped Topology

open CoulombAnalysis

lemma quantumUpperDeficitConstant_pos : 0 < quantumUpperDeficitConstant := by
  have := tfPatchCapConstant_pos
  unfold quantumUpperDeficitConstant
  positivity

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_FinitePotentialDecay
attribute [-instance] _root_.OAI.CoulombAtom.fermionSpace_nontrivial _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set Metric
open scoped Topology
noncomputable section
namespace CoulombAnalysis
open CoulombAtom

lemma cutoff_coulomb_majorant {ρ : TFSpace → ℝ} {x : TFSpace} {b M : ℝ}
    (hb : 0 < b) (hn : ∀ z, 0 ≤ ρ z) (hM : ∀ z, ρ z ≤ M) (z : TFSpace) :
    ρ z/‖x-z‖ ≤ M*truncatedCoulomb b (x-z)+ρ z/max b ‖x-z‖ := by
  by_cases hz : ‖x-z‖ < b
  · rw [max_eq_left hz.le,truncatedCoulomb,indicator_of_mem (mem_ball_zero_iff.mpr hz)]
    have hh := mul_le_mul_of_nonneg_right (hM z) (inv_nonneg.mpr (norm_nonneg (x-z)))
    simp only [div_eq_mul_inv,one_mul] at hh ⊢
    linarith [mul_nonneg (hn z) (inv_pos.mpr hb).le]
  · rw [max_eq_right (le_of_not_gt hz),truncatedCoulomb,
      indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hz),mul_zero,zero_add]

lemma cutoff_coulomb_integrable {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z) {b : ℝ} (hb : 0 < b) (x : TFSpace) :
    Integrable (fun z => ρ z/max b ‖x-z‖) := by
  apply (hi.div_const b).mono'
    (hm.div (measurable_const.max (measurable_const.sub measurable_id).norm)).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    change ‖ρ z/max b ‖x-z‖‖ ≤ ρ z/b
    rw [Real.norm_of_nonneg (div_nonneg (hn z) (hb.le.trans (le_max_left _ _)))]
    exact div_le_div_of_nonneg_left (hn z) hb (le_max_left _ _))

lemma potential_cutoff_le {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z) {M b : ℝ} (hM : ∀ z, ρ z ≤ M)
    (hb : 0 < b) (x : TFSpace) :
    tfPotential ρ x ≤ 2*Real.pi*M*b^2+∫ z, ρ z/max b ‖x-z‖ := by
  have hk : Integrable (fun z => truncatedCoulomb b (x-z)) :=
    (tfSubMap_preserving x).integrable_comp (truncatedCoulomb_integrable b).aestronglyMeasurable
      |>.mpr (truncatedCoulomb_integrable b)
  calc
    _ ≤ ∫ z, M*truncatedCoulomb b (x-z)+ρ z/max b ‖x-z‖ := integral_mono
      (local_bounded_potential_integrable hm hi hb hn (fun z _ => hM z))
      ((hk.const_mul M).add (cutoff_coulomb_integrable hm hi hn hb x))
      (cutoff_coulomb_majorant hb hn hM)
    _ = _ := by
      rw [integral_add (hk.const_mul M) (cutoff_coulomb_integrable hm hi hn hb x),
        integral_const_mul,integral_sub_left_eq_self,truncatedCoulomb,integral_indicator measurableSet_ball]
      simp only [one_div]
      rw [integral_coulomb_ball hb]
      ring

lemma cutoff_potential_decay {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    {v : ι → TFSpace} (hv : Tendsto (fun i => ‖v i‖) F atTop)
    {ρ : TFSpace → ℝ} (hm : Measurable ρ) (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {b : ℝ} (hb : 0 < b) :
    Tendsto (fun i => ∫ z, ρ z/max b ‖v i-z‖) F (𝓝 0) := by
  have hh := tendsto_integral_filter_of_dominated_convergence (l := F)
    (F := fun i z => ρ z/max b ‖v i-z‖) (fun z => ρ z/b)
    (f := fun _ : TFSpace => (0:ℝ))
    (Eventually.of_forall (fun i => (cutoff_coulomb_integrable hm hi hn hb (v i)).aestronglyMeasurable))
    (Eventually.of_forall (fun i => ae_of_all _ (fun z => by
      rw [Real.norm_of_nonneg (div_nonneg (hn z) (hb.le.trans (le_max_left _ _)))]
      exact div_le_div_of_nonneg_left (hn z) hb (le_max_left _ _))))
    (hi.div_const b) (ae_of_all _ (fun z => ?_))
  · simpa only [integral_zero] using hh
  · apply Tendsto.const_div_atTop
    apply tendsto_atTop_mono (fun i => le_max_right b ‖v i-z‖)
    apply tendsto_atTop_mono (fun i => ?_) (show Tendsto (fun i => ‖v i‖-‖z‖) F atTop from by
      simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right F (-‖z‖) hv)
    linarith [norm_le_norm_sub_add (v i) z]

theorem bounded_L1_potential_decay {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    {v : ι → TFSpace} (hv : Tendsto (fun i => ‖v i‖) F atTop)
    {ρ : TFSpace → ℝ} (hm : Measurable ρ) (hi : Integrable ρ)
    (hn : ∀ z, 0 ≤ ρ z) {M : ℝ} (hM : 0 ≤ M) (hMb : ∀ z, ρ z ≤ M) :
    Tendsto (fun i => tfPotential ρ (v i)) F (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let b := Real.sqrt (ε/(8*Real.pi*(M+1)))
  have hd : 0 < 8*Real.pi*(M+1) := by positivity
  have hb : 0 < b := Real.sqrt_pos.mpr (div_pos hε hd)
  have hbs : b^2 = ε/(8*Real.pi*(M+1)) := Real.sq_sqrt (div_pos hε hd).le
  have hmul : b^2*(8*Real.pi*(M+1)) = ε := by rw [hbs]; exact div_mul_cancel₀ ε hd.ne'
  have hnear : 2*Real.pi*M*b^2 < ε/2 := by
    nlinarith [mul_pos Real.pi_pos (sq_pos_of_pos hb)]
  have hfar := cutoff_potential_decay hv hm hi hn hb
  filter_upwards [hfar.eventually (gt_mem_nhds (half_pos hε))] with i hi'
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (tfPotential_nonneg (ae_of_all _ hn) _)]
  exact lt_of_le_of_lt (potential_cutoff_le hm hi hn hMb hb (v i)) (by linarith)
end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierTransferGlobal
attribute [-instance] _root_.OAI.CoulombAtom.fermionSpace_nontrivial _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology
noncomputable section
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

theorem barrier_transfer_global {a ρ p q : TFSpace → ℝ} {Z k r lam M P Q C : ℝ}
    (hr : 0 < r) (hlam : 0 ≤ lam) (hk : 0 ≤ k)
    (ha : Continuous a)
    (hρm : Measurable ρ) (hρi : Integrable ρ) (hM : 0 ≤ M)
    (hρn : ∀ x, 0 ≤ ρ x) (hρb : ∀ x, ρ x ≤ M)
    (hpm : Measurable p) (hpi : Integrable p) (hP : 0 ≤ P)
    (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ P)
    (hqm : Measurable q) (hqi : Integrable q) (hQ : 0 ≤ Q)
    (hqn : ∀ x, 0 ≤ q x) (hqb : ∀ x, q x ≤ Q)
    (hw : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource r ρ p x+outerCoefficient r x*reaction k (nuclearField Z x+a x)))
    (hd : ∀ x, r ≤ ‖x‖ →
      4*Real.pi*ρ x ≤ reaction k (nuclearField Z x-tfPotential ρ x-lam)+4*Real.pi*q x)
    (hu : ∀ x, r ≤ ‖x‖ → nuclearField Z x+a x ≤ C/‖x‖^4) :
    ∀ x, nuclearField Z x+a x ≤ nuclearField Z x-tfPotential ρ x+
        tfPotential (fun y => p y+q y) x := by
  have hn : Tendsto (norm : TFSpace → ℝ) (comap norm (atTop : Filter ℝ)) atTop := tendsto_comap
  have hpdec := bounded_L1_potential_decay hn hρm hρi hρn hM hρb
  have hd0 : Tendsto (fun x : TFSpace => C/‖x‖^4-Z/‖x‖+tfPotential ρ x)
      (comap norm (atTop : Filter ℝ)) (𝓝 0) := by
    simpa only [sub_zero,zero_add, Function.comp_apply] using
      (((tendsto_pow_atTop (by norm_num : (4:ℕ) ≠ 0)).comp hn).const_div_atTop C).sub
        (hn.const_div_atTop Z) |>.add hpdec
  intro x
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨S,hS⟩ := eventually_atTop.mp (eventually_comap.mp (hd0.eventually (gt_mem_nhds hε)))
  let T := max (max S ‖x‖) (r+1)
  have hST : S ≤ T := (le_max_left S ‖x‖).trans (le_max_left _ _)
  have hxT : ‖x‖ ≤ T := (le_max_right S ‖x‖).trans (le_max_left _ _)
  have hrT : r < T := (lt_add_one r).trans_le (le_max_right _ _)
  have hT : 0 < T := hr.trans hrT
  apply barrier_transfer_ball hr hT hlam hk hε.le ha hρm hρi hM hρn hρb
    hpm hpi hP hpn hpb hqm hqi hQ hqn hqb hw (fun y _ hy => hd y hy) _ x
    (mem_closedBall_zero_iff.mpr hxT)
  intro y hy
  have hbd := hu y (hrT.le.trans_eq hy.symm)
  have hsmall := hS T hST y hy
  unfold nuclearField at hbd
  linarith
end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierChargeBound
attribute [-instance] _root_.OAI.CoulombAtom.fermionSpace_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology
noncomputable section
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

theorem barrier_charge_bound {a ρ p : TFSpace → ℝ} {Z k r l S M P C : ℝ}
    (hr : 0 < r) (hl : 0 < l) (hal : 1/(2*l) ≤ r) (hk : 0 ≤ k)
    (ha : Continuous a)
    (hρm : Measurable ρ) (hρi : Integrable ρ) (hM : 0 ≤ M)
    (hρn : ∀ x, 0 ≤ ρ x) (hρb : ∀ x, ρ x ≤ M)
    (hpm : Measurable p) (hpi : Integrable p) (hP : 0 ≤ P)
    (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ P)
    (hw : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource r ρ p x+outerCoefficient r x*reaction k (nuclearField Z x+a x)))
    (hd : ∀ x, r ≤ ‖x‖ → ‖x‖ ≤ S →
      ρ x ≤ k*(max (nuclearField Z x-tfPotential ρ x-1) 0)^(3/2:ℝ)+l⁻¹^8/‖x‖^6)
    (hlo : ∀ x, r ≤ ‖x‖ → 0 ≤ nuclearField Z x+a x)
    (hu : ∀ x, r ≤ ‖x‖ → nuclearField Z x+a x ≤ C/‖x‖^4) :
    (∫ x, ρ x)-Z ≤ (∫ x, p x)+
      volume.real (closedBall (0:TFSpace) S)*(64*l⁻¹^2)+(∫ x in {x : TFSpace | S < ‖x‖}, ρ x) := by
  let q₀ := annularApproximationError l r S
  let E : Set TFSpace := {x | S < ‖x‖}
  let q : TFSpace → ℝ := fun x => q₀ x+E.indicator ρ x
  have hEm : MeasurableSet E := measurableSet_lt measurable_const measurable_norm
  have hq₀m : Measurable q₀ := annularApproximationError_measurable _ _ _
  have hq₀n : ∀ x, 0 ≤ q₀ x := annularApproximationError_nonneg _ _ _
  have hq₀b : ∀ x, q₀ x ≤ 64*l⁻¹^2 := annularApproximationError_bound hl hal
  have hq₀i := bounded_compact_mass_le hq₀m (by positivity : 0 ≤ 64*l⁻¹^2)
    hq₀n hq₀b (annularApproximationError_support _ _ _)
  have htm : Measurable (E.indicator ρ) := hρm.indicator hEm
  have hti : Integrable (E.indicator ρ) := hρi.indicator hEm
  have htn : ∀ x, 0 ≤ E.indicator ρ x := fun x => indicator_nonneg (fun z _ => hρn z) x
  have htb : ∀ x, E.indicator ρ x ≤ M := by
    intro x
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx]; exact hρb x
    · rw [indicator_of_notMem hx]; exact hM
  have hqm : Measurable q := hq₀m.add htm
  have hqi : Integrable q := hq₀i.1.add hti
  have hqn : ∀ x, 0 ≤ q x := fun x => add_nonneg (hq₀n x) (htn x)
  have hqb : ∀ x, q x ≤ 64*l⁻¹^2+M := fun x => add_le_add (hq₀b x) (htb x)
  have hcomp : ∀ x, r ≤ ‖x‖ →
      4*Real.pi*ρ x ≤ reaction k (nuclearField Z x-tfPotential ρ x-1)+4*Real.pi*q x := by
    intro x hx
    by_cases hxS : ‖x‖ ≤ S
    · have hq0 : q₀ x = l⁻¹^8/‖x‖^6 := indicator_of_mem (show x ∈ {x : TFSpace | r ≤ ‖x‖ ∧ ‖x‖ ≤ S} from ⟨hx,hxS⟩) _
      have ht0 : E.indicator ρ x = 0 := indicator_of_notMem (show x ∉ E from not_lt.mpr hxS) _
      dsimp [q]
      rw [hq0,ht0,add_zero,reaction]
      have hh := mul_le_mul_of_nonneg_left (hd x hx hxS) (by positivity : (0:ℝ) ≤ 4*Real.pi)
      nlinarith only [hh]
    · have ht0 : E.indicator ρ x = ρ x := indicator_of_mem (show x ∈ E from lt_of_not_ge hxS) _
      have hqρ : ρ x ≤ q x := by dsimp [q]; rw [ht0]; exact le_add_of_nonneg_left (hq₀n x)
      have hreac : 0 ≤ reaction k (nuclearField Z x-tfPotential ρ x-1) := by
        unfold reaction; positivity
      have hh := mul_le_mul_of_nonneg_left hqρ (by positivity : (0:ℝ) ≤ 4*Real.pi)
      linarith
  have htrans := barrier_transfer_global hr (by norm_num : (0:ℝ) ≤ 1) hk ha
    hρm hρi hM hρn hρb hpm hpi hP hpn hpb hqm hqi (by positivity) hqn hqb hw hcomp hu
  have heqn : ∀ x, 0 ≤ p x+q x := fun x => add_nonneg (hpn x) (hqn x)
  have hcharge := corrected_field_charge hr hρm hρi hM hρn hρb
    (hpm.add hqm) (hpi.add hqi) heqn (fun x hx => (hlo x hx).trans (htrans x))
  change (∫ x, ρ x)-Z ≤ ∫ x, p x+q x at hcharge
  rw [integral_add hpi hqi] at hcharge
  have hqmass : (∫ x, q x) ≤ volume.real (closedBall (0:TFSpace) S)*(64*l⁻¹^2)+
      (∫ x in E, ρ x) := by
    rw [show (∫ x, q x) = (∫ x, q₀ x)+(∫ x, E.indicator ρ x) from integral_add hq₀i.1 hti,
      integral_indicator hEm]
    linarith only [hq₀i.2]
  linarith

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_SelectedScreenedProfileBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfDensityCoefficient_pos : 0 < tfDensityCoefficient := by
  unfold tfDensityCoefficient
  have hh := tfKinetic_pos
  positivity
end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FiniteBarrier
attribute [-instance] _root_.OAI.CoulombAtom.fermionSpace_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology
open CoulombAtom CoulombAnalysis

lemma SelectedQuantumData.opposite_charge {Z s l τ B C R : ℝ} {N : ℕ}
    (d : SelectedQuantumData Z N s l τ B C R) (hs : 0 < s) (hl : 0 < l)
    (hB : 0 ≤ B) (hRl : R ≤ l) :
    -(s^3+volume.real (closedBall (0:TFSpace) R)*(64*l⁻¹^2)+τ) ≤ s^3*(Z-(N:ℝ)) := by
  obtain ⟨M,hM,hMb⟩ := d.bounded_density
  obtain ⟨P,hP,hPb⟩ := d.bounded_error
  have hh := barrier_charge_bound (div_pos d.radius_pos hs) hl d.radius_lower
    tfDensityCoefficient_pos.le ((d.continuous_offset.comp (continuous_id.const_smul s)).const_mul (s^4))
    (tfDilation_measurable d.measurable_density) (tfDilation_integrable hs d.integrable_density)
    (mul_nonneg (pow_nonneg hs.le 6) hM) (tfDilation_nonneg d.nonneg_density)
    (fun x => mul_le_mul_of_nonneg_left (hMb _) (pow_nonneg hs.le 6))
    (tfDilation_measurable d.measurable_error) (tfDilation_integrable hs d.integrable_error)
    (mul_nonneg (pow_nonneg hs.le 6) hP) (tfDilation_nonneg d.nonneg_error)
    (fun x => mul_le_mul_of_nonneg_left (hPb _) (pow_nonneg hs.le 6))
    (barrier_weak_dilation hs d.weak)
    (S := R) (fun x hx hxR => by
      have ht := (abs_le.mp (d.TF x hx (hxR.trans hRl))).2
      linarith only [ht])
    (fun x hx => (show 0 ≤ (7*B/8)/‖x‖^4 by positivity).trans
      ((outerBarrier_bounds hB (div_pos d.radius_pos hs) hx).1.trans
        (scaled_barrier_lower hs d.lower x hx)))
    (scaled_barrier_upper hs d.upper)
  rw [tfDilation_mass hs,tfDilation_mass hs,d.mass_density] at hh
  have he := mul_le_mul_of_nonneg_left d.mass_error (pow_nonneg hs.le 3)
  nlinarith only [hh,he,d.tail]

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ShellAbsorptionNumerics
attribute [-instance] _root_.OAI.CoulombAtom.fermionSpace_nontrivial _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply FermionLipschitzMultiplier.apply oneBodySquareTotal
  formEnergy energy sectorExcessOperator fermionGraphValue shellBiasMultiplier
  rawFormPair formMass weightedMass oneBodyGradientError corePriceExcess shellMeanField innerScale

lemma actualShellRadius_ge : 16 ≤ actualShellRadius := le_max_left _ _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ExteriorScreenNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

lemma actualScreenRadius_ge : actualShellRadius ≤ actualScreenRadius := le_max_left _ _
lemma actualScreenRadius_ge16 : 16 ≤ actualScreenRadius := actualShellRadius_ge.trans actualScreenRadius_ge

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
open CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator graphRawLaw

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SelectionBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

section
open MeasureTheory Filter Set
open scoped Topology
open CoulombAtom CoulombAnalysis

lemma selectedTailThreshold_tendsto {ι : Type*} {F : Filter ι} {s : ι → ℝ}
    (hs : Tendsto s F (𝓝 0)) : Tendsto (fun i => selectedTailThreshold (s i)) F (𝓝 0) := by
  simpa only [selectedTailThreshold,mul_zero] using hs.const_mul (actualScreenConstant+1)

lemma price_scale_inverse {s : ℝ} (hs : 0 < s) : s^(-4:ℝ) = 1/s^4 := by
  rw [Real.rpow_neg hs.le,show (4:ℝ) = (4:ℕ) by norm_num,Real.rpow_natCast,one_div]

end
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local instance] physicalObservationLaw_probability

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SelectionDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set Metric
open scoped Topology
noncomputable section
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma diagonal_of_eventually {P : ℕ → ℕ → Prop} (hP : ∀ k, ∀ᶠ n in atTop, P n k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, P (φ k) k := by
  classical
  choose t ht using fun k => eventually_atTop.mp (hP k)
  let φ : ℕ → ℕ := Nat.rec (t 0) (fun k prev => max (prev+1) (t (k+1)))
  have hφstep (k) : φ k < φ (k+1) := by
    change φ k < max (φ k+1) (t (k+1))
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  refine ⟨φ,strictMono_nat_of_lt_succ hφstep,fun k => ht k (φ k) ?_⟩
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_max_right _ _

lemma SelectedQuantumData.rough_lower {Z s l τ B C R : ℝ} {N : ℕ}
    (d : SelectedQuantumData Z N s l τ B C R) (hs : 0 < s) (hs1 : s ≤ 1)
    (hl : 1 ≤ l) (hτ : τ ≤ 1) (hB : 0 ≤ B) (hRl : R ≤ l) :
    -(2+64*volume.real (closedBall (0:TFSpace) R)) ≤ s^3*(Z-(N:ℝ)) := by
  have hh := d.opposite_charge hs (zero_lt_one.trans_le hl) hB hRl
  have hs3 : s^3 ≤ 1 := pow_le_one₀ hs.le hs1
  have hl2 : l⁻¹^2 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr (zero_lt_one.trans_le hl).le)
    ((inv_le_one₀ (zero_lt_one.trans_le hl)).mpr hl)
  have hv : 0 ≤ volume.real (closedBall (0:TFSpace) R) := ENNReal.toReal_nonneg
  have hmul := mul_le_mul_of_nonneg_left hl2 (mul_nonneg (by norm_num : (0:ℝ) ≤ 64) hv)
  nlinarith only [hh,hs3,hmul,hτ]

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_PricedSubsequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier
open MeasureTheory Filter Set Metric
open scoped Topology
open CoulombAtom CoulombAnalysis

lemma actual_priced_deficit_subsequence (Z N : ℕ → ℕ) (s : ℕ → ℝ)
    (hZ : ∀ n, 1 ≤ Z n) (hs : ∀ n, 0 < s n) (hs0 : Tendsto s atTop (𝓝 0))
    (hscale : Tendsto (fun n => (Z n:ℝ)*(s n)^3) atTop atTop)
    (hN : ∀ n, PriceMinimizes (energy (Z n)) ((s n)^(-4:ℝ)) (N n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (s (φ n))^3*((Z (φ n):ℝ)-(N (φ n):ℝ))) atTop (𝓝 tfResidualCharge) := by
  classical
  obtain ⟨B,C,hB,hC,hfinite⟩ := exists_actual_selected_data_constants
  let R := selectedTailRadius
  have hR : 0 < R := by
    have hh := actualScreenRadius_ge16
    dsimp [R,selectedTailRadius]
    linarith
  let l : ℕ → ℝ := fun k => (k:ℝ)+max R 1
  have hl (k) : 1 ≤ l k := by dsimp [l]; linarith [Nat.cast_nonneg (α := ℝ) k,le_max_right R 1]
  have hRl (k) : R ≤ l k := by dsimp [l]; linarith [Nat.cast_nonneg (α := ℝ) k,le_max_left R 1]
  have hl0 : Tendsto l atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hτ0 := selectedTailThreshold_tendsto hs0
  have hsmall := hs0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  have hτsmall := hτ0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  have hu := actual_uniform_upper_deficit (Eventually.of_forall hs) hs0
  have hchoose (k : ℕ) : ∀ᶠ n in atTop,
      Nonempty (SelectedQuantumData (Z n) (N n) (s n) (l k) (selectedTailThreshold (s n)) B C R) ∧
      s n ≤ 1 ∧ selectedTailThreshold (s n) ≤ 1 ∧
      (s n)^3*((Z n:ℝ)-(N n:ℝ)) ≤ quantumUpperDeficitConstant := by
    filter_upwards [hfinite Z s N hZ hs hs0 hscale hN (l k) (hl k),hsmall,hτsmall,hu]
      with n hd hs1 hτ1 hu1
    refine ⟨hd,hs1.le,hτ1.le,hu1 (Z n) (Nat.cast_nonneg _) (N n) ?_⟩
    simpa only [price_scale_inverse (hs n),one_div] using hN n
  obtain ⟨φ,hφ,hchosen⟩ := diagonal_of_eventually hchoose
  let d (k : ℕ) := Classical.choice (hchosen k).1
  let Q := quantumUpperDeficitConstant+(2+64*volume.real (closedBall (0:TFSpace) R))
  have hQ : 0 ≤ Q := by
    have hh := quantumUpperDeficitConstant_pos
    dsimp [Q]
    positivity
  have hbound (k) : |(s (φ k))^3*((Z (φ k):ℝ)-(N (φ k):ℝ))| ≤ Q := by
    have hlow := (d k).rough_lower (hs _) (hchosen k).2.1 (hl k) (hchosen k).2.2.1 hB.le (hRl k)
    have hhigh := (hchosen k).2.2.2
    have hv : 0 ≤ volume.real (closedBall (0:TFSpace) R) := ENNReal.toReal_nonneg
    have hqu := quantumUpperDeficitConstant_pos
    apply abs_le.mpr
    dsimp [Q]
    constructor <;> linarith
  obtain ⟨ψ,hψ,hlim⟩ := selected_data_profile_subsequence d
    (fun k => Nat.cast_nonneg (Z (φ k))) (fun k => hs (φ k)) hl
    (hs0.comp hφ.tendsto_atTop) hl0 (hτ0.comp hφ.tendsto_atTop) hB hC hR hQ hbound
  exact ⟨φ ∘ ψ,hφ.comp hψ,hlim⟩

end CoulombBarrier

section
open Filter Set
open scoped Topology

lemma real_tendsto_of_subsequences {a : ℕ → ℝ} {b : ℝ}
    (h : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ φ : ℕ → ℕ, Tendsto (fun n => a (ns (φ n))) atTop (𝓝 b)) :
    Tendsto a atTop (𝓝 b) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  by_contra hh
  have hfreq : ∃ᶠ n in atTop, ¬dist (a n) b < ε := not_eventually.mp hh
  obtain ⟨ns,hns,hbad⟩ := subseq_forall_of_frequently (x := fun n : ℕ => n) (p := fun n => ¬dist (a n) b < ε) tendsto_id hfreq
  obtain ⟨φ,hφ⟩ := h ns hns
  obtain ⟨n,hn⟩ := (Metric.tendsto_nhds.mp hφ ε hε).exists
  exact hbad (φ n) hn

end
open Filter
open scoped Topology
namespace CoulombAtom
open CoulombAnalysis CoulombBarrier

theorem actual_priced_deficit_limit (Z N : ℕ → ℕ) (s : ℕ → ℝ)
    (hZ : ∀ n, 1 ≤ Z n) (hs : ∀ n, 0 < s n) (hs0 : Tendsto s atTop (𝓝 0))
    (hscale : Tendsto (fun n => (Z n:ℝ)*(s n)^3) atTop atTop)
    (hN : ∀ n, PriceMinimizes (energy (Z n)) ((s n)^(-4:ℝ)) (N n)) :
    Tendsto (fun n => (s n)^3*((Z n:ℝ)-(N n:ℝ))) atTop (𝓝 tfResidualCharge) := by
  apply real_tendsto_of_subsequences
  intro ns hns
  obtain ⟨φ,_hφ,hlim⟩ := actual_priced_deficit_subsequence (Z ∘ ns) (N ∘ ns) (s ∘ ns)
    (fun n => hZ (ns n)) (fun n => hs (ns n)) (hs0.comp hns) (hscale.comp hns)
    (fun n => hN (ns n))
  exact ⟨φ,hlim⟩

end CoulombAtom

open Filter
open scoped Topology
namespace CoulombAtom

lemma fixedSectorScale_pos {t m : ℝ} (ht : 0 < t) (hm : 0 < m) :
    0 < fixedSectorScale t m := mul_pos (Real.rpow_pos_of_pos ht _) (Real.rpow_pos_of_pos hm _)
lemma fixedSectorScale_price {t m : ℝ} (ht : 0 < t) (hm : 0 < m) :
    (fixedSectorScale t m)^(-4:ℝ) = t*m^(4/3:ℝ) := by
  rw [fixedSectorScale,Real.mul_rpow (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg hm.le _),
    ←Real.rpow_mul ht.le,←Real.rpow_mul hm.le]
  norm_num
lemma fixedSectorScale_cube {t m : ℝ} (ht : 0 < t) (hm : 0 < m) :
    (fixedSectorScale t m)^3 = t^(-3/4:ℝ)/m := by
  rw [fixedSectorScale,mul_pow,←Real.rpow_natCast (t^(-1/4:ℝ)) 3,
    ←Real.rpow_natCast (m^(-1/3:ℝ)) 3,←Real.rpow_mul ht.le,←Real.rpow_mul hm.le]
  norm_num [Real.rpow_neg_one,div_eq_mul_inv]
lemma fixedSectorScale_deficit {t m Z N : ℝ} (ht : 0 < t) (hm : 0 < m) :
    t^(3/4:ℝ)*((fixedSectorScale t m)^3*(Z-N)) = (Z-N)/m := by
  rw [fixedSectorScale_cube ht hm]
  calc
    t^(3/4:ℝ)*(t^(-3/4:ℝ)/m*(Z-N)) = (t^(3/4:ℝ)*t^(-3/4:ℝ))*((Z-N)/m) := by ring
    _ = (Z-N)/m := by rw [←Real.rpow_add ht]; norm_num
lemma fixedSectorScale_tendsto {ι : Type*} {f : Filter ι} {m : ι → ℝ} {t : ℝ}
    (hm : Tendsto m f atTop) : Tendsto (fun i => fixedSectorScale t (m i)) f (𝓝 0) := by
  have hh := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).comp hm).const_mul (t^(-1/4:ℝ))
  simpa only [mul_zero,fixedSectorScale,Function.comp_def,neg_div] using hh
lemma fixedSectorScale_joint {ι : Type*} {f : Filter ι} {m Z : ι → ℝ} {t : ℝ}
    (ht : 0 < t) (hm : ∀ i, 0 < m i) (hr : Tendsto (fun i => Z i/m i) f atTop) :
    Tendsto (fun i => Z i*(fixedSectorScale t (m i))^3) f atTop := by
  have hh := hr.const_mul_atTop (Real.rpow_pos_of_pos ht (-3/4:ℝ))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  rw [fixedSectorScale_cube ht (hm i)]
  ring
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology
noncomputable section
namespace CoulombAtom
open CoulombAnalysis

theorem actual_quantum_jointLimit : JointLimit actualTFCoefficient := by
  classical
  intro m Z hm hmtop hratio
  have hmp (j) : 0 < (m j:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hm j).1)
  have hZ (j) : 1 ≤ Z j := (hm j).1.trans (hm j).2.le
  have hmr : Tendsto (fun j => (m j:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hmtop
  let N (j : ℕ) (t : ℝ) : ℕ := if ht : 0 < t then
    Classical.choose (quantum_exists_priceMinimizes (Nat.cast_nonneg (Z j))
      (mul_pos ht (Real.rpow_pos_of_pos (hmp j) (4/3:ℝ)))) else 0
  have hN (j : ℕ) (t : ℝ) (ht : 0 < t) :
      PriceMinimizes (energy (Z j)) (t*(m j:ℝ)^(4/3:ℝ)) (N j t) := by
    dsimp only [N]
    rw [dite_eq_left ht]
    exact Classical.choose_spec (quantum_exists_priceMinimizes (Nat.cast_nonneg (Z j))
      (mul_pos ht (Real.rpow_pos_of_pos (hmp j) (4/3:ℝ))))
  have hd (t : ℝ) (ht : 0 < t) : Tendsto (fun j => scaledDeficit (Z j) (N j t) (m j))
      atTop (𝓝 (limitDeficit tfResidualCharge t)) := by
    have hh := actual_priced_deficit_limit Z (fun j => N j t)
      (fun j => fixedSectorScale t (m j)) hZ (fun j => fixedSectorScale_pos ht (hmp j))
      (fixedSectorScale_tendsto hmr) (fixedSectorScale_joint ht hmp hratio)
      (fun j => by rw [fixedSectorScale_price ht (hmp j)]; exact hN j t ht)
    have hscaled := hh.const_mul (t^(3/4:ℝ))
    simpa only [fixedSectorScale_deficit ht (hmp _),scaledDeficit,limitDeficit,mul_comm] using hscaled
  have hfixed := fixed_sector_limit_of_priced_deficit tfResidualCharge_pos
    (fun j => ⟨(hm j).1,(hm j).2.le⟩)
    (fun j => quantum_energy_antitone (Nat.cast_nonneg (Z j))) hN hd
  exact hfixed

theorem generalized_ionization_oai : MainStatement :=
  ⟨actualTFCoefficient,actualTFCoefficient_pos,tf_actual_characterization,
    actual_quantum_jointLimit,iteratedLimits_of_jointLimit actual_quantum_jointLimit⟩

end CoulombAtom

end

end OAI
end

theorem solution : type_of% @OAI.CoulombAtom.generalized_ionization_oai := @OAI.CoulombAtom.generalized_ionization_oai
