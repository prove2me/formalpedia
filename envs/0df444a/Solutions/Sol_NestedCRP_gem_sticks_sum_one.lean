-- Prove2me | solution 1 for NestedCRP.gem_sticks_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-15T19:24:34.925974+00:00
-- url     : https://prove2.me/submissions/5f39a033-3fa8-4701-ad02-e5b0bb25e62a

import Mathlib
import Definitions.Def_NestedCRP_Hyper
import Definitions.Def_NestedCRP_gemLaw
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace StickNormalization
noncomputable section

def remainder (U : ℕ → ℝ) (n : ℕ) : ℝ := ∏ i ∈ Finset.range n, (1-U i)

lemma partial_sum (U : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, NestedCRP.stick U i = 1-remainder U n := by
  induction n with
  | zero => simp [remainder]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [remainder,Finset.prod_range_succ,NestedCRP.stick]
    ring

lemma beta_support (a b : ℝ) : ∀ᵐ x ∂betaMeasure a b, 0 < x ∧ x < 1 := by
  unfold betaMeasure
  rw [ae_withDensity_iff (by
    unfold betaPDF betaPDFReal
    apply Measurable.ennreal_ofReal
    exact Measurable.ite measurableSet_Ioo (by fun_prop) measurable_const)]
  exact ae_of_all _ fun x hx => by
    by_contra h
    exact hx (by simp [betaPDF,betaPDFReal,h])

lemma iid_sticks (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hs : ∀ᵐ x ∂ν, 0 < x ∧ x < 1) :
    ∀ᵐ U ∂Measure.infinitePi (fun _ : ℕ => ν), HasSum (NestedCRP.stick U) 1 := by
  let μ := Measure.infinitePi (fun _ : ℕ => ν)
  have hc : ∀ᵐ U ∂μ, ∀ i, 0 < U i ∧ U i < 1 := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) i).quasiMeasurePreserving.ae hs
  have hi : Integrable (fun x : ℝ => x) ν :=
    (integrable_const (1:ℝ)).mono' (by fun_prop) (hs.mono fun x hx => by
      rw [Real.norm_eq_abs,abs_of_pos hx.1]; exact hx.2.le)
  have hj : Integrable (fun x : ℝ => 1-x) ν := (integrable_const _).sub hi
  have hip : 0 < ∫ x : ℝ, x ∂ν := by
    apply (integral_pos_iff_support_of_nonneg_ae (hs.mono fun x hx => hx.1.le) hi).mpr
    have heq : Function.support (fun x : ℝ => x) =ᵐ[ν] Set.univ :=
      hs.mono fun x hx => by
        apply propext
        change (x ≠ 0) ↔ True
        simp [hx.1.ne']
    rw [measure_congr heq,measure_univ]
    exact zero_lt_one
  let q := ∫ x : ℝ, (1-x) ∂ν
  have hq0 : 0 ≤ q := integral_nonneg_of_ae (hs.mono fun x hx => sub_nonneg.mpr hx.2.le)
  have hq1 : q < 1 := by
    dsimp [q]
    rw [integral_sub (integrable_const _) hi]
    simpa using (sub_lt_self (1:ℝ) hip)
  have hr0 : ∀ n, ∀ᵐ U ∂μ, 0 ≤ remainder U n := by
    intro n
    exact hc.mono fun U hU => Finset.prod_nonneg fun i _ => sub_nonneg.mpr (hU i).2.le
  have hr1 : ∀ n, ∀ᵐ U ∂μ, remainder U n ≤ 1 := by
    intro n
    exact hc.mono fun U hU => Finset.prod_le_one (fun i _ => sub_nonneg.mpr (hU i).2.le)
      (fun i _ => by linarith [(hU i).1])
  have hrm : ∀ n, AEStronglyMeasurable (fun U => remainder U n) μ := by
    intro n
    apply Continuous.aestronglyMeasurable
    unfold remainder
    fun_prop
  have hri : ∀ n, Integrable (fun U => remainder U n) μ := by
    intro n
    apply (integrable_const (1:ℝ)).mono' (hrm n)
    filter_upwards [hr0 n,hr1 n] with U h0 h1
    simpa [Real.norm_eq_abs,abs_of_nonneg h0] using h1
  have hre : ∀ n, ∫ U, remainder U n ∂μ = q^n := by
    intro n
    have hh := integral_restrict_infinitePi (fun _ : ℕ => ν)
      (s := Finset.range n) (f := fun y => ∏ i, (1-y i : ℝ))
      (by apply Continuous.aestronglyMeasurable; fun_prop)
    rw [integral_fintype_prod_eq_prod] at hh
    have he : (fun U : ℕ → ℝ => ∏ i : Finset.range n, (1-U i : ℝ)) =
        (fun U => remainder U n) := by
      funext U
      exact Finset.prod_coe_sort (Finset.range n) (fun i => (1-U i))
    change (∫ U, ∏ i : Finset.range n, (1-U i : ℝ) ∂μ) = _ at hh
    rw [he] at hh
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_coe,Finset.card_range,q] using hh
  have hrnorm : ∀ n, ∫ U, ‖remainder U n‖ ∂μ = q^n := by
    intro n
    rw [integral_congr_ae ((hr0 n).mono fun U h => Real.norm_of_nonneg h)]
    exact hre n
  have hsumm : ∑' n, eLpNorm (fun U => remainder U n) 1 μ ≠ ⊤ := by
    have heq : ∀ n, eLpNorm (fun U => remainder U n) 1 μ = ENNReal.ofReal (q^n) := by
      intro n
      rw [eLpNorm_one_eq_lintegral_enorm,← ofReal_integral_norm_eq_lintegral_enorm (hri n),hrnorm]
    simp_rw [heq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => pow_nonneg hq0 n)
      (summable_geometric_of_lt_one hq0 hq1)]
    exact ENNReal.ofReal_ne_top
  have ha := summable_norm_of_tsum_eLpNorm_ne_top (μ := μ) (p := 1) (by rfl) hrm hsumm
  filter_upwards [hc,ha] with U hU hsum
  have hz : Tendsto (fun n => remainder U n) atTop (𝓝 0) := hsum.of_norm.tendsto_atTop_zero
  apply (hasSum_iff_tendsto_nat_of_nonneg (f := NestedCRP.stick U) (fun i =>
    mul_nonneg (hU i).1.le (Finset.prod_nonneg fun j _ => sub_nonneg.mpr (hU j).2.le)) 1).mpr
  simp_rw [partial_sum]
  simpa using tendsto_const_nhds.sub hz

end
end StickNormalization

theorem solution (H : NestedCRP.Hyper) :
    ∀ᵐ U ∂NestedCRP.gemLaw H.m H.pi, HasSum (NestedCRP.stick U) 1 := by
  letI := isProbabilityMeasureBeta (mul_pos H.m_pos H.pi_pos)
    (mul_pos (sub_pos.mpr H.m_lt_one) H.pi_pos)
  exact StickNormalization.iid_sticks _ (StickNormalization.beta_support _ _)

/-- If zero stick fractions are permitted, normalization can fail. -/
theorem zero_sticks_control : ¬ HasSum (NestedCRP.stick (fun _ => 0)) 1 := by
  intro h
  have hz : HasSum (NestedCRP.stick (fun _ => 0)) (0:ℝ) := by
    have he : NestedCRP.stick (fun _ => 0) = (fun _ : ℕ => (0:ℝ)) := by
      funext i
      simp [NestedCRP.stick]
    rw [he]
    exact hasSum_zero
  have hh := h.unique hz
  norm_num at hh
