-- Prove2me | solution 1 for NearlyUnstableHawkes.Heston.eq_11
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T04:52:47.297798+00:00
-- url     : https://prove2.me/submissions/4bee7e3a-983b-4228-819c-4ba1e4930d74

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Heston_Kernel
import Definitions.Def_NearlyUnstableHawkes_Heston_Setting

/-! U2 of the 7ade6a3f decomposition: the mass of the signed resolvent,
`1 + ∫_{Ioi 0} ψ^T = 1 / (1 - a ‖φ‖₁)`. Deterministic; no probability. -/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace P7ade6a3f
open NearlyUnstableHawkes.Heston NearlyUnstableHawkes.Deterministic

/-- `convPow f k` restricted to positive time. -/
noncomputable def cpI (f : ℝ → ℝ) (k : ℕ) : ℝ → ℝ := (Ioi (0:ℝ)).indicator (convPow f k)

lemma cpI_succ (f : ℝ → ℝ) (k : ℕ) :
    cpI f (k+1) = convolution (cpI f 0) (cpI f k) (ContinuousLinearMap.mul ℝ ℝ) volume := by
  funext x
  rw [convolution_def]
  by_cases hx : 0 < x
  · have h1 : cpI f (k+1) x = ∫ y in Ioc 0 x, f y * convPow f k (x - y) := by
      simp only [cpI, indicator_of_mem (show x ∈ Ioi (0:ℝ) from hx), convPow, conv]
      rw [intervalIntegral.integral_of_le hx.le]
      congr 1; funext y; ring
    have h2 : (fun y => (ContinuousLinearMap.mul ℝ ℝ) (cpI f 0 y) (cpI f k (x - y))) =
        (Ioo 0 x).indicator (fun y => f y * convPow f k (x - y)) := by
      funext y
      simp only [ContinuousLinearMap.mul_apply', cpI, convPow]
      by_cases hy : y ∈ Ioo 0 x
      · rw [indicator_of_mem hy, indicator_of_mem (show y ∈ Ioi (0:ℝ) from hy.1),
          indicator_of_mem (show x - y ∈ Ioi (0:ℝ) from sub_pos.2 hy.2)]
      · rw [indicator_of_notMem hy]
        simp only [mem_Ioo, not_and_or, not_lt] at hy
        rcases hy with hy | hy
        · rw [indicator_of_notMem (show y ∉ Ioi (0:ℝ) from not_lt.2 hy), zero_mul]
        · rw [indicator_of_notMem (show x - y ∉ Ioi (0:ℝ) by
            simp only [mem_Ioi, not_lt]; linarith), mul_zero]
    rw [h1, h2, integral_indicator measurableSet_Ioo, integral_Ioc_eq_integral_Ioo]
  · have h1 : cpI f (k+1) x = 0 := indicator_of_notMem hx _
    rw [h1]; symm
    refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
    simp only [ContinuousLinearMap.mul_apply', cpI, Pi.zero_apply]
    by_cases hy : 0 < y
    · rw [indicator_of_notMem (show x - y ∉ Ioi (0:ℝ) by
        simp only [mem_Ioi, not_lt]; linarith), mul_zero]
    · rw [indicator_of_notMem (show y ∉ Ioi (0:ℝ) from hy), zero_mul]

lemma lintegral_conv_le (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g) :
    ∫⁻ x, ‖convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume x‖ₑ ≤
      (∫⁻ x, ‖f x‖ₑ) * ∫⁻ x, ‖g x‖ₑ := by
  have hI := hf.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hg
  calc ∫⁻ x, ‖convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume x‖ₑ
      ≤ ∫⁻ x, ∫⁻ y, ‖f y‖ₑ * ‖g (x - y)‖ₑ := by
        refine lintegral_mono fun x => ?_
        rw [convolution_def]
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        congr 1; funext y; simp [ContinuousLinearMap.mul_apply', enorm_mul]
    _ = ∫⁻ y, ∫⁻ x, ‖f y‖ₑ * ‖g (x - y)‖ₑ := by
        refine lintegral_lintegral_swap ?_
        have := hI.aestronglyMeasurable.enorm
        refine this.congr (Eventually.of_forall fun p => ?_)
        simp [Function.uncurry, ContinuousLinearMap.mul_apply', enorm_mul]
    _ = ∫⁻ y, ‖f y‖ₑ * ∫⁻ x, ‖g x‖ₑ := by
        refine lintegral_congr fun y => ?_
        rw [lintegral_const_mul' _ _ enorm_ne_top,
          lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ) y]
    _ = (∫⁻ x, ‖f x‖ₑ) * ∫⁻ x, ‖g x‖ₑ := lintegral_mul_const' _ _ hg.2.ne

lemma cpI_int_mass (f : ℝ → ℝ) (hf : Integrable (cpI f 0)) : ∀ k : ℕ,
    Integrable (cpI f k) ∧ ∫ x, cpI f k x = (∫ x, cpI f 0 x) ^ (k+1) ∧
      ∫⁻ x, ‖cpI f k x‖ₑ ≤ (∫⁻ x, ‖cpI f 0 x‖ₑ) ^ (k+1)
  | 0 => ⟨hf, by simp, by simp⟩
  | k+1 => by
    obtain ⟨h1, h2, h3⟩ := cpI_int_mass f hf k
    rw [cpI_succ]
    refine ⟨hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) h1, ?_, ?_⟩
    · rw [integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf h1, h2,
        ContinuousLinearMap.mul_apply']
      ring
    · refine (lintegral_conv_le _ _ hf h1).trans ?_
      calc (∫⁻ x, ‖cpI f 0 x‖ₑ) * ∫⁻ x, ‖cpI f k x‖ₑ
          ≤ (∫⁻ x, ‖cpI f 0 x‖ₑ) * (∫⁻ x, ‖cpI f 0 x‖ₑ) ^ (k+1) := by gcongr
        _ = (∫⁻ x, ‖cpI f 0 x‖ₑ) ^ (k+1+1) := by ring

lemma lintegral_cpI (f : ℝ → ℝ) (k : ℕ) :
    ∫⁻ x, ‖cpI f k x‖ₑ = ∫⁻ x in Ioi (0:ℝ), ‖convPow f k x‖ₑ := by
  simp only [cpI, enorm_indicator_eq_indicator_enorm]
  exact lintegral_indicator measurableSet_Ioi _

lemma integral_cpI (f : ℝ → ℝ) (k : ℕ) :
    ∫ x, cpI f k x = ∫ x in Ioi (0:ℝ), convPow f k x :=
  integral_indicator measurableSet_Ioi

/-- Generic resolvent mass: for `f` with `∫_{Ioi 0} |f| < 1`,
`1 + ∫_{Ioi 0} Σ_k f^{*(k+1)} = 1/(1 - ∫_{Ioi 0} f)`. -/
lemma resolvent_mass (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0))
    (hlt : ∫⁻ x in Ioi (0:ℝ), ‖f x‖ₑ < 1) :
    1 + ∫ s in Ioi (0:ℝ), NearlyUnstableHawkes.Heston.resolvent f s = 1 / (1 - ∫ s in Ioi (0:ℝ), f s) := by
  have hf0 : Integrable (cpI f 0) := (integrable_indicator_iff measurableSet_Ioi).2 hf
  have H := cpI_int_mass f hf0
  set r := ∫⁻ x in Ioi (0:ℝ), ‖f x‖ₑ with hr_def
  have hr : ∫⁻ x, ‖cpI f 0 x‖ₑ = r := lintegral_cpI f 0
  set c := ∫ s in Ioi (0:ℝ), f s with hc_def
  have hc0 : ∫ x, cpI f 0 x = c := integral_cpI f 0
  have hcabs : |c| < 1 := by
    have h1 : ‖c‖ₑ ≤ r := enorm_integral_le_lintegral_enorm _
    have h2 : ‖c‖ₑ < 1 := lt_of_le_of_lt h1 hlt
    rw [Real.enorm_eq_ofReal_abs] at h2
    exact ENNReal.ofReal_lt_one.1 h2
  have hmeas : ∀ k, AEStronglyMeasurable (convPow f k) (volume.restrict (Ioi (0:ℝ))) := by
    intro k
    exact ((integrable_indicator_iff measurableSet_Ioi).1 (H k).1).aestronglyMeasurable
  have hsum : ∑' k, ∫⁻ x in Ioi (0:ℝ), ‖convPow f k x‖ₑ ≠ ∞ := by
    have hle : ∑' k, ∫⁻ x in Ioi (0:ℝ), ‖convPow f k x‖ₑ ≤ ∑' k : ℕ, r ^ (k+1) := by
      refine ENNReal.tsum_le_tsum fun k => ?_
      rw [← lintegral_cpI, ← hr]; exact (H k).2.2
    have hgeo : ∑' k : ℕ, r ^ (k+1) = r * (1 - r)⁻¹ := by
      simp_rw [pow_succ']
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ne_top_of_le_ne_top ?_ hle
    rw [hgeo]
    exact ENNReal.mul_ne_top (ne_top_of_lt hlt) (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hlt).ne')
  have hint : ∫ s in Ioi (0:ℝ), NearlyUnstableHawkes.Heston.resolvent f s = ∑' k : ℕ, c ^ (k+1) := by
    unfold NearlyUnstableHawkes.Heston.resolvent
    rw [integral_tsum hmeas hsum]
    congr 1; funext k
    rw [← integral_cpI, (H k).2.1, hc0]
  have hgeo : ∑' k : ℕ, c ^ (k+1) = c * (1 - c)⁻¹ := by
    simp_rw [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hcabs]
  have hne : (1:ℝ) - c ≠ 0 := by
    have := (abs_lt.1 hcabs).2; linarith
  rw [hint, hgeo]
  field_simp
  ring

lemma int₁' {φ₁ φ₂ : ℝ → ℝ} {m : ℝ} (h : KernelAssumption3 φ₁ φ₂ m) :
    IntegrableOn φ₁ (Ici 0) := by
  refine Integrable.mono' h.integrable h.meas₁.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun s (hs : 0 ≤ s) => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (h.nonneg₁ s hs)]
  linarith [h.nonneg₂ s hs]

lemma int₂' {φ₁ φ₂ : ℝ → ℝ} {m : ℝ} (h : KernelAssumption3 φ₁ φ₂ m) :
    IntegrableOn φ₂ (Ici 0) := by
  refine Integrable.mono' h.integrable h.meas₂.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun s (hs : 0 ≤ s) => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (h.nonneg₂ s hs)]
  linarith [h.nonneg₁ s hs]

/-- **U2** `psiSigned_mass`. -/
theorem psiSigned_mass (a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (m : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (h : KernelAssumption3 φ₁ φ₂ m) :
    1 + ∫ s in Ioi (0:ℝ), psiSigned a φ₁ φ₂ s = 1 / (1 - a * phiMass φ₁ φ₂) := by
  have h1 : IntegrableOn φ₁ (Ioi 0) := (int₁' h).mono_set Ioi_subset_Ici_self
  have h2 : IntegrableOn φ₂ (Ioi 0) := (int₂' h).mono_set Ioi_subset_Ici_self
  have hfeq : phiSignedT a φ₁ φ₂ = fun s => a * (φ₁ s - φ₂ s) := by
    funext s; simp only [phiSignedT]; ring
  have hfi : IntegrableOn (phiSignedT a φ₁ φ₂) (Ioi 0) := by
    rw [hfeq]; exact (h1.sub h2).const_mul a
  have hmass : ∫ s in Ioi (0:ℝ), phiSignedT a φ₁ φ₂ s = a * phiMass φ₁ φ₂ := by
    rw [hfeq, integral_const_mul, phiMass]
  have hsumI : IntegrableOn (fun s => a * (φ₁ s + φ₂ s)) (Ioi 0) := (h1.add h2).const_mul a
  have hlt : ∫⁻ x in Ioi (0:ℝ), ‖phiSignedT a φ₁ φ₂ x‖ₑ < 1 := by
    have hle : ∫⁻ x in Ioi (0:ℝ), ‖phiSignedT a φ₁ φ₂ x‖ₑ ≤
        ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (a * (φ₁ x + φ₂ x)) := by
      refine setLIntegral_mono' measurableSet_Ioi fun x (hx : 0 < x) => ?_
      rw [Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal (abs_le.2 ⟨?_, ?_⟩)
      · simp only [phiSignedT]
        nlinarith [h.nonneg₁ x hx.le, h.nonneg₂ x hx.le]
      · simp only [phiSignedT]
        nlinarith [h.nonneg₁ x hx.le, h.nonneg₂ x hx.le]
    have heq : ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (a * (φ₁ x + φ₂ x)) = ENNReal.ofReal a := by
      rw [← ofReal_integral_eq_lintegral_ofReal hsumI]
      · rw [integral_const_mul, ← integral_Ici_eq_integral_Ioi, h.mass_eq_one, mul_one]
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 0 < x) => ?_)
        exact mul_nonneg ha.le (add_nonneg (h.nonneg₁ x hx.le) (h.nonneg₂ x hx.le))
    refine lt_of_le_of_lt hle ?_
    rw [heq]; exact ENNReal.ofReal_lt_one.2 ha1
  rw [← hmass]
  exact resolvent_mass _ hfi hlt

/-- `1 - ‖φ‖₁ > 0` (copy of Basic.one_sub_phiMass_pos, self-contained here). -/
lemma one_sub_phiMass_pos' {φ₁ φ₂ : ℝ → ℝ} {m : ℝ} (h : KernelAssumption3 φ₁ φ₂ m) :
    0 < 1 - phiMass φ₁ φ₂ := by
  have h1 := int₁' h
  have h2 := int₂' h
  have hp : phiMass φ₁ φ₂ = (∫ s in Ici (0:ℝ), φ₁ s) - ∫ s in Ici (0:ℝ), φ₂ s := by
    rw [phiMass, ← integral_Ici_eq_integral_Ioi, integral_sub h1 h2]
  have hm : (∫ s in Ici (0:ℝ), φ₁ s) + ∫ s in Ici (0:ℝ), φ₂ s = 1 := by
    rw [← integral_add h1 h2]; exact h.mass_eq_one
  have hnn : 0 ≤ᵐ[volume.restrict (Ici (0:ℝ))] φ₂ :=
    (ae_restrict_iff' measurableSet_Ici).2
      (Eventually.of_forall fun s (hs : 0 ≤ s) => h.nonneg₂ s hs)
  have hpos : 0 < ∫ s in Ici (0:ℝ), φ₂ s := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hnn h2]
    have : Function.support φ₂ ∩ Ici 0 = {s : ℝ | 0 ≤ s ∧ φ₂ s ≠ 0} := by
      ext s; simp [Function.mem_support, and_comm]
    rw [this]; exact h.support₂
  rw [hp]; linarith

/-- **U3** `psiSigned_mass_tendsto`: `1 + ∫ψ^{T_n} → 1/(1 - ‖φ‖₁)` as `a_n → 1`. -/
theorem psiSigned_mass_tendsto (a : ℕ → ℝ) (φ₁ φ₂ : ℝ → ℝ) (m : ℝ)
    (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1) (hlim : Tendsto a atTop (𝓝 1))
    (h : KernelAssumption3 φ₁ φ₂ m) :
    Tendsto (fun n => 1 + ∫ s in Ioi (0:ℝ), psiSigned (a n) φ₁ φ₂ s) atTop
      (𝓝 (1 / (1 - phiMass φ₁ φ₂))) := by
  have heq : (fun n => 1 + ∫ s in Ioi (0:ℝ), psiSigned (a n) φ₁ φ₂ s) =
      fun n => 1 / (1 - a n * phiMass φ₁ φ₂) := by
    funext n; exact psiSigned_mass (a n) φ₁ φ₂ m (ha n) (ha1 n) h
  rw [heq]
  have hne : (1:ℝ) - 1 * phiMass φ₁ φ₂ ≠ 0 := by
    rw [one_mul]; exact (one_sub_phiMass_pos' h).ne'
  have ht := (tendsto_const_nhds (x := (1:ℝ))).div
    ((tendsto_const_nhds (x := (1:ℝ))).sub (hlim.mul_const (phiMass φ₁ φ₂))) hne
  rwa [one_mul] at ht

/-! ## Integrated resolvent equation `Ψ(y) = F(y) + ∫_0^y f(v) Ψ(y - v) dv` (used by D). -/

/-- `Ψ_k(z) = ∫_0^z f^{*(k+1)}`. -/
noncomputable def PsiK (f : ℝ → ℝ) (k : ℕ) (z : ℝ) : ℝ := ∫ s in (0:ℝ)..z, convPow f k s

/-- `Ψ(z) = ∫_0^z ψ` for the resolvent `ψ` of `f`. -/
noncomputable def PsiR (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..z, NearlyUnstableHawkes.Heston.resolvent f s

lemma intervalIntegral_cpI (f : ℝ → ℝ) (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    ∫ s in (0:ℝ)..z, cpI f k s = PsiK f k z := by
  rw [PsiK, intervalIntegral.integral_of_le hz, intervalIntegral.integral_of_le hz]
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  simp only [cpI, indicator_of_mem (show s ∈ Ioi (0:ℝ) from hs.1)]

lemma shift_cpI (f : ℝ → ℝ) (k : ℕ) (hk : Integrable (cpI f k)) {w y : ℝ} (hw : 0 ≤ w)
    (hy : 0 ≤ y) :
    ∫ s in (0:ℝ)..y, cpI f k (s - w) = if w ≤ y then PsiK f k (y - w) else 0 := by
  rw [intervalIntegral.integral_comp_sub_right (fun s => cpI f k s) w, zero_sub]
  have hz : ∀ a b : ℝ, a ≤ b → b ≤ 0 → ∫ s in a..b, cpI f k s = 0 := by
    intro a b hab hb
    rw [intervalIntegral.integral_of_le hab]
    refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
    exact indicator_of_notMem (show s ∉ Ioi (0:ℝ) by
      simp only [mem_Ioi, not_lt]; exact hs.2.trans hb) _
  split_ifs with hwy
  · rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hk.intervalIntegrable) (hk.intervalIntegrable), hz _ _ (by linarith) le_rfl, zero_add,
      intervalIntegral_cpI f k (by linarith)]
  · exact hz _ _ (by linarith) (by linarith)

lemma PsiK_succ (f : ℝ → ℝ) (hf0 : Integrable (cpI f 0)) (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    PsiK f (k+1) y = ∫ v in (0:ℝ)..y, f v * PsiK f k (y - v) := by
  have hk := (cpI_int_mass f hf0 k).1
  have hI := hf0.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hk
  simp only [ContinuousLinearMap.mul_apply'] at hI
  have hI' : Integrable (Function.uncurry fun s w => cpI f 0 w * cpI f k (s - w))
      ((volume.restrict (Ioc (0:ℝ) y)).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]; exact hI.restrict
  rw [← intervalIntegral_cpI f (k+1) hy, cpI_succ, intervalIntegral.integral_of_le hy]
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  rw [integral_integral_swap hI']
  have hH : (fun w => ∫ s in Ioc (0:ℝ) y, cpI f 0 w * cpI f k (s - w)) =
      (Ioc 0 y).indicator (fun v => f v * PsiK f k (y - v)) := by
    funext w
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hy]
    by_cases hw : 0 < w
    · rw [shift_cpI f k hk hw.le hy]
      have h0 : cpI f 0 w = f w := by
        simp only [cpI, indicator_of_mem (show w ∈ Ioi (0:ℝ) from hw), convPow]
      split_ifs with hwy
      · rw [indicator_of_mem (show w ∈ Ioc 0 y from ⟨hw, hwy⟩), h0]
      · rw [indicator_of_notMem (show w ∉ Ioc 0 y from fun h => hwy h.2), mul_zero]
    · rw [indicator_of_notMem (show w ∉ Ioc 0 y from fun h => hw h.1)]
      simp only [cpI, indicator_of_notMem (show w ∉ Ioi (0:ℝ) from hw), zero_mul]
  rw [hH, integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hy]

lemma PsiK_abs_le (f : ℝ → ℝ) (hf0 : Integrable (cpI f 0)) (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    ‖PsiK f k z‖ₑ ≤ (∫⁻ x, ‖cpI f 0 x‖ₑ) ^ (k+1) := by
  rw [← intervalIntegral_cpI f k hz, intervalIntegral.integral_of_le hz]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  exact (setLIntegral_le_lintegral _ _).trans (cpI_int_mass f hf0 k).2.2

lemma PsiK_norm_le (f : ℝ → ℝ) (hf0 : Integrable (cpI f 0)) (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    ‖PsiK f k z‖ ≤ ((∫⁻ x, ‖cpI f 0 x‖ₑ).toReal) ^ (k+1) := by
  have hfin : ∫⁻ x, ‖cpI f 0 x‖ₑ ≠ ∞ := hf0.2.ne
  have h := PsiK_abs_le f hf0 k hz
  rw [← ofReal_norm, ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_pow ENNReal.toReal_nonneg] at h
  exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg ENNReal.toReal_nonneg _)).1 h

lemma cpI_meas_Ioi (f : ℝ → ℝ) (hf0 : Integrable (cpI f 0)) (k : ℕ) :
    AEStronglyMeasurable (convPow f k) (volume.restrict (Ioi (0:ℝ))) :=
  ((integrable_indicator_iff measurableSet_Ioi).1 (cpI_int_mass f hf0 k).1).aestronglyMeasurable

lemma cpI_tsum_ne_top (f : ℝ → ℝ) (hf0 : Integrable (cpI f 0))
    (hlt : ∫⁻ x, ‖cpI f 0 x‖ₑ < 1) :
    ∑' k, ∫⁻ x in Ioi (0:ℝ), ‖convPow f k x‖ₑ ≠ ∞ := by
  set r := ∫⁻ x, ‖cpI f 0 x‖ₑ
  have hle : ∑' k, ∫⁻ x in Ioi (0:ℝ), ‖convPow f k x‖ₑ ≤ ∑' k : ℕ, r ^ (k+1) := by
    refine ENNReal.tsum_le_tsum fun k => ?_
    rw [← lintegral_cpI]; exact (cpI_int_mass f hf0 k).2.2
  have hgeo : ∑' k : ℕ, r ^ (k+1) = r * (1 - r)⁻¹ := by
    simp_rw [pow_succ']
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  refine ne_top_of_le_ne_top ?_ hle
  rw [hgeo]
  exact ENNReal.mul_ne_top (ne_top_of_lt hlt) (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hlt).ne')

lemma PsiR_eq_tsum (f : ℝ → ℝ) (hf0 : Integrable (cpI f 0))
    (hlt : ∫⁻ x, ‖cpI f 0 x‖ₑ < 1) {y : ℝ} (hy : 0 ≤ y) :
    PsiR f y = ∑' k, PsiK f k y := by
  have hsub : volume.restrict (Ioc (0:ℝ) y) ≤ volume.restrict (Ioi (0:ℝ)) :=
    Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
  rw [PsiR, intervalIntegral.integral_of_le hy]
  unfold NearlyUnstableHawkes.Heston.resolvent
  rw [integral_tsum (fun k => (cpI_meas_Ioi f hf0 k).mono_measure hsub)
    (ne_top_of_le_ne_top (cpI_tsum_ne_top f hf0 hlt)
      (ENNReal.tsum_le_tsum fun k => lintegral_mono' hsub le_rfl))]
  congr 1; funext k
  rw [PsiK, intervalIntegral.integral_of_le hy]

/-- Integrated resolvent equation. -/
theorem PsiR_resolvent_eq (f : ℝ → ℝ) (hf0 : Integrable (cpI f 0))
    (hlt : ∫⁻ x, ‖cpI f 0 x‖ₑ < 1) {y : ℝ} (hy : 0 ≤ y) :
    PsiR f y = (∫ s in (0:ℝ)..y, f s) + ∫ v in (0:ℝ)..y, f v * PsiR f (y - v) := by
  set ρ := (∫⁻ x, ‖cpI f 0 x‖ₑ).toReal with hρ
  have hρ0 : 0 ≤ ρ := ENNReal.toReal_nonneg
  have hρ1 : ρ < 1 := by
    have := ENNReal.toReal_strict_mono ENNReal.one_ne_top hlt
    simpa [hρ] using this
  have hsumm : ∀ z, 0 ≤ z → Summable fun k => PsiK f k z := by
    intro z hz
    refine Summable.of_norm_bounded (g := fun k : ℕ => ρ ^ (k+1)) ?_ fun k => PsiK_norm_le f hf0 k hz
    simp_rw [pow_succ']
    exact (summable_geometric_of_lt_one hρ0 hρ1).mul_left ρ
  rw [PsiR_eq_tsum f hf0 hlt hy, (hsumm y hy).tsum_eq_zero_add]
  congr 1
  simp_rw [PsiK_succ f hf0 _ hy]
  -- interchange the sum and the integral in `v`
  have hfI : IntegrableOn f (Ioc (0:ℝ) y) :=
    ((integrable_indicator_iff measurableSet_Ioi).1 hf0).mono_set Ioc_subset_Ioi_self
  have hcont : ∀ k, Continuous fun z => ∫ s in (0:ℝ)..z, cpI f k s := fun k =>
    intervalIntegral.continuous_primitive (fun _ _ => (cpI_int_mass f hf0 k).1.intervalIntegrable) 0
  have hEq : ∀ k, EqOn (fun v => f v * PsiK f k (y - v))
      (fun v => f v * ∫ s in (0:ℝ)..(y - v), cpI f k s) (Ioc 0 y) := by
    intro k v hv
    simp only [intervalIntegral_cpI f k (show 0 ≤ y - v by linarith [hv.2])]
  have hmeas : ∀ k, AEStronglyMeasurable (fun v => f v * PsiK f k (y - v))
      (volume.restrict (Ioc (0:ℝ) y)) := by
    intro k
    refine AEStronglyMeasurable.congr
      (f := fun v => f v * ∫ s in (0:ℝ)..(y - v), cpI f k s)
      (hfI.aestronglyMeasurable.mul (g := fun v => ∫ s in (0:ℝ)..(y - v), cpI f k s) ?_) ?_
    · exact ((hcont k).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · refine ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => ?_))
      exact (hEq k hv).symm
  set r := ∫⁻ x, ‖cpI f 0 x‖ₑ
  have hbound : ∀ k, ∫⁻ v in Ioc (0:ℝ) y, ‖f v * PsiK f k (y - v)‖ₑ ≤
      (∫⁻ v in Ioc (0:ℝ) y, ‖f v‖ₑ) * r ^ (k+1) := by
    intro k
    rw [← lintegral_mul_const' _ _ (ENNReal.pow_ne_top (ne_top_of_lt hlt))]
    refine setLIntegral_mono' measurableSet_Ioc fun v hv => ?_
    rw [enorm_mul]
    gcongr
    exact PsiK_abs_le f hf0 k (by linarith [hv.2])
  have hfin : ∑' k, ∫⁻ v in Ioc (0:ℝ) y, ‖f v * PsiK f k (y - v)‖ₑ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [ENNReal.tsum_mul_left]
    refine ENNReal.mul_ne_top hfI.2.ne ?_
    have hgeo : ∑' k : ℕ, r ^ (k+1) = r * (1 - r)⁻¹ := by
      simp_rw [pow_succ']
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    rw [hgeo]
    exact ENNReal.mul_ne_top (ne_top_of_lt hlt) (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hlt).ne')
  simp_rw [intervalIntegral.integral_of_le hy]
  rw [← integral_tsum hmeas hfin]
  refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
  have hyv : 0 ≤ y - v := by linarith [hv.2]
  rw [tsum_mul_left, PsiR_eq_tsum f hf0 hlt hyv]

/-! ## Integrability of the resolvent and the per-atom scalar identity (used by D). -/

theorem resolvent_integrableOn (f : ℝ → ℝ) (hf0 : Integrable (cpI f 0))
    (hlt : ∫⁻ x, ‖cpI f 0 x‖ₑ < 1) :
    IntegrableOn (NearlyUnstableHawkes.Heston.resolvent f) (Ioi 0) := by
  set μ := volume.restrict (Ioi (0:ℝ))
  have hmeas := cpI_meas_Ioi f hf0
  have hlin : ∫⁻ x, ∑' k, ‖convPow f k x‖ₑ ∂μ ≠ ∞ := by
    rw [lintegral_tsum fun k => (hmeas k).enorm]; exact cpI_tsum_ne_top f hf0 hlt
  have hae : ∀ᵐ x ∂μ, ∑' k, ‖convPow f k x‖ₑ < ∞ :=
    ae_lt_top' (AEMeasurable.ennreal_tsum fun k => (hmeas k).enorm) hlin
  have hsum : ∀ᵐ x ∂μ, Summable fun k => convPow f k x := by
    filter_upwards [hae] with x hx
    refine Summable.of_norm ?_
    simp only [enorm_eq_nnnorm] at hx
    have h2 := ENNReal.tsum_coe_ne_top_iff_summable.1 hx.ne
    exact NNReal.summable_coe.2 h2
  have hsm : AEStronglyMeasurable (NearlyUnstableHawkes.Heston.resolvent f) μ := by
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun n x => ∑ k ∈ Finset.range n, convPow f k x)
      (fun n => Finset.aestronglyMeasurable_fun_sum _ fun k _ => hmeas k) ?_
    filter_upwards [hsum] with x hx
    exact hx.hasSum.tendsto_sum_nat
  refine ⟨hsm, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun x => enorm_tsum_le_tsum_enorm) ?_
  exact lt_top_iff_ne_top.2 hlin

/-- `G(z) = ∫_{Ioi z} ψ = Ψ̄ − Ψ(z)` for `z ≥ 0`. -/
lemma tail_eq (f : ℝ → ℝ) (hf0 : Integrable (cpI f 0))
    (hlt : ∫⁻ x, ‖cpI f 0 x‖ₑ < 1) {z : ℝ} (hz : 0 ≤ z) :
    ∫ s in Ioi z, NearlyUnstableHawkes.Heston.resolvent f s =
      (∫ s in Ioi (0:ℝ), NearlyUnstableHawkes.Heston.resolvent f s) - PsiR f z := by
  have hI := resolvent_integrableOn f hf0 hlt
  have hU := setIntegral_union (Set.disjoint_left.2 fun x (h1 : x ∈ Ioc 0 z) (h2 : x ∈ Ioi z) =>
      not_lt.2 h1.2 h2) measurableSet_Ioi (hI.mono_set Ioc_subset_Ioi_self)
      (hI.mono_set (Ioi_subset_Ioi hz))
  rw [Ioc_union_Ioi_eq_Ioi hz] at hU
  rw [hU, PsiR, intervalIntegral.integral_of_le hz]; ring

/-- The per-atom scalar identity behind the price decomposition (D). -/
theorem atom_identity (f : ℝ → ℝ) (hf0 : Integrable (cpI f 0))
    (hlt : ∫⁻ x, ‖cpI f 0 x‖ₑ < 1) {y : ℝ} (hy : 0 ≤ y) :
    (1 + ∫ s in Ioi (0:ℝ), NearlyUnstableHawkes.Heston.resolvent f s) *
        (1 - ∫ v in (0:ℝ)..y, f v)
      - (∫ s in Ioi y, NearlyUnstableHawkes.Heston.resolvent f s)
      + (∫ v in (0:ℝ)..y, (∫ s in Ioi (y - v), NearlyUnstableHawkes.Heston.resolvent f s) * f v)
      = 1 := by
  set Ψb := ∫ s in Ioi (0:ℝ), NearlyUnstableHawkes.Heston.resolvent f s
  have hI := resolvent_integrableOn f hf0 hlt
  have hfI : IntervalIntegrable f volume 0 y := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hy]
    exact ((integrable_indicator_iff measurableSet_Ioi).1 hf0).mono_set Ioc_subset_Ioi_self
  have hcont : ContinuousOn (PsiR f) (uIcc 0 y) :=
    intervalIntegral.continuousOn_primitive_interval (by
      rw [uIcc_of_le hy, integrableOn_Icc_iff_integrableOn_Ioc]
      exact hI.mono_set Ioc_subset_Ioi_self)
  have hcont' : ContinuousOn (fun v => PsiR f (y - v)) (uIcc 0 y) := by
    refine hcont.comp (continuousOn_const.sub continuousOn_id) fun v hv => ?_
    rw [uIcc_of_le hy] at hv ⊢
    exact ⟨by linarith [hv.2], by linarith [hv.1]⟩
  have h1 : ∫ v in (0:ℝ)..y, (∫ s in Ioi (y - v), NearlyUnstableHawkes.Heston.resolvent f s) * f v
      = ∫ v in (0:ℝ)..y, (Ψb * f v - f v * PsiR f (y - v)) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le hy] at hv
    rw [tail_eq f hf0 hlt (show 0 ≤ y - v by linarith [hv.2])]; ring
  have h2 : IntervalIntegrable (fun v => f v * PsiR f (y - v)) volume 0 y := by
    have := hfI.continuousOn_mul hcont'
    exact this.congr fun v _ => mul_comm _ _
  rw [h1, intervalIntegral.integral_sub (hfI.const_mul Ψb) h2, intervalIntegral.integral_const_mul,
    tail_eq f hf0 hlt hy]
  have hR := PsiR_resolvent_eq f hf0 hlt hy
  rw [hR]
  ring



/-- The jump set of `x` in `(0, τ]`. -/
def jset (x : ℝ → ℝ) (τ : ℝ) : Set ℝ := {s | s ∈ Ioc 0 τ ∧ NearlyUnstableHawkes.Heston.jump x s ≠ 0}

lemma leftLim_of_const {x : ℝ → ℝ} {a s c : ℝ} (has : a < s) (h : ∀ u ∈ Ioo a s, x u = c) :
    Function.leftLim x s = c := by
  apply leftLim_eq_of_tendsto
  refine tendsto_const_nhds.congr' ?_
  exact Filter.mem_of_superset (Ioo_mem_nhdsLT has) fun u hu => (h u hu).symm

lemma jump_of_const {x : ℝ → ℝ} {a s c : ℝ} (has : a < s) (h : ∀ u ∈ Ioc a s, x u = c) :
    NearlyUnstableHawkes.Heston.jump x s = 0 := by
  rw [NearlyUnstableHawkes.Heston.jump,
    leftLim_of_const has (fun u hu => h u ⟨hu.1, hu.2.le⟩), h s ⟨has, le_rfl⟩, sub_self]

theorem jumps_count (g : ℝ → ℕ) (hmono : MonotoneOn g (Ici 0)) (h0 : g 0 = 0)
    (hrc : ∀ t, 0 ≤ t → ContinuousWithinAt (fun u => (g u : ℝ)) (Ici t) t) :
    ∀ n : ℕ, ∀ τ : ℝ, 0 ≤ τ → g τ = n →
      (jset (fun u => (g u : ℝ)) τ).Finite ∧
      ∑ᶠ s ∈ jset (fun u => (g u : ℝ)) τ, NearlyUnstableHawkes.Heston.jump (fun u => (g u : ℝ)) s
        = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro τ hτ hgτ
  set x : ℝ → ℝ := fun u => (g u : ℝ) with hx
  have hle : ∀ s ∈ Icc 0 τ, g s ≤ n := fun s hs => hgτ ▸ hmono hs.1 hτ hs.2
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- all values zero: no jumps
    have hz : ∀ s ∈ Icc 0 τ, g s = 0 := fun s hs => Nat.le_zero.1 (hn ▸ hle s hs)
    have hJ : jset x τ = ∅ := by
      ext s
      simp only [jset, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
      intro hs
      refine jump_of_const (c := 0) hs.1 fun u hu => ?_
      simp [hx, hz u ⟨hu.1.le, hu.2.trans hs.2⟩]
    rw [hJ, hn]; simp
  · -- first passage time to level n
    set A : Set ℝ := {s | s ∈ Icc 0 τ ∧ g s = n} with hA
    have hAne : A.Nonempty := ⟨τ, ⟨hτ, le_rfl⟩, hgτ⟩
    have hAbdd : BddBelow A := ⟨0, fun s hs => hs.1.1⟩
    set σ := sInf A with hσ
    have hσ0 : 0 ≤ σ := le_csInf hAne fun s hs => hs.1.1
    have hστ : σ ≤ τ := csInf_le hAbdd ⟨⟨hτ, le_rfl⟩, hgτ⟩
    have F1 : ∀ s ∈ Ioc σ τ, g s = n := by
      intro s hs
      obtain ⟨a, haA, has⟩ := exists_lt_of_csInf_lt hAne hs.1
      refine le_antisymm (hle s ⟨hσ0.trans hs.1.le, hs.2⟩) ?_
      rw [← haA.2]; exact hmono haA.1.1 (hσ0.trans hs.1.le) has.le
    have F2 : g σ = n := by
      rcases hστ.lt_or_eq with hlt | heq
      · have h1 : Tendsto x (𝓝[>] σ) (𝓝 (x σ)) := (hrc σ hσ0).mono Ioi_subset_Ici_self
        have h2 : Tendsto x (𝓝[>] σ) (𝓝 (n : ℝ)) := by
          refine tendsto_const_nhds.congr' ?_
          exact Filter.mem_of_superset (Ioo_mem_nhdsGT hlt) fun u hu =>
            (by simp [hx, F1 u ⟨hu.1, hu.2.le⟩])
        have := tendsto_nhds_unique h1 h2
        simp only [hx] at this
        exact_mod_cast this
      · rw [heq]; exact hgτ
    have F3 : ∀ s, 0 ≤ s → s < σ → g s < n := by
      intro s hs0 hsσ
      refine lt_of_le_of_ne (hle s ⟨hs0, hsσ.le.trans hστ⟩) fun hgs => ?_
      exact absurd (csInf_le hAbdd ⟨⟨hs0, hsσ.le.trans hστ⟩, hgs⟩) (not_le.2 hsσ)
    have hσpos : 0 < σ := by
      refine lt_of_le_of_ne hσ0 fun h => ?_
      rw [← h, h0] at F2; omega
    -- the level just before σ
    classical
    set S : Finset ℕ := (Finset.range n).filter (fun j => ∃ s ∈ Ico 0 σ, g s = j) with hS
    have h0S : 0 ∈ S := by
      simp only [hS, Finset.mem_filter, Finset.mem_range]
      exact ⟨hn, 0, ⟨le_rfl, hσpos⟩, h0⟩
    set m := S.max' ⟨0, h0S⟩ with hm
    have hmS : m ∈ S := Finset.max'_mem _ _
    simp only [hS, Finset.mem_filter, Finset.mem_range] at hmS
    obtain ⟨hmn, s₀, hs₀, hgs₀⟩ := hmS
    have hmax : ∀ s ∈ Ico 0 σ, g s ≤ m := by
      intro s hs
      refine Finset.le_max' _ _ ?_
      simp only [hS, Finset.mem_filter, Finset.mem_range]
      exact ⟨F3 s hs.1 hs.2, s, hs, rfl⟩
    have Fm : ∀ u ∈ Icc s₀ σ, u < σ → g u = m := by
      intro u hu huσ
      refine le_antisymm (hmax u ⟨hs₀.1.trans hu.1, huσ⟩) ?_
      rw [← hgs₀]; exact hmono hs₀.1 (hs₀.1.trans hu.1) hu.1
    obtain ⟨hfin, hsum⟩ := ih m hmn s₀ hs₀.1 hgs₀
    have hjσ : NearlyUnstableHawkes.Heston.jump x σ = (n : ℝ) - m := by
      rw [NearlyUnstableHawkes.Heston.jump, leftLim_of_const (c := (m : ℝ)) hs₀.2
        (fun u hu => by simp [hx, Fm u ⟨hu.1.le, hu.2.le⟩ hu.2])]
      simp [hx, F2]
    have hJ : jset x τ = insert σ (jset x s₀) := by
      ext s
      simp only [jset, mem_ofPred_eq, mem_insert_iff, mem_Ioc]
      constructor
      · rintro ⟨⟨hs0, hsτ⟩, hj⟩
        rcases le_or_gt s s₀ with hss | hss
        · exact Or.inr ⟨⟨hs0, hss⟩, hj⟩
        rcases lt_trichotomy s σ with hsσ | hsσ | hsσ
        · exact absurd (jump_of_const (c := (m : ℝ)) hss fun u hu => by
            simp [hx, Fm u ⟨hu.1.le, hu.2.trans hsσ.le⟩ (hu.2.trans_lt hsσ)]) hj
        · exact Or.inl hsσ
        · exact absurd (jump_of_const (c := (n : ℝ)) hsσ fun u hu => by
            simp [hx, F1 u ⟨hu.1, hu.2.trans hsτ⟩]) hj
      · rintro (hs | ⟨⟨hs0, hss⟩, hj⟩)
        · refine ⟨⟨hs ▸ hσpos, hs ▸ hστ⟩, ?_⟩
          rw [hs, hjσ]
          have : (m : ℝ) < n := by exact_mod_cast hmn
          linarith
        · exact ⟨⟨hs0, hss.trans (hs₀.2.le.trans hστ)⟩, hj⟩
    have hσnot : σ ∉ jset x s₀ := fun h => absurd h.1.2 (not_le.2 hs₀.2)
    refine ⟨hJ ▸ hfin.insert σ, ?_⟩
    rw [hJ, finsum_mem_insert _ hσnot hfin, hsum, hjσ]
    ring


/-! ## D step (b): jump sums as finite sums; (d1) atom integrals. -/

lemma jumpSum_eq_finset (x : ℝ → ℝ) (τ : ℝ) (hfin : (jset x τ).Finite) (k : ℝ → ℝ) {s : ℝ}
    (hs : s ≤ τ) :
    NearlyUnstableHawkes.Heston.jumpSumOn x k (Ioc 0 s) =
      ∑ u ∈ hfin.toFinset, if u ≤ s then NearlyUnstableHawkes.Heston.jump x u * k u else 0 := by
  rw [← Finset.sum_filter]
  have hset : {u | u ∈ Ioc 0 s ∧ NearlyUnstableHawkes.Heston.jump x u ≠ 0} =
      ↑(hfin.toFinset.filter (· ≤ s)) := by
    ext u
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, jset, mem_Ioc, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨h1, h2.trans hs⟩, h3⟩, h2⟩
    · rintro ⟨⟨⟨h1, _⟩, h3⟩, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩
  rw [← finsum_mem_coe_finset, ← hset]
  rfl

/-- One atom of a jump sum: `s ↦ 1_{u ≤ s} k(s − u)`. -/
noncomputable def atomK (k : ℝ → ℝ) (u s : ℝ) : ℝ := if u ≤ s then k (s - u) else 0

lemma atomK_ae (k : ℝ → ℝ) (u : ℝ) :
    ∀ᵐ s ∂(volume : Measure ℝ), atomK k u s = cpI k 0 (s - u) := by
  filter_upwards [Measure.ae_ne volume u] with s hs
  simp only [atomK, cpI, convPow]
  by_cases h : u ≤ s
  · rw [if_pos h, indicator_of_mem (show s - u ∈ Ioi (0:ℝ) from
      sub_pos.2 (lt_of_le_of_ne h (Ne.symm hs)))]
  · rw [if_neg h, indicator_of_notMem (show s - u ∉ Ioi (0:ℝ) by
      simp only [mem_Ioi, not_lt]; linarith [not_le.1 h])]

lemma atomK_intervalIntegrable (k : ℝ → ℝ) (hk : Integrable (cpI k 0)) (u a b : ℝ) :
    IntervalIntegrable (atomK k u) volume a b :=
  ((hk.comp_sub_right u).intervalIntegrable).congr_ae
    (ae_restrict_of_ae ((atomK_ae k u).mono fun _ hs => hs.symm))

lemma atom_integral (k : ℝ → ℝ) (hk : Integrable (cpI k 0)) {u τ : ℝ} (hu : 0 ≤ u)
    (huτ : u ≤ τ) :
    ∫ s in (0:ℝ)..τ, atomK k u s = ∫ v in (0:ℝ)..(τ - u), k v := by
  have hτ : 0 ≤ τ := hu.trans huτ
  rw [intervalIntegral.integral_congr_ae ((atomK_ae k u).mono fun s hs _ => hs),
    shift_cpI k 0 hk hu hτ, if_pos huτ]
  rfl

lemma atom_integral_mul (k : ℝ → ℝ) (hk : Integrable (cpI k 0)) (H : ℝ → ℝ) {u τ : ℝ}
    (hu : 0 ≤ u) (huτ : u ≤ τ) (hH : ContinuousOn H (Icc 0 τ)) :
    ∫ s in (0:ℝ)..τ, H s * atomK k u s = ∫ v in (0:ℝ)..(τ - u), H (v + u) * k v := by
  have hτ : 0 ≤ τ := hu.trans huτ
  rw [intervalIntegral.integral_congr_ae ((atomK_ae k u).mono fun s hs _ => by rw [hs])]
  have hF : (fun s => H s * cpI k 0 (s - u)) =
      fun s => (fun v => H (v + u) * cpI k 0 v) (s - u) := by
    funext s; simp only [sub_add_cancel]
  rw [hF, intervalIntegral.integral_comp_sub_right (fun v => H (v + u) * cpI k 0 v) u, zero_sub]
  have hHc : ContinuousOn (fun v => H (v + u)) (Icc (-u) (τ - u)) := by
    refine hH.comp (continuousOn_id.add continuousOn_const) fun v hv => ?_
    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hII : ∀ a b, -u ≤ a → a ≤ b → b ≤ τ - u →
      IntervalIntegrable (fun v => H (v + u) * cpI k 0 v) volume a b := by
    intro a b ha hab hb
    refine hk.intervalIntegrable.continuousOn_mul (hHc.mono ?_)
    rw [uIcc_of_le hab]; exact Icc_subset_Icc ha hb
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hII _ _ le_rfl (by linarith) (by linarith)) (hII _ _ (by linarith) (by linarith) le_rfl)]
  have hz : ∫ v in (-u)..0, H (v + u) * cpI k 0 v = 0 := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
    simp only [cpI, indicator_of_notMem (show v ∉ Ioi (0:ℝ) by
      simp only [mem_Ioi, not_lt]; exact hv.2), mul_zero]
  rw [hz, zero_add, intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_of_le (by linarith)]
  refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
  simp only [cpI, indicator_of_mem (show v ∈ Ioi (0:ℝ) from hv.1), convPow]

/-- An intensity on `[0, τ]` as `μ` plus finite atom sums. -/
lemma lam_eq (μ : ℝ) (k₁ k₂ : ℝ → ℝ) (xs xo : ℝ → ℝ) (τ : ℝ) (hsf : (jset xs τ).Finite)
    (hof : (jset xo τ).Finite) {s : ℝ} (hs : s ≤ τ) :
    NearlyUnstableHawkes.Heston.intensity μ k₁ k₂ xs xo s =
      μ + ∑ u ∈ hsf.toFinset, NearlyUnstableHawkes.Heston.jump xs u * atomK k₁ u s
        + ∑ u ∈ hof.toFinset, NearlyUnstableHawkes.Heston.jump xo u * atomK k₂ u s := by
  unfold NearlyUnstableHawkes.Heston.intensity
  rw [jumpSum_eq_finset xs τ hsf _ hs, jumpSum_eq_finset xo τ hof _ hs]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [atomK]; split_ifs <;> simp
  · refine Finset.sum_congr rfl fun u _ => ?_
    simp only [atomK]; split_ifs <;> simp

/-- `λ⁺ − λ⁻` on `[0, τ]`: `μ` cancels and the kernel becomes `φ^T = aφ₁ − aφ₂`. -/
lemma lam_diff (μ a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (xp xm : ℝ → ℝ) (τ : ℝ) (hp : (jset xp τ).Finite)
    (hm : (jset xm τ).Finite) {s : ℝ} (hs : s ≤ τ) :
    NearlyUnstableHawkes.Heston.intensity μ (fun s => a * φ₁ s) (fun s => a * φ₂ s) xp xm s -
      NearlyUnstableHawkes.Heston.intensity μ (fun s => a * φ₁ s) (fun s => a * φ₂ s) xm xp s =
      ∑ u ∈ hp.toFinset, NearlyUnstableHawkes.Heston.jump xp u * atomK (phiSignedT a φ₁ φ₂) u s
        - ∑ u ∈ hm.toFinset,
            NearlyUnstableHawkes.Heston.jump xm u * atomK (phiSignedT a φ₁ φ₂) u s := by
  rw [lam_eq μ _ _ xp xm τ hp hm hs, lam_eq μ _ _ xm xp τ hm hp hs]
  have e1 : ∀ (x : ℝ → ℝ) (J : Finset ℝ),
      ∑ u ∈ J, NearlyUnstableHawkes.Heston.jump x u * atomK (phiSignedT a φ₁ φ₂) u s =
        ∑ u ∈ J, NearlyUnstableHawkes.Heston.jump x u * atomK (fun s => a * φ₁ s) u s -
          ∑ u ∈ J, NearlyUnstableHawkes.Heston.jump x u * atomK (fun s => a * φ₂ s) u s := by
    intro x J
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [atomK, phiSignedT]; split_ifs <;> ring
  rw [e1, e1]; ring

/-! ## D assembly: `price_decomposition` -/

/-- Integrability facts for the kernel `φ^T = aφ₁ − aφ₂` (as in `psiSigned_mass`). -/
lemma phiSignedT_facts (a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (m : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (h : KernelAssumption3 φ₁ φ₂ m) :
    Integrable (cpI (phiSignedT a φ₁ φ₂) 0) ∧ ∫⁻ x, ‖cpI (phiSignedT a φ₁ φ₂) 0 x‖ₑ < 1 := by
  have h1 : IntegrableOn φ₁ (Ioi 0) := (int₁' h).mono_set Ioi_subset_Ici_self
  have h2 : IntegrableOn φ₂ (Ioi 0) := (int₂' h).mono_set Ioi_subset_Ici_self
  have hfeq : phiSignedT a φ₁ φ₂ = fun s => a * (φ₁ s - φ₂ s) := by
    funext s; simp only [phiSignedT]; ring
  have hfi : IntegrableOn (phiSignedT a φ₁ φ₂) (Ioi 0) := by
    rw [hfeq]; exact (h1.sub h2).const_mul a
  have hsumI : IntegrableOn (fun s => a * (φ₁ s + φ₂ s)) (Ioi 0) := (h1.add h2).const_mul a
  have hlt : ∫⁻ x in Ioi (0:ℝ), ‖phiSignedT a φ₁ φ₂ x‖ₑ < 1 := by
    have hle : ∫⁻ x in Ioi (0:ℝ), ‖phiSignedT a φ₁ φ₂ x‖ₑ ≤
        ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (a * (φ₁ x + φ₂ x)) := by
      refine setLIntegral_mono' measurableSet_Ioi fun x (hx : 0 < x) => ?_
      rw [Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal (abs_le.2 ⟨?_, ?_⟩)
      · simp only [phiSignedT]
        nlinarith [h.nonneg₁ x hx.le, h.nonneg₂ x hx.le]
      · simp only [phiSignedT]
        nlinarith [h.nonneg₁ x hx.le, h.nonneg₂ x hx.le]
    have heq : ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (a * (φ₁ x + φ₂ x)) = ENNReal.ofReal a := by
      rw [← ofReal_integral_eq_lintegral_ofReal hsumI]
      · rw [integral_const_mul, ← integral_Ici_eq_integral_Ioi, h.mass_eq_one, mul_one]
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 0 < x) => ?_)
        exact mul_nonneg ha.le (add_nonneg (h.nonneg₁ x hx.le) (h.nonneg₂ x hx.le))
    refine lt_of_le_of_lt hle ?_
    rw [heq]; exact ENNReal.ofReal_lt_one.2 ha1
  exact ⟨(integrable_indicator_iff measurableSet_Ioi).2 hfi, (lintegral_cpI _ 0).trans_lt hlt⟩

/-- `a φᵢ` restricted to positive time is integrable. -/
lemma cpI_const_mul_int (a : ℝ) (φ : ℝ → ℝ) (hφ : IntegrableOn φ (Ici 0)) :
    Integrable (cpI (fun s => a * φ s) 0) :=
  (integrable_indicator_iff measurableSet_Ioi).2
    ((hφ.mono_set Ioi_subset_Ici_self).const_mul a)

/-- A finite atom sum is interval integrable. -/
lemma sum_atom_ii (k : ℝ → ℝ) (hk : Integrable (cpI k 0)) (c : ℝ → ℝ) (a b : ℝ) :
    ∀ J : Finset ℝ, IntervalIntegrable (fun s => ∑ u ∈ J, c u * atomK k u s) volume a b := by
  intro J
  induction J using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact intervalIntegrable_const
  | insert u J hu ih =>
    simp only [Finset.sum_insert hu]
    exact ((atomK_intervalIntegrable k hk u a b).const_mul (c u)).add ih

/-- An intensity is interval integrable on `[0, τ]`. -/
lemma intensity_ii (μ : ℝ) (k₁ k₂ : ℝ → ℝ) (hk₁ : Integrable (cpI k₁ 0))
    (hk₂ : Integrable (cpI k₂ 0)) (xs xo : ℝ → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hsf : (jset xs τ).Finite) (hof : (jset xo τ).Finite) :
    IntervalIntegrable (fun s => NearlyUnstableHawkes.Heston.intensity μ k₁ k₂ xs xo s)
      volume 0 τ := by
  have hS : IntervalIntegrable (fun s => μ
      + ∑ u ∈ hsf.toFinset, NearlyUnstableHawkes.Heston.jump xs u * atomK k₁ u s
      + ∑ u ∈ hof.toFinset, NearlyUnstableHawkes.Heston.jump xo u * atomK k₂ u s) volume 0 τ :=
    (intervalIntegrable_const.add (sum_atom_ii k₁ hk₁ _ 0 τ _)).add (sum_atom_ii k₂ hk₂ _ 0 τ _)
  refine hS.congr ?_
  rw [uIoc_of_le hτ]
  exact fun s hs => (lam_eq μ k₁ k₂ xs xo τ hsf hof hs.2).symm

/-- Per-family core identity: `(1+Ψ̄)(Σc − ∫Σ c·atom) − (Σ c H − ∫ H Σ c·atom) = Σ c`. -/
lemma atom_core (f : ℝ → ℝ) (hf0 : Integrable (cpI f 0)) (hlt : ∫⁻ x, ‖cpI f 0 x‖ₑ < 1)
    (τ : ℝ) (hτ : 0 ≤ τ) (J : Finset ℝ) (hJ : ∀ u ∈ J, u ∈ Ioc 0 τ) (c : ℝ → ℝ) (H : ℝ → ℝ)
    (hHc : ContinuousOn H (Icc 0 τ))
    (hH : ∀ s, H s = ∫ r in Ioi (τ - s), NearlyUnstableHawkes.Heston.resolvent f r) :
    (1 + ∫ s in Ioi (0:ℝ), NearlyUnstableHawkes.Heston.resolvent f s) *
        (∑ u ∈ J, c u - ∫ s in (0:ℝ)..τ, ∑ u ∈ J, c u * atomK f u s)
      - (∑ u ∈ J, c u * H u - ∫ s in (0:ℝ)..τ, H s * ∑ u ∈ J, c u * atomK f u s)
      = ∑ u ∈ J, c u := by
  set A := 1 + ∫ s in Ioi (0:ℝ), NearlyUnstableHawkes.Heston.resolvent f s
  have hI : ∀ u, IntervalIntegrable (fun s => c u * atomK f u s) volume 0 τ :=
    fun u => (atomK_intervalIntegrable f hf0 u 0 τ).const_mul (c u)
  have hHc' : ContinuousOn H (uIcc 0 τ) := by rwa [uIcc_of_le hτ]
  have hII : ∀ u, IntervalIntegrable (fun s => H s * (c u * atomK f u s)) volume 0 τ :=
    fun u => (hI u).continuousOn_mul hHc'
  have e1 : ∫ s in (0:ℝ)..τ, ∑ u ∈ J, c u * atomK f u s =
      ∑ u ∈ J, c u * ∫ v in (0:ℝ)..(τ - u), f v := by
    rw [intervalIntegral.integral_finsetSum fun u _ => hI u]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [intervalIntegral.integral_const_mul, atom_integral f hf0 (hJ u hu).1.le (hJ u hu).2]
  have e2 : ∫ s in (0:ℝ)..τ, H s * ∑ u ∈ J, c u * atomK f u s =
      ∑ u ∈ J, c u * ∫ v in (0:ℝ)..(τ - u),
        (∫ r in Ioi ((τ - u) - v), NearlyUnstableHawkes.Heston.resolvent f r) * f v := by
    simp_rw [Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum fun u _ => hII u]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hfun : (fun s => H s * (c u * atomK f u s)) = fun s => c u * (H s * atomK f u s) := by
      funext s; ring
    rw [hfun, intervalIntegral.integral_const_mul,
      atom_integral_mul f hf0 H (hJ u hu).1.le (hJ u hu).2 hHc]
    congr 1
    refine intervalIntegral.integral_congr fun v _ => ?_
    rw [hH (v + u), show τ - (v + u) = τ - u - v by ring]
  have key : ∀ u ∈ J, c u = c u * (A * (1 - ∫ v in (0:ℝ)..(τ - u), f v) - H u
      + ∫ v in (0:ℝ)..(τ - u),
        (∫ r in Ioi ((τ - u) - v), NearlyUnstableHawkes.Heston.resolvent f r) * f v) := by
    intro u hu
    rw [hH u, atom_identity f hf0 hlt (sub_nonneg.2 (hJ u hu).2), mul_one]
  have hexp : ∑ u ∈ J, c u * (A * (1 - ∫ v in (0:ℝ)..(τ - u), f v) - H u
      + ∫ v in (0:ℝ)..(τ - u),
        (∫ r in Ioi ((τ - u) - v), NearlyUnstableHawkes.Heston.resolvent f r) * f v) =
      A * (∑ u ∈ J, c u - ∑ u ∈ J, c u * ∫ v in (0:ℝ)..(τ - u), f v)
        - (∑ u ∈ J, c u * H u - ∑ u ∈ J, c u * ∫ v in (0:ℝ)..(τ - u),
          (∫ r in Ioi ((τ - u) - v), NearlyUnstableHawkes.Heston.resolvent f r) * f v) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  rw [e1, e2, ← hexp]
  exact (Finset.sum_congr rfl key).symm

/-- Pathwise decomposition identity (generic, before rescaling by `T`). -/
lemma decomp_path (f : ℝ → ℝ) (hf0 : Integrable (cpI f 0)) (hlt : ∫⁻ x, ‖cpI f 0 x‖ₑ < 1)
    (τ : ℝ) (hτ : 0 ≤ τ) (xp xm : ℝ → ℝ) (hp : (jset xp τ).Finite) (hm : (jset xm τ).Finite)
    (hxp : xp τ = ∑ u ∈ hp.toFinset, NearlyUnstableHawkes.Heston.jump xp u)
    (hxm : xm τ = ∑ u ∈ hm.toFinset, NearlyUnstableHawkes.Heston.jump xm u)
    (lp lm : ℝ → ℝ) (hlp : IntervalIntegrable lp volume 0 τ)
    (hlm : IntervalIntegrable lm volume 0 τ)
    (hdiff : ∀ s ≤ τ, lp s - lm s =
      ∑ u ∈ hp.toFinset, NearlyUnstableHawkes.Heston.jump xp u * atomK f u s
        - ∑ u ∈ hm.toFinset, NearlyUnstableHawkes.Heston.jump xm u * atomK f u s)
    (H : ℝ → ℝ) (hHc : ContinuousOn H (Icc 0 τ))
    (hH : ∀ s, H s = ∫ r in Ioi (τ - s), NearlyUnstableHawkes.Heston.resolvent f r) :
    xp τ - xm τ =
      (1 + ∫ s in Ioi (0:ℝ), NearlyUnstableHawkes.Heston.resolvent f s) *
          (xp τ - (∫ s in (0:ℝ)..τ, lp s) - (xm τ - ∫ s in (0:ℝ)..τ, lm s))
        - ((NearlyUnstableHawkes.Heston.jumpSumOn xp H (Ioc 0 τ) - ∫ s in (0:ℝ)..τ, H s * lp s)
          - (NearlyUnstableHawkes.Heston.jumpSumOn xm H (Ioc 0 τ)
              - ∫ s in (0:ℝ)..τ, H s * lm s)) := by
  set A := 1 + ∫ s in Ioi (0:ℝ), NearlyUnstableHawkes.Heston.resolvent f s
  have hJp : ∀ u ∈ hp.toFinset, u ∈ Ioc 0 τ := fun u hu => ((Set.Finite.mem_toFinset hp).1 hu).1
  have hJm : ∀ u ∈ hm.toFinset, u ∈ Ioc 0 τ := fun u hu => ((Set.Finite.mem_toFinset hm).1 hu).1
  have cp := atom_core f hf0 hlt τ hτ hp.toFinset hJp (NearlyUnstableHawkes.Heston.jump xp) H hHc hH
  have cm := atom_core f hf0 hlt τ hτ hm.toFinset hJm (NearlyUnstableHawkes.Heston.jump xm) H hHc hH
  have hsp : NearlyUnstableHawkes.Heston.jumpSumOn xp H (Ioc 0 τ) =
      ∑ u ∈ hp.toFinset, NearlyUnstableHawkes.Heston.jump xp u * H u := by
    rw [jumpSum_eq_finset xp τ hp H le_rfl]
    exact Finset.sum_congr rfl fun u hu => if_pos (hJp u hu).2
  have hsm : NearlyUnstableHawkes.Heston.jumpSumOn xm H (Ioc 0 τ) =
      ∑ u ∈ hm.toFinset, NearlyUnstableHawkes.Heston.jump xm u * H u := by
    rw [jumpSum_eq_finset xm τ hm H le_rfl]
    exact Finset.sum_congr rfl fun u hu => if_pos (hJm u hu).2
  have hSp := sum_atom_ii f hf0 (NearlyUnstableHawkes.Heston.jump xp) 0 τ hp.toFinset
  have hSm := sum_atom_ii f hf0 (NearlyUnstableHawkes.Heston.jump xm) 0 τ hm.toFinset
  have hHc' : ContinuousOn H (uIcc 0 τ) := by rwa [uIcc_of_le hτ]
  have hle : ∀ s ∈ uIcc (0:ℝ) τ, s ≤ τ := fun s hs => by rw [uIcc_of_le hτ] at hs; exact hs.2
  have hint1 : (∫ s in (0:ℝ)..τ, lp s) - (∫ s in (0:ℝ)..τ, lm s) =
      (∫ s in (0:ℝ)..τ, ∑ u ∈ hp.toFinset, NearlyUnstableHawkes.Heston.jump xp u * atomK f u s)
      - ∫ s in (0:ℝ)..τ, ∑ u ∈ hm.toFinset, NearlyUnstableHawkes.Heston.jump xm u * atomK f u s := by
    rw [← intervalIntegral.integral_sub hlp hlm, ← intervalIntegral.integral_sub hSp hSm]
    exact intervalIntegral.integral_congr fun s hs => hdiff s (hle s hs)
  have hint2 : (∫ s in (0:ℝ)..τ, H s * lp s) - (∫ s in (0:ℝ)..τ, H s * lm s) =
      (∫ s in (0:ℝ)..τ,
          H s * ∑ u ∈ hp.toFinset, NearlyUnstableHawkes.Heston.jump xp u * atomK f u s)
      - ∫ s in (0:ℝ)..τ,
          H s * ∑ u ∈ hm.toFinset, NearlyUnstableHawkes.Heston.jump xm u * atomK f u s := by
    rw [← intervalIntegral.integral_sub (hlp.continuousOn_mul hHc') (hlm.continuousOn_mul hHc'),
      ← intervalIntegral.integral_sub (hSp.continuousOn_mul hHc') (hSm.continuousOn_mul hHc')]
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [← mul_sub, hdiff s (hle s hs)]
  rw [hsp, hsm, hxp, hxm]
  linear_combination cm - cp + A * hint1 - hint2

/-- **D** `price_decomposition` (pathwise, pp. 27 and 30). -/
theorem price_decomposition {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ a Tn m : ℝ)
    (φ₁ φ₂ : ℝ → ℝ) (Np Nm : ℝ → Ω → ℕ) (ha : 0 < a) (ha1 : a < 1)
    (hK : KernelAssumption3 φ₁ φ₂ m) (hT : 0 < Tn) (_hμ : 0 < μ)
    (hH2 : IsHawkes2 P μ (fun s => a * φ₁ s) (fun s => a * φ₂ s) Tn Np Nm) :
    ∀ ω, ∀ t ∈ Icc (0:ℝ) 1,
      priceProc Tn Np Nm t ω =
        (1 + ∫ s in Ioi (0:ℝ), psiSigned a φ₁ φ₂ s) * MbarDiff Tn μ a φ₁ φ₂ Np Nm t ω
          - remainderR Tn μ a φ₁ φ₂ Np Nm t ω := by
  intro ω t ht
  obtain ⟨hf0, hlt⟩ := phiSignedT_facts a φ₁ φ₂ m ha ha1 hK
  set f := phiSignedT a φ₁ φ₂ with hf_def
  set τ := Tn * t with hτ_def
  have hτ : 0 ≤ τ := mul_nonneg hT.le ht.1
  obtain ⟨hp, hxp'⟩ := jumps_count (fun u => Np u ω) (hH2.countPlus.mono ω) (hH2.countPlus.zero ω)
    (fun s hs => hH2.countPlus.rcont ω s hs) (Np τ ω) τ hτ rfl
  obtain ⟨hm, hxm'⟩ := jumps_count (fun u => Nm u ω) (hH2.countMinus.mono ω)
    (hH2.countMinus.zero ω) (fun s hs => hH2.countMinus.rcont ω s hs) (Nm τ ω) τ hτ rfl
  have hp' : (jset (path Np ω) τ).Finite := hp
  have hm' : (jset (path Nm ω) τ).Finite := hm
  have hxp : path Np ω τ = ∑ u ∈ hp'.toFinset, jump (path Np ω) u := by
    rw [← finsum_mem_eq_finite_toFinset_sum]; exact hxp'.symm
  have hxm : path Nm ω τ = ∑ u ∈ hm'.toFinset, jump (path Nm ω) u := by
    rw [← finsum_mem_eq_finite_toFinset_sum]; exact hxm'.symm
  have hk₁ := cpI_const_mul_int a φ₁ (int₁' hK)
  have hk₂ := cpI_const_mul_int a φ₂ (int₂' hK)
  have hlp := intensity_ii μ _ _ hk₁ hk₂ (path Np ω) (path Nm ω) τ hτ hp' hm'
  have hlm := intensity_ii μ _ _ hk₁ hk₂ (path Nm ω) (path Np ω) τ hτ hm' hp'
  set H : ℝ → ℝ := fun s =>
    ∫ r in Ioi (Tn * (t - s / Tn)), NearlyUnstableHawkes.Heston.resolvent f r with hH_def
  have hH : ∀ s, H s = ∫ r in Ioi (τ - s), NearlyUnstableHawkes.Heston.resolvent f r := by
    intro s
    have e : Tn * (t - s / Tn) = τ - s := by rw [hτ_def]; field_simp
    simp only [hH_def, e]
  have hψ := resolvent_integrableOn f hf0 hlt
  have hψI : IntegrableOn (NearlyUnstableHawkes.Heston.resolvent f) (uIcc 0 τ) := by
    rw [uIcc_of_le hτ]
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hψ.mono_set Ioc_subset_Ioi_self
  have hprim := intervalIntegral.continuousOn_primitive_interval hψI
  have hG : ContinuousOn (fun s => (∫ r in Ioi (0:ℝ), NearlyUnstableHawkes.Heston.resolvent f r)
      - PsiR f (τ - s)) (Icc 0 τ) := by
    refine continuousOn_const.sub (hprim.comp (continuousOn_const.sub continuousOn_id) ?_)
    intro s hs
    have hmem : τ - s ∈ Icc 0 τ := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    rw [uIcc_of_le hτ]
    exact hmem
  have hHc : ContinuousOn H (Icc 0 τ) := by
    refine hG.congr fun s hs => ?_
    rw [hH s, tail_eq f hf0 hlt (sub_nonneg.2 hs.2)]
  have E := decomp_path f hf0 hlt τ hτ (path Np ω) (path Nm ω) hp' hm' hxp hxm
    (fun s => lamPlus μ a φ₁ φ₂ Np Nm s ω) (fun s => lamMinus μ a φ₁ φ₂ Np Nm s ω) hlp hlm
    (fun s hs => lam_diff μ a φ₁ φ₂ (path Np ω) (path Nm ω) τ hp' hm' hs) H hHc hH
  simp only [priceProc, MbarDiff, MPlus, MMinus, remainderR, intDiffMbar, intDiffM, intDM]
  rw [← mul_div_assoc, ← sub_div]
  exact congrArg (· / Tn) E


/-! ## eq. (11): `N⁺_t − N⁻_t = ∫_0^t (1 + Ψ(t − u)) (dM⁺ − dM⁻)_u` -/

/-- `s ↦ Ψ(τ − s)` is continuous on `[0, τ]`. -/
lemma PsiR_contOn (f : ℝ → ℝ) (hf0 : Integrable (cpI f 0)) (hlt : ∫⁻ x, ‖cpI f 0 x‖ₑ < 1)
    {τ : ℝ} (hτ : 0 ≤ τ) : ContinuousOn (fun s => PsiR f (τ - s)) (Icc 0 τ) := by
  have hψ := resolvent_integrableOn f hf0 hlt
  have hψI : IntegrableOn (NearlyUnstableHawkes.Heston.resolvent f) (uIcc 0 τ) := by
    rw [uIcc_of_le hτ, integrableOn_Icc_iff_integrableOn_Ioc]
    exact hψ.mono_set Ioc_subset_Ioi_self
  have hprim := intervalIntegral.continuousOn_primitive_interval hψI
  refine hprim.comp (continuousOn_const.sub continuousOn_id) ?_
  intro s hs
  have hmem : τ - s ∈ Icc 0 τ := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  rw [uIcc_of_le hτ]
  exact hmem

/-- Per-atom identity for (11): `1 + Ψ(y) − ∫_0^y (1 + Ψ(y − v)) f(v) dv = 1`. -/
lemma psi_atom (f : ℝ → ℝ) (hf0 : Integrable (cpI f 0)) (hlt : ∫⁻ x, ‖cpI f 0 x‖ₑ < 1)
    {y : ℝ} (hy : 0 ≤ y) :
    1 + PsiR f y - ∫ v in (0:ℝ)..y, (1 + PsiR f (y - v)) * f v = 1 := by
  set Ψb := ∫ s in Ioi (0:ℝ), NearlyUnstableHawkes.Heston.resolvent f s
  have hA := atom_identity f hf0 hlt hy
  have hfI : IntervalIntegrable f volume 0 y :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).2
      (((integrable_indicator_iff measurableSet_Ioi).1 hf0).mono_set Ioc_subset_Ioi_self)
  have hc : ContinuousOn (fun v => PsiR f (y - v)) (uIcc 0 y) := by
    rw [uIcc_of_le hy]; exact PsiR_contOn f hf0 hlt hy
  have hPf : IntervalIntegrable (fun v => PsiR f (y - v) * f v) volume 0 y :=
    hfI.continuousOn_mul hc
  have hG : ∫ v in (0:ℝ)..y,
      (∫ s in Ioi (y - v), NearlyUnstableHawkes.Heston.resolvent f s) * f v =
      Ψb * (∫ v in (0:ℝ)..y, f v) - ∫ v in (0:ℝ)..y, PsiR f (y - v) * f v := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (hfI.const_mul Ψb) hPf]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le hy] at hv
    rw [tail_eq f hf0 hlt (sub_nonneg.2 hv.2)]
    ring
  have h1 : ∫ v in (0:ℝ)..y, (1 + PsiR f (y - v)) * f v =
      (∫ v in (0:ℝ)..y, f v) + ∫ v in (0:ℝ)..y, PsiR f (y - v) * f v := by
    rw [← intervalIntegral.integral_add hfI hPf]
    refine intervalIntegral.integral_congr fun v _ => ?_
    ring
  rw [tail_eq f hf0 hlt hy, hG] at hA
  rw [h1]
  linear_combination hA

/-- Per-family core for (11). -/
lemma atom_core11 (f : ℝ → ℝ) (hf0 : Integrable (cpI f 0)) (hlt : ∫⁻ x, ‖cpI f 0 x‖ₑ < 1)
    (τ : ℝ) (hτ : 0 ≤ τ) (J : Finset ℝ) (hJ : ∀ u ∈ J, u ∈ Ioc 0 τ) (c : ℝ → ℝ) :
    (∑ u ∈ J, c u * (1 + PsiR f (τ - u))
      - ∫ s in (0:ℝ)..τ, (1 + PsiR f (τ - s)) * ∑ u ∈ J, c u * atomK f u s)
      = ∑ u ∈ J, c u := by
  have hHc : ContinuousOn (fun s => 1 + PsiR f (τ - s)) (Icc 0 τ) :=
    continuousOn_const.add (PsiR_contOn f hf0 hlt hτ)
  have hI : ∀ u, IntervalIntegrable (fun s => c u * atomK f u s) volume 0 τ :=
    fun u => (atomK_intervalIntegrable f hf0 u 0 τ).const_mul (c u)
  have hHc' : ContinuousOn (fun s => 1 + PsiR f (τ - s)) (uIcc 0 τ) := by rwa [uIcc_of_le hτ]
  have hII : ∀ u, IntervalIntegrable
      (fun s => (1 + PsiR f (τ - s)) * (c u * atomK f u s)) volume 0 τ :=
    fun u => (hI u).continuousOn_mul hHc'
  have e2 : ∫ s in (0:ℝ)..τ, (1 + PsiR f (τ - s)) * ∑ u ∈ J, c u * atomK f u s =
      ∑ u ∈ J, c u * ∫ v in (0:ℝ)..(τ - u), (1 + PsiR f ((τ - u) - v)) * f v := by
    simp_rw [Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum fun u _ => hII u]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hfun : (fun s => (1 + PsiR f (τ - s)) * (c u * atomK f u s)) =
        fun s => c u * ((1 + PsiR f (τ - s)) * atomK f u s) := by
      funext s; ring
    rw [hfun, intervalIntegral.integral_const_mul,
      atom_integral_mul f hf0 _ (hJ u hu).1.le (hJ u hu).2 hHc]
    congr 1
    refine intervalIntegral.integral_congr fun v _ => ?_
    rw [show τ - (v + u) = τ - u - v by ring]
  rw [e2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have := psi_atom f hf0 hlt (sub_nonneg.2 (hJ u hu).2)
  linear_combination c u * this

/-- Pathwise (11), generic. -/
lemma decomp_path11 (f : ℝ → ℝ) (hf0 : Integrable (cpI f 0)) (hlt : ∫⁻ x, ‖cpI f 0 x‖ₑ < 1)
    (τ : ℝ) (hτ : 0 ≤ τ) (xp xm : ℝ → ℝ) (hp : (jset xp τ).Finite) (hm : (jset xm τ).Finite)
    (hxp : xp τ = ∑ u ∈ hp.toFinset, NearlyUnstableHawkes.Heston.jump xp u)
    (hxm : xm τ = ∑ u ∈ hm.toFinset, NearlyUnstableHawkes.Heston.jump xm u)
    (lp lm : ℝ → ℝ) (hlp : IntervalIntegrable lp volume 0 τ)
    (hlm : IntervalIntegrable lm volume 0 τ)
    (hdiff : ∀ s ≤ τ, lp s - lm s =
      ∑ u ∈ hp.toFinset, NearlyUnstableHawkes.Heston.jump xp u * atomK f u s
        - ∑ u ∈ hm.toFinset, NearlyUnstableHawkes.Heston.jump xm u * atomK f u s) :
    xp τ - xm τ =
      (NearlyUnstableHawkes.Heston.jumpSumOn xp (fun s => 1 + PsiR f (τ - s)) (Ioc 0 τ)
          - ∫ s in (0:ℝ)..τ, (1 + PsiR f (τ - s)) * lp s)
        - (NearlyUnstableHawkes.Heston.jumpSumOn xm (fun s => 1 + PsiR f (τ - s)) (Ioc 0 τ)
          - ∫ s in (0:ℝ)..τ, (1 + PsiR f (τ - s)) * lm s) := by
  have hJp : ∀ u ∈ hp.toFinset, u ∈ Ioc 0 τ := fun u hu => ((Set.Finite.mem_toFinset hp).1 hu).1
  have hJm : ∀ u ∈ hm.toFinset, u ∈ Ioc 0 τ := fun u hu => ((Set.Finite.mem_toFinset hm).1 hu).1
  have cp := atom_core11 f hf0 hlt τ hτ hp.toFinset hJp (NearlyUnstableHawkes.Heston.jump xp)
  have cm := atom_core11 f hf0 hlt τ hτ hm.toFinset hJm (NearlyUnstableHawkes.Heston.jump xm)
  have hsp := jumpSum_eq_finset xp τ hp (fun s => 1 + PsiR f (τ - s)) (le_refl τ)
  have hsm := jumpSum_eq_finset xm τ hm (fun s => 1 + PsiR f (τ - s)) (le_refl τ)
  rw [Finset.sum_congr rfl fun u hu => if_pos (hJp u hu).2] at hsp
  rw [Finset.sum_congr rfl fun u hu => if_pos (hJm u hu).2] at hsm
  have hSp := sum_atom_ii f hf0 (NearlyUnstableHawkes.Heston.jump xp) 0 τ hp.toFinset
  have hSm := sum_atom_ii f hf0 (NearlyUnstableHawkes.Heston.jump xm) 0 τ hm.toFinset
  have hHc' : ContinuousOn (fun s => 1 + PsiR f (τ - s)) (uIcc 0 τ) := by
    rw [uIcc_of_le hτ]; exact continuousOn_const.add (PsiR_contOn f hf0 hlt hτ)
  have hle : ∀ s ∈ uIcc (0:ℝ) τ, s ≤ τ := fun s hs => by rw [uIcc_of_le hτ] at hs; exact hs.2
  have hint2 : (∫ s in (0:ℝ)..τ, (1 + PsiR f (τ - s)) * lp s)
      - (∫ s in (0:ℝ)..τ, (1 + PsiR f (τ - s)) * lm s) =
      (∫ s in (0:ℝ)..τ, (1 + PsiR f (τ - s)) *
          ∑ u ∈ hp.toFinset, NearlyUnstableHawkes.Heston.jump xp u * atomK f u s)
      - ∫ s in (0:ℝ)..τ, (1 + PsiR f (τ - s)) *
          ∑ u ∈ hm.toFinset, NearlyUnstableHawkes.Heston.jump xm u * atomK f u s := by
    rw [← intervalIntegral.integral_sub (hlp.continuousOn_mul hHc') (hlm.continuousOn_mul hHc'),
      ← intervalIntegral.integral_sub (hSp.continuousOn_mul hHc') (hSm.continuousOn_mul hHc')]
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [← mul_sub, hdiff s (hle s hs)]
  rw [hsp, hsm, hxp, hxm]
  linear_combination cm - cp + hint2

/-- **(11)** pathwise. -/
theorem eq11_path {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ a T m : ℝ)
    (φ₁ φ₂ : ℝ → ℝ) (Np Nm : ℝ → Ω → ℕ) (ha : 0 < a) (ha1 : a < 1)
    (hK : KernelAssumption3 φ₁ φ₂ m)
    (hH2 : IsHawkes2 P μ (fun s => a * φ₁ s) (fun s => a * φ₂ s) T Np Nm) :
    ∀ ω : Ω, ∀ t : ℝ, 0 ≤ t →
      path Np ω t - path Nm ω t =
        intDiffM μ a φ₁ φ₂ Np Nm (fun u => 1 + PsiSigned a φ₁ φ₂ (t - u)) t ω := by
  intro ω τ hτ
  obtain ⟨hf0, hlt⟩ := phiSignedT_facts a φ₁ φ₂ m ha ha1 hK
  obtain ⟨hp, hxp'⟩ := jumps_count (fun u => Np u ω) (hH2.countPlus.mono ω) (hH2.countPlus.zero ω)
    (fun s hs => hH2.countPlus.rcont ω s hs) (Np τ ω) τ hτ rfl
  obtain ⟨hm, hxm'⟩ := jumps_count (fun u => Nm u ω) (hH2.countMinus.mono ω)
    (hH2.countMinus.zero ω) (fun s hs => hH2.countMinus.rcont ω s hs) (Nm τ ω) τ hτ rfl
  have hp' : (jset (path Np ω) τ).Finite := hp
  have hm' : (jset (path Nm ω) τ).Finite := hm
  have hxp : path Np ω τ = ∑ u ∈ hp'.toFinset, jump (path Np ω) u := by
    rw [← finsum_mem_eq_finite_toFinset_sum]; exact hxp'.symm
  have hxm : path Nm ω τ = ∑ u ∈ hm'.toFinset, jump (path Nm ω) u := by
    rw [← finsum_mem_eq_finite_toFinset_sum]; exact hxm'.symm
  have hk₁ := cpI_const_mul_int a φ₁ (int₁' hK)
  have hk₂ := cpI_const_mul_int a φ₂ (int₂' hK)
  have hlp := intensity_ii μ _ _ hk₁ hk₂ (path Np ω) (path Nm ω) τ hτ hp' hm'
  have hlm := intensity_ii μ _ _ hk₁ hk₂ (path Nm ω) (path Np ω) τ hτ hm' hp'
  exact decomp_path11 (phiSignedT a φ₁ φ₂) hf0 hlt τ hτ (path Np ω) (path Nm ω) hp' hm' hxp hxm
    (fun s => lamPlus μ a φ₁ φ₂ Np Nm s ω) (fun s => lamMinus μ a φ₁ φ₂ Np Nm s ω) hlp hlm
    (fun s hs => lam_diff μ a φ₁ φ₂ (path Np ω) (path Nm ω) τ hp' hm' hs)

end P7ade6a3f

open MeasureTheory ProbabilityTheory Filter NearlyUnstableHawkes.Heston in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (φ₁ φ₂ : ℝ → ℝ) (m : ℝ) (hK : KernelAssumption3 φ₁ φ₂ m)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (μ : ℝ) (hμ : 0 < μ) (T : ℝ) (hT : 0 < T)
    (Np Nm : ℝ → Ω → ℕ)
    (hH : IsHawkes2 P μ (fun s => a * φ₁ s) (fun s => a * φ₂ s) T Np Nm) :
    ∀ ω : Ω, ∀ t : ℝ, 0 ≤ t → t ≤ T →
      path Np ω t - path Nm ω t =
        intDiffM μ a φ₁ φ₂ Np Nm (fun u => 1 + PsiSigned a φ₁ φ₂ (t - u)) t ω := by
  intro ω t ht0 _
  exact P7ade6a3f.eq11_path P μ a T m φ₁ φ₂ Np Nm ha0 ha1 hK hH ω t ht0
