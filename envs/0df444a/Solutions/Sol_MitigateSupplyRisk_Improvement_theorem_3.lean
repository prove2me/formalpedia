-- Prove2me | solution 1 for MitigateSupplyRisk.Improvement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T14:19:52.816846+00:00
-- url     : https://prove2.me/submissions/78a3b289-4c63-477c-8ad1-8e9bb58758ae

import Mathlib
import Definitions.Def_MitigateSupplyRisk_Improvement_Model
import Definitions.Def_MitigateSupplyRisk_Improvement_FirstStage

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology Interval

namespace P7fe25a30

open MitigateSupplyRisk.Improvement

lemma swap_ind (ρ : Measure ℝ) [IsFiniteMeasure ρ] (q : ℝ) (k : ℝ → ℝ) (hk : Measurable k)
    (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ u, |g u| ≤ C) :
    ∫ x, (∫ u in Ioc 0 q, (if x ≤ k u then g u else 0)) ∂ρ
      = ∫ u in Ioc 0 q, ρ.real (Iic (k u)) * g u := by
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 ≤ k p.2} :=
    measurableSet_le measurable_fst (hk.comp measurable_snd)
  have hint : Integrable (Function.uncurry fun (x u : ℝ) => if x ≤ k u then g u else 0)
      (ρ.prod (volume.restrict (Ioc 0 q))) := by
    have : (Function.uncurry fun (x u : ℝ) => if x ≤ k u then g u else 0)
        = {p : ℝ × ℝ | p.1 ≤ k p.2}.indicator (fun p => g p.2) := by
      funext p; simp [Function.uncurry, Set.indicator]
    rw [this]
    refine Integrable.indicator ?_ hS
    refine Integrable.mono' (integrable_const C) (hg.comp measurable_snd).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hC p.2
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have : (fun x => if x ≤ k u then g u else 0) = (Iic (k u)).indicator (fun _ => g u) := by
    funext x; simp [Set.indicator]
  simp only
  rw [this, integral_indicator_const _ measurableSet_Iic, smul_eq_mul]

lemma integral_pos_part (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Iio 0) = 0)
    {y : ℝ} (_hy : 0 ≤ y) :
    ∫ x, max (y - x) 0 ∂μ = ∫ u in Ioc 0 y, cdf μ u := by
  have h1 := swap_ind μ y id measurable_id (fun _ => 1) measurable_const 1 (by simp)
  simp only [id, mul_one] at h1
  rw [setIntegral_congr_fun measurableSet_Ioc (fun u _ => cdf_eq_real μ u), ← h1]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ x ∂μ, 0 ≤ x := by
    rw [ae_iff]
    have : {x : ℝ | ¬ 0 ≤ x} = Iio 0 := by ext; simp
    rw [this]; exact hμ
  filter_upwards [hae] with x hx
  have : (fun u : ℝ => if x ≤ u then (1:ℝ) else 0) = (Ici x).indicator 1 := by
    funext u; simp [Set.indicator]
  rw [this, integral_indicator_one measurableSet_Ici, Measure.real,
    Measure.restrict_apply measurableSet_Ici]
  have hsub1 : Ioc x y ⊆ Ici x ∩ Ioc 0 y := fun u hu =>
    ⟨le_of_lt hu.1, lt_of_le_of_lt hx hu.1, hu.2⟩
  have hsub2 : Ici x ∩ Ioc 0 y ⊆ Icc x y := fun u hu => ⟨hu.1, hu.2.2⟩
  have e1 := measure_mono (μ := volume) hsub1
  have e2 := measure_mono (μ := volume) hsub2
  rw [Real.volume_Ioc] at e1
  rw [Real.volume_Icc] at e2
  rw [le_antisymm e2 e1, ENNReal.toReal_ofReal']

lemma Ioc_y (M : Model) (q ξ : ℝ) :
    Ioc 0 (M.y q ξ) = Ioc 0 q ∩ Iic (M.K - ξ) := by
  ext u
  simp only [Model.y, mem_Ioc, mem_inter_iff, mem_Iic, le_min_iff, le_max_iff]
  constructor
  · rintro ⟨h0, hq, h | h⟩
    · exact ⟨⟨h0, hq⟩, h⟩
    · exact absurd h (not_le.2 h0)
  · rintro ⟨⟨h0, hq⟩, h⟩
    exact ⟨h0, hq, Or.inl h⟩

lemma inner_ind (M : Model) (q ξ : ℝ) (g : ℝ → ℝ) :
    ∫ u in Ioc 0 (M.y q ξ), g u = ∫ u in Ioc 0 q, (if ξ ≤ M.K - u then g u else 0) := by
  rw [Ioc_y, ← setIntegral_indicator measurableSet_Iic]
  refine setIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
  simp only [Set.indicator, mem_Iic]
  split_ifs with h h' h' <;> first | rfl | (exfalso; linarith)

lemma intOn_bdd {f : ℝ → ℝ} (hf : Measurable f) (C : ℝ) (hC : ∀ u, |f u| ≤ C) (a b : ℝ) :
    IntegrableOn f (Ioc a b) :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (ae_of_all _ fun u => by simpa [Real.norm_eq_abs] using hC u)

lemma intOn_bdd' {f : ℝ → ℝ} (hf : Measurable f) (C : ℝ) (hC : ∀ u, |f u| ≤ C) (a b : ℝ) :
    IntegrableOn f (Ioo a b) :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (ae_of_all _ fun u => by simpa [Real.norm_eq_abs] using hC u)

lemma measF (M : Model) : Measurable M.F := (cdf M.μ).mono.measurable

lemma measG (M : Model) (a : ℝ) : Measurable fun u => M.G (M.K - u) a :=
  (cdf (M.ν a)).mono.measurable.comp (measurable_const.sub measurable_id)

lemma absF (M : Model) (hM : M.Assumptions) (u : ℝ) : |M.F u| ≤ 1 := by
  have := hM.μ_prob
  have h1 := cdf_nonneg M.μ u
  have h2 := cdf_le_one M.μ u
  unfold Model.F
  rw [abs_le]; constructor <;> linarith

lemma absG (M : Model) (hM : M.Assumptions) (ξ a : ℝ) : |M.G ξ a| ≤ 1 := by
  have := hM.ν_prob a
  have h1 := cdf_nonneg (M.ν a) ξ
  have h2 := cdf_le_one (M.ν a) ξ
  unfold Model.G
  rw [abs_le]; constructor <;> linarith

lemma G_nonneg (M : Model) (ξ a : ℝ) : 0 ≤ M.G ξ a := cdf_nonneg _ _

lemma absW (M : Model) (hM : M.Assumptions) (u : ℝ) : |M.φ - M.F u| ≤ |M.φ| + 1 := by
  calc |M.φ - M.F u| ≤ |M.φ| + |M.F u| := abs_sub _ _
    _ ≤ |M.φ| + 1 := by linarith [absF M hM u]

lemma measH (M : Model) (a : ℝ) : Measurable fun u => (M.φ - M.F u) * M.G (M.K - u) a :=
  (measurable_const.sub (measF M)).mul (measG M a)

lemma absH (M : Model) (hM : M.Assumptions) (a u : ℝ) :
    |(M.φ - M.F u) * M.G (M.K - u) a| ≤ (|M.φ| + 1) * 1 := by
  rw [abs_mul]
  exact mul_le_mul (absW M hM u) (absG M hM _ _) (abs_nonneg _) (by positivity)

/-- representation of `Π₂` for `η = 0`. -/
lemma Pi2_rep (M : Model) (hM : M.Assumptions) (hη : M.η = 0) (a q : ℝ) (hq : 0 ≤ q) :
    M.Pi2 q a = (M.r + M.p - M.v) * (∫ u in Ioc 0 q, (M.φ - M.F u) * M.G (M.K - u) a)
      - M.p * ∫ x, x ∂M.μ := by
  have := hM.μ_prob
  have := hM.ν_prob a
  have hψ : M.ψ = 0 := by simp [Model.ψ, hη]
  have hy0 : ∀ ξ, 0 ≤ M.y q ξ := fun ξ => le_min hq (le_max_right _ _)
  have hyq : ∀ ξ, M.y q ξ ≤ q := fun ξ => min_le_left _ _
  have hae : ∀ᵐ x ∂M.μ, 0 ≤ x := by
    rw [ae_iff]
    have : {x : ℝ | ¬ 0 ≤ x} = Iio 0 := by ext; simp
    rw [this]; exact hM.μ_nonneg
  have hprod_int : Integrable (fun ω : ℝ × ℝ => max (M.y q ω.1 - ω.2) 0)
      ((M.ν a).prod M.μ) := by
    refine Integrable.mono' (integrable_const q) ?_ ?_
    · have hc : Continuous fun ω : ℝ × ℝ => max (M.y q ω.1 - ω.2) 0 := by
        unfold Model.y; fun_prop
      exact hc.aestronglyMeasurable
    · have h2 : ∀ᵐ ω ∂((M.ν a).prod M.μ), 0 ≤ ω.2 :=
        (measurePreserving_snd (μ := M.ν a) (ν := M.μ)).quasiMeasurePreserving.ae hae
      filter_upwards [h2] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [hyq ω.1]) hq
  unfold Model.Pi2
  rw [integral_prod _ hprod_int, hψ]
  have hinner : ∀ ξ, ∫ x, max (M.y q ξ - x) 0 ∂M.μ
      = ∫ u in Ioc 0 q, (if ξ ≤ M.K - u then M.F u else 0) := fun ξ => by
    rw [integral_pos_part M.μ hM.μ_nonneg (hy0 ξ), inner_ind]
    rfl
  have hyint : ∀ ξ, M.y q ξ = ∫ u in Ioc 0 q, (if ξ ≤ M.K - u then (1:ℝ) else 0) := fun ξ => by
    rw [← inner_ind]
    simp [Real.volume_real_Ioc_of_le (hy0 ξ)]
  simp only [hinner]
  simp only [hyint]
  rw [swap_ind (M.ν a) q (fun u => M.K - u) (measurable_const.sub measurable_id) M.F (measF M) 1
      (absF M hM),
    swap_ind (M.ν a) q (fun u => M.K - u) (measurable_const.sub measurable_id) (fun _ => 1)
      measurable_const 1 (by simp)]
  have hGe : ∀ u, (M.ν a).real (Iic (M.K - u)) = M.G (M.K - u) a := fun u =>
    (cdf_eq_real (M.ν a) (M.K - u)).symm
  simp only [hGe, mul_one]
  have i1 : IntegrableOn (fun u => M.φ * M.G (M.K - u) a) (Ioc 0 q) :=
    intOn_bdd ((measG M a).const_mul _) (|M.φ| * 1) (fun u => by
      show |M.φ * M.G (M.K - u) a| ≤ |M.φ| * 1
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (absG M hM _ _) (abs_nonneg _)) 0 q
  have i2 : IntegrableOn (fun u => M.G (M.K - u) a * M.F u) (Ioc 0 q) :=
    intOn_bdd ((measG M a).mul (measF M)) (1 * 1) (fun u => by
      show |M.G (M.K - u) a * M.F u| ≤ 1 * 1
      rw [abs_mul]; exact mul_le_mul (absG M hM _ _) (absF M hM u) (abs_nonneg _) zero_le_one) 0 q
  have key : M.φ * (∫ u in Ioc 0 q, M.G (M.K - u) a) - ∫ u in Ioc 0 q, M.G (M.K - u) a * M.F u
      = ∫ u in Ioc 0 q, (M.φ - M.F u) * M.G (M.K - u) a := by
    rw [← integral_const_mul, ← integral_sub i1 i2]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only; ring
  rw [zero_mul, zero_add, key]

def T (M : Model) : Set ℝ := {u | u ∈ Icc 0 M.K ∧ ∀ t ∈ Ioo 0 u, 0 ≤ M.φ - M.F t}

noncomputable def y0 (M : Model) : ℝ := sSup (T M)

lemma T_bdd (M : Model) : BddAbove (T M) := ⟨M.K, fun _ hu => hu.1.2⟩

lemma zero_mem_T (M : Model) (hM : M.Assumptions) : (0:ℝ) ∈ T M :=
  ⟨⟨le_rfl, hM.K_pos.le⟩, fun _ ht => absurd ht.2 (not_lt.2 ht.1.le)⟩

lemma y0_nonneg (M : Model) (hM : M.Assumptions) : 0 ≤ y0 M :=
  le_csSup (T_bdd M) (zero_mem_T M hM)

lemma w_pos (M : Model) (hM : M.Assumptions) {t : ℝ} (ht : t ∈ Ioo 0 (y0 M)) :
    0 ≤ M.φ - M.F t := by
  obtain ⟨u, huT, htu⟩ := exists_lt_of_lt_csSup ⟨0, zero_mem_T M hM⟩ ht.2
  exact huT.2 t ⟨ht.1, htu⟩

lemma w_neg (M : Model) (hM : M.Assumptions) {t : ℝ} (ht : y0 M < t) (htK : t ≤ M.K) :
    M.φ - M.F t ≤ 0 := by
  by_contra h
  push Not at h
  have hT : t ∈ T M := ⟨⟨(y0_nonneg M hM).trans ht.le, htK⟩, fun s hs => by
    have : M.F s ≤ M.F t := (cdf M.μ).mono hs.2.le
    linarith⟩
  exact absurd (le_csSup (T_bdd M) hT) (not_le.2 ht)

lemma G_zero (M : Model) (hM : M.Assumptions) (a : ℝ) {t : ℝ} (ht : M.K < t) :
    M.G (M.K - t) a = 0 := by
  have := hM.ν_prob a
  unfold Model.G
  rw [cdf_eq_real, Measure.real,
    measure_mono_null (Iic_subset_Iio.2 (by linarith : M.K - t < 0)) (hM.ν_nonneg a),
    ENNReal.toReal_zero]

lemma h_int (M : Model) (hM : M.Assumptions) (a s t : ℝ) :
    IntegrableOn (fun u => (M.φ - M.F u) * M.G (M.K - u) a) (Ioc s t) :=
  intOn_bdd (measH M a) _ (absH M hM a) s t

lemma Ioc_le (M : Model) (hM : M.Assumptions) (a q : ℝ) (hq : 0 ≤ q) :
    ∫ u in Ioc 0 q, (M.φ - M.F u) * M.G (M.K - u) a
      ≤ ∫ u in Ioc 0 (y0 M), (M.φ - M.F u) * M.G (M.K - u) a := by
  have hy := y0_nonneg M hM
  have hii : ∀ s t, IntervalIntegrable (fun u => (M.φ - M.F u) * M.G (M.K - u) a) volume s t :=
    fun s t => ⟨h_int M hM a s t, h_int M hM a t s⟩
  rw [← intervalIntegral.integral_of_le hq, ← intervalIntegral.integral_of_le hy, ← sub_nonpos,
    intervalIntegral.integral_interval_sub_left (hii 0 q) (hii 0 (y0 M))]
  rcases le_total (y0 M) q with hyq | hqy
  · rw [intervalIntegral.integral_of_le hyq]
    refine setIntegral_nonpos measurableSet_Ioc (fun u hu => ?_)
    rcases le_or_gt u M.K with huK | huK
    · have h1 := w_neg M hM hu.1 huK
      have h2 := G_nonneg M (M.K - u) a
      nlinarith
    · simp [G_zero M hM a huK]
  · rw [intervalIntegral.integral_symm, neg_nonpos, intervalIntegral.integral_of_le hqy,
      integral_Ioc_eq_integral_Ioo]
    refine setIntegral_nonneg measurableSet_Ioo (fun u hu => ?_)
    exact mul_nonneg (w_pos M hM ⟨lt_of_le_of_lt hq hu.1, hu.2⟩) (G_nonneg _ _ _)

lemma Pi2_le (M : Model) (hM : M.Assumptions) (hη : M.η = 0) (a q : ℝ) (hq : 0 ≤ q) :
    M.Pi2 q a ≤ M.Pi2 (y0 M) a := by
  rw [Pi2_rep M hM hη a q hq, Pi2_rep M hM hη a _ (y0_nonneg M hM)]
  have hc : 0 ≤ M.r + M.p - M.v := by linarith [hM.v_lt]
  linarith [mul_le_mul_of_nonneg_left (Ioc_le M hM a q hq) hc]

lemma Pi2star_eq (M : Model) (hM : M.Assumptions) (hη : M.η = 0) (a : ℝ) :
    M.Pi2star a = M.Pi2 (y0 M) a := by
  unfold Model.Pi2star
  exact IsGreatest.csSup_eq ⟨⟨y0 M, y0_nonneg M hM, rfl⟩, by
    rintro _ ⟨q, hq, rfl⟩; exact Pi2_le M hM hη a q hq⟩

lemma Phi0_concave (M : Model) (hM : M.Assumptions) (a0 : ℝ)
    (hG : ∀ ξ : ℝ, ConcaveOn ℝ (Ici a0) (fun a => M.G ξ a)) :
    ConcaveOn ℝ (Ici a0)
      (fun a => ∫ u in Ioc 0 (y0 M), (M.φ - M.F u) * M.G (M.K - u) a) := by
  refine ⟨convex_Ici _, fun a1 ha1 a2 ha2 α β hα hβ hαβ => ?_⟩
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((h_int M hM a1 _ _).const_mul α) ((h_int M hM a2 _ _).const_mul β),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_mono_on ?_ ?_ measurableSet_Ioo (fun u hu => ?_)
  · exact ((intOn_bdd' (measH M a1) _ (absH M hM a1) _ _).const_mul α).add
      ((intOn_bdd' (measH M a2) _ (absH M hM a2) _ _).const_mul β)
  · exact intOn_bdd' (measH M _) _ (absH M hM _) _ _
  · have hw := w_pos M hM hu
    have hc := (hG (M.K - u)).2 ha1 ha2 hα hβ hαβ
    simp only [smul_eq_mul] at hc
    nlinarith [mul_le_mul_of_nonneg_left hc hw]

lemma lipG (g : ℝ → ℝ) (a0 a1 : ℝ) (h01 : a0 < a1) (hc : ConcaveOn ℝ (Ici a0) g)
    (hm : Monotone g) (h0 : ∀ x, 0 ≤ g x) (h1 : ∀ x, g x ≤ 1) {x y : ℝ}
    (hx : a1 < x) (hy : a1 < y) :
    |g x - g y| ≤ (1 / (a1 - a0)) * |x - y| := by
  wlog hxy : x ≤ y generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x]; exact this hy hx (le_of_not_ge hxy)
  rcases hxy.lt_or_eq with hxy | rfl
  · have hs := hc.slope_anti_adjacent (x := a0) (y := x) (z := y) (mem_Ici.2 le_rfl)
      (mem_Ici.2 (by linarith)) (by linarith) hxy
    have hpos : 0 < x - a0 := by linarith
    have hB : 1 / (a1 - a0) * (a1 - a0) = 1 := one_div_mul_cancel (by linarith)
    have hBpos : 0 ≤ 1 / (a1 - a0) := by
      have : 0 < a1 - a0 := by linarith
      positivity
    have hb : (g x - g a0) / (x - a0) ≤ 1 / (a1 - a0) := by
      rw [div_le_iff₀ hpos]
      nlinarith [h0 a0, h1 x]
    have hle : g y - g x ≤ 1 / (a1 - a0) * (y - x) := by
      have := hs.trans hb
      rwa [div_le_iff₀ (by linarith)] at this
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hm hxy.le)), abs_sub_comm,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x)]
    exact hle
  · simp

end P7fe25a30

open P7fe25a30

open MitigateSupplyRisk.Improvement MeasureTheory ProbabilityTheory Set in
theorem solution (M : Model) (I : Effort) (hM : M.Assumptions) (hI : I.Assumptions)
    (hη : M.η = 0) (hG : ∀ ξ : ℝ, ConcaveOn ℝ (Ici I.a0) (fun a => M.G ξ a)) :
    ConcaveOn ℝ (Ici I.a0) (Pi1 M I) ∧
    ∀ (aStar qStar z' : ℝ) (dG : ℝ → ℝ),
      I.a0 < aStar → IsMaxOn (Pi1 M I) (Ici I.a0) aStar →
      0 ≤ qStar → IsMaxOn (fun q => M.Pi2 q aStar) (Ici 0) qStar →
      HasDerivAt I.z z' aStar →
      (∀ ξ ∈ Icc (M.K - qStar) M.K, HasDerivAt (fun a => M.G ξ a) (dG ξ) aStar) →
      I.m * z' = I.θ * ((M.r + M.p - M.v) *
        ∫ ξ in (M.K - qStar)..M.K, (M.φ - M.F (M.K - ξ)) * dG ξ) := by
  have hc : 0 ≤ M.r + M.p - M.v := by linarith [hM.v_lt]
  constructor
  · have hfun : Pi1 M I = fun a =>
        (-(I.m • I.z a)) + I.θ • ((M.r + M.p - M.v) •
          (∫ u in Ioc 0 (y0 M), (M.φ - M.F u) * M.G (M.K - u) a))
        + (-(I.θ * (M.p * ∫ x, x ∂M.μ)) + (1 - I.θ) * M.Pi2star I.a0) := by
      funext a
      simp only [Pi1, Pi2star_eq M hM hη a,
        Pi2_rep M hM hη a _ (y0_nonneg M hM), smul_eq_mul]
      ring
    rw [hfun]
    have h1 : ConcaveOn ℝ (Ici I.a0) (fun a => -(I.m • I.z a)) :=
      (hI.z_convex.smul hI.m_nonneg).neg
    have h2 : ConcaveOn ℝ (Ici I.a0) (fun a => I.θ • ((M.r + M.p - M.v) •
          (∫ u in Ioc 0 (y0 M), (M.φ - M.F u) * M.G (M.K - u) a))) :=
      ((Phi0_concave M hM I.a0 hG).smul hc).smul hI.θ_nonneg
    exact (h1.add h2).add (concaveOn_const _ (convex_Ici _))
  · intro aStar qStar z' dG ha hmax hq0 hqmax hz hdG
    have hq' : Ι (0:ℝ) qStar = Ioc 0 qStar := uIoc_of_le hq0
    have hrepq : ∀ a, M.Pi2 qStar a = (M.r + M.p - M.v) *
        (∫ u in (0:ℝ)..qStar, (M.φ - M.F u) * M.G (M.K - u) a) - M.p * ∫ x, x ∂M.μ :=
      fun a => by rw [Pi2_rep M hM hη a qStar hq0, intervalIntegral.integral_of_le hq0]
    have e3 : M.Pi2star aStar = M.Pi2 qStar aStar := by
      rw [Pi2star_eq M hM hη aStar]
      exact le_antisymm (isMaxOn_iff.1 hqmax _ (y0_nonneg M hM)) (Pi2_le M hM hη aStar qStar hq0)
    have hloc : IsLocalMax (fun a => -I.m * I.z a + I.θ * M.Pi2 qStar a
        + (1 - I.θ) * M.Pi2star I.a0) aStar := by
      filter_upwards [Ici_mem_nhds ha] with a ha'
      have e1 := isMaxOn_iff.1 hmax a ha'
      simp only [Pi1] at e1
      rw [e3] at e1
      have e2 : M.Pi2 qStar a ≤ M.Pi2star a := by
        rw [Pi2star_eq M hM hη a]; exact Pi2_le M hM hη a qStar hq0
      nlinarith [mul_le_mul_of_nonneg_left e2 hI.θ_nonneg]
    simp only [hrepq] at hloc
    -- derivative of the integral
    set a1 := (I.a0 + aStar) / 2 with ha1
    have h01 : I.a0 < a1 := by linarith
    have hs : Ioi a1 ∈ 𝓝 aStar := Ioi_mem_nhds (by linarith)
    have hF'meas : AEStronglyMeasurable (fun u => (M.φ - M.F u) * dG (M.K - u))
        (volume.restrict (Ι (0:ℝ) qStar)) := by
      have htn : Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) atTop (𝓝[≠] 0) :=
        tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
          Eventually.of_forall fun n => by
            simp only [mem_compl_iff, mem_singleton_iff]; positivity⟩
      refine aestronglyMeasurable_of_tendsto_ae atTop
        (f := fun (n : ℕ) u => (M.φ - M.F u) * ((1 / ((n:ℝ) + 1))⁻¹ *
          (M.G (M.K - u) (aStar + 1 / ((n:ℝ) + 1)) - M.G (M.K - u) aStar)))
        (fun n => ?_) ?_
      · exact ((measurable_const.sub (measF M)).mul
          (((measG M _).sub (measG M _)).const_mul _)).aestronglyMeasurable
      · rw [hq', ae_restrict_iff' measurableSet_Ioc]
        refine ae_of_all _ fun u hu => ?_
        have hd := hdG (M.K - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
        exact ((hasDerivAt_iff_tendsto_slope_zero.1 hd).comp htn).const_mul _
    have hlip : ∀ᵐ t ∂volume, t ∈ Ι (0:ℝ) qStar →
        LipschitzOnWith (Real.nnabs ((|M.φ| + 1) * (1 / (a1 - I.a0))))
          (fun x => (M.φ - M.F t) * M.G (M.K - t) x) (Ioi a1) := by
      refine ae_of_all _ fun u _ => LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      have hBpos : 0 ≤ (|M.φ| + 1) * (1 / (a1 - I.a0)) := by
        have : 0 < a1 - I.a0 := by linarith
        positivity
      rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs, abs_of_nonneg hBpos, ← mul_sub, abs_mul,
        mul_assoc]
      refine mul_le_mul (absW M hM u) ?_ (abs_nonneg _) (by positivity)
      have := hM.ν_prob
      exact lipG (fun a => M.G (M.K - u) a) I.a0 a1 h01 (hG _)
        (fun a a' h => hM.stochOrder a a' h _) (fun x => G_nonneg M _ x)
        (fun x => (abs_le.1 (absG M hM _ x)).2) hx hy
    have hdiff : ∀ᵐ t ∂volume, t ∈ Ι (0:ℝ) qStar →
        HasDerivAt (fun x => (M.φ - M.F t) * M.G (M.K - t) x)
          ((M.φ - M.F t) * dG (M.K - t)) aStar := by
      refine ae_of_all _ fun u hu => ?_
      rw [hq'] at hu
      exact (hdG (M.K - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩).const_mul _
    have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume)
      (a := 0) (b := qStar) (F := fun x u => (M.φ - M.F u) * M.G (M.K - u) x)
      (F' := fun u => (M.φ - M.F u) * dG (M.K - u)) (x₀ := aStar)
      (bound := fun _ => (|M.φ| + 1) * (1 / (a1 - I.a0))) hs
      (Eventually.of_forall fun x => (measH M x).aestronglyMeasurable)
      ⟨h_int M hM aStar 0 qStar, h_int M hM aStar qStar 0⟩ hF'meas hlip
      intervalIntegrable_const hdiff
    have hΨd := ((hz.const_mul (-I.m)).add
      (((key.2.const_mul (M.r + M.p - M.v)).sub_const (M.p * ∫ x, x ∂M.μ)).const_mul I.θ)).add_const
      ((1 - I.θ) * M.Pi2star I.a0)
    have h0 := hloc.hasDerivAt_eq_zero hΨd
    have hcov := intervalIntegral.integral_comp_sub_left
      (fun ξ => (M.φ - M.F (M.K - ξ)) * dG ξ) M.K (a := 0) (b := qStar)
    simp only [sub_zero, sub_sub_cancel] at hcov
    rw [← hcov]
    linear_combination -h0
