-- Prove2me | solution 1 for ManyServerFluid.Uniqueness.remark_4_3
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-05T19:50:43.125889+00:00
-- url     : https://prove2.me/submissions/e76562bc-4bd5-4057-9710-8c312353f8ca

import Mathlib
import Definitions.Def_ManyServerFluid_Uniqueness_Model
import Definitions.Def_ManyServerFluid_Uniqueness_AgeEquation
open MeasureTheory Filter Topology Set
open scoped ENNReal

open ManyServerFluid.Uniqueness

namespace MSFRem43

variable (S : ServiceLaw)

lemma G_eq_intervalIntegral (x : ℝ) : S.G x = ∫ y in (0 : ℝ)..x, S.g y := by
  have hint : ∀ c : ℝ, IntegrableOn S.g (Iic c) := fun c => S.integrable_g.integrableOn
  have h0 : S.G 0 = 0 := by
    unfold ServiceLaw.G
    apply setIntegral_eq_zero_of_ae_eq_zero
    have : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 0 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [this] with y hy hyI
    exact S.g_eq_zero_of_neg y (lt_of_le_of_ne hyI hy)
  have := intervalIntegral.integral_Iic_sub_Iic (hint 0) (hint x)
  unfold ServiceLaw.G at h0 ⊢
  rw [← this, h0, sub_zero]

lemma G_fun_eq : S.G = fun x => ∫ y in (0 : ℝ)..x, S.g y :=
  funext (G_eq_intervalIntegral S)

lemma G_zero : S.G 0 = 0 := by
  rw [G_eq_intervalIntegral]; simp

lemma G_continuous : Continuous S.G := by
  rw [G_fun_eq]
  exact intervalIntegral.continuous_primitive (fun _ _ => S.integrable_g.intervalIntegrable) 0

lemma G_hasDerivAt_ae : ∀ᵐ y, HasDerivAt S.G (S.g y) y := by
  have hloc : LocallyIntegrable S.g volume := S.integrable_g.locallyIntegrable
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hloc] with y hy
  rw [G_fun_eq]
  exact hy 0

/-- The Stieltjes measure of an `I_0` path is the genuine one. -/
lemma stieltjes_facts (Z : ℝ → ℝ) (hZ : ServiceLaw.IsI0 Z) :
    ∃ hF : Monotone (fun t => Z (max t 0)) ∧
        ∀ t, ContinuousWithinAt (fun t => Z (max t 0)) (Ici t) t,
      stieltjes Z = (StieltjesFunction.mk (fun t => Z (max t 0)) hF.1 hF.2).measure := by
  have hmono : Monotone (fun t => Z (max t 0)) := by
    intro a b hab
    exact hZ.1 (show (0:ℝ) ≤ max a 0 from le_max_right _ _)
      (show (0:ℝ) ≤ max b 0 from le_max_right _ _) (max_le_max hab le_rfl)
  have hrc : ∀ t, ContinuousWithinAt (fun t => Z (max t 0)) (Ici t) t := by
    intro t
    by_cases ht : 0 ≤ t
    · have := hZ.2.2.1 t ht
      refine this.congr (fun s hs => ?_) ?_
      · simp [max_eq_left (ht.trans (show t ≤ s from hs))]
      · simp [max_eq_left ht]
    · have hev : (fun t => Z (max t 0)) =ᶠ[𝓝 t] fun _ => Z 0 := by
        filter_upwards [Iio_mem_nhds (not_le.mp ht)] with s hs
        simp [max_eq_right (le_of_lt (show s < 0 from hs))]
      exact (continuousAt_const.congr hev.symm).continuousWithinAt
  refine ⟨⟨hmono, hrc⟩, ?_⟩
  unfold stieltjes
  rw [dif_pos ⟨hmono, hrc⟩]

lemma measureReal_Icc (Z : ℝ → ℝ) (hZ : ServiceLaw.IsI0 Z) (u : ℝ) (hu : 0 ≤ u) :
    (stieltjes Z).real (Icc 0 u) = Z u := by
  obtain ⟨hF, hμ⟩ := stieltjes_facts Z hZ
  rw [measureReal_def, hμ, StieltjesFunction.measure_Icc]
  have hl : Function.leftLim (StieltjesFunction.mk (fun t => Z (max t 0)) hF.1 hF.2) 0 = 0 := by
    apply leftLim_eq_of_tendsto
    have hev : (fun t => Z (max t 0)) =ᶠ[𝓝[<] (0:ℝ)] fun _ => (0:ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [max_eq_right (le_of_lt (show s < 0 from hs)), hZ.2.1]
    exact tendsto_const_nhds.congr' hev.symm
  rw [hl]
  simp only [sub_zero]
  have hZu : 0 ≤ Z u := by
    have := hZ.1 ((Set.mem_Ici.mpr (le_refl (0:ℝ)))) (show u ∈ Ici 0 from hu) hu
    rw [hZ.2.1] at this; exact this
  show (ENNReal.ofReal (Z (max u 0))).toReal = Z u
  rw [max_eq_left hu, ENNReal.toReal_ofReal hZu]

lemma finite_restrict (Z : ℝ → ℝ) (hZ : ServiceLaw.IsI0 Z) (t : ℝ) :
    IsFiniteMeasure ((stieltjes Z).restrict (Icc 0 t)) := by
  obtain ⟨hF, hμ⟩ := stieltjes_facts Z hZ
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ, hμ, StieltjesFunction.measure_Icc]
  exact ENNReal.ofReal_lt_top

/-- Integration by parts against `dZ` for an `I_0` path `Z`, in the Fubini form. -/
lemma ibp_single (Z : ℝ → ℝ) (hZ : ServiceLaw.IsI0 Z) (t : ℝ) (ht : 0 ≤ t)
    (φ ψ : ℝ → ℝ) (c : ℝ) (hψ : IntegrableOn ψ (Icc 0 t))
    (hφ : ∀ s ∈ Icc 0 t, φ s = c + ∫ u in s..t, ψ u) :
    ∫ s in Icc 0 t, φ s ∂(stieltjes Z) = c * Z t + ∫ s in Icc 0 t, ψ s * Z s := by
  have := finite_restrict Z hZ t
  set μ := stieltjes Z with hμdef
  let k : ℝ → ℝ → ℝ := fun s u => if s ≤ u then ψ u else 0
  have hint : Integrable (Function.uncurry k)
      ((μ.restrict (Icc 0 t)).prod (volume.restrict (Icc 0 t))) := by
    have hsnd : Integrable (fun p : ℝ × ℝ => ψ p.2)
        ((μ.restrict (Icc 0 t)).prod (volume.restrict (Icc 0 t))) :=
      hψ.comp_snd _
    refine Integrable.mono' hsnd.norm ?_ ?_
    · have : Function.uncurry k = {p : ℝ × ℝ | p.1 ≤ p.2}.indicator (fun p => ψ p.2) := by
        funext p; simp [k, indicator, Function.uncurry]
      rw [this]
      exact hsnd.aestronglyMeasurable.indicator (measurableSet_le measurable_fst measurable_snd)
    · filter_upwards with p
      simp only [Function.uncurry, k]
      split_ifs <;> simp
  have hinner : ∀ s ∈ Icc 0 t, ∫ u in s..t, ψ u = ∫ u in Icc 0 t, k s u := by
    intro s hs
    rw [intervalIntegral.integral_of_le hs.2, ← integral_Icc_eq_integral_Ioc]
    have : ∀ u, k s u = (Ici s).indicator ψ u := by
      intro u; simp only [k, Set.indicator_apply, mem_Ici]
    simp_rw [this]
    have hset : Icc 0 t ∩ Ici s = Icc s t := by
      ext u
      simp only [mem_Icc, mem_inter_iff, mem_Ici]
      constructor
      · intro h; exact ⟨h.2, h.1.2⟩
      · intro h; exact ⟨⟨hs.1.trans h.1, h.2⟩, h.1⟩
    rw [setIntegral_indicator measurableSet_Ici, hset]
  calc ∫ s in Icc 0 t, φ s ∂μ = ∫ s in Icc 0 t, (c + ∫ u in Icc 0 t, k s u) ∂μ :=
        setIntegral_congr_fun measurableSet_Icc (fun s hs => by rw [hφ s hs, hinner s hs])
    _ = c * Z t + ∫ s in Icc 0 t, (∫ u in Icc 0 t, k s u) ∂μ := by
        have hl : Integrable (fun s => ∫ u in Icc 0 t, k s u) (μ.restrict (Icc 0 t)) :=
          hint.integral_prod_left
        rw [integral_add (integrable_const c) hl, setIntegral_const,
          measureReal_Icc Z hZ t ht, smul_eq_mul, mul_comm]
    _ = c * Z t + ∫ u in Icc 0 t, (∫ s in Icc 0 t, k s u ∂μ) := by
        congr 1
        exact integral_integral_swap hint
    _ = c * Z t + ∫ u in Icc 0 t, ψ u * Z u := by
        congr 1
        apply setIntegral_congr_fun measurableSet_Icc
        intro u hu
        have : ∀ s, k s u = (Iic u).indicator (fun _ => ψ u) s := by
          intro s; simp only [k, Set.indicator_apply, mem_Iic]
        simp only [this]
        rw [setIntegral_indicator measurableSet_Iic, setIntegral_const]
        have hset : Icc 0 t ∩ Iic u = Icc 0 u := by
          ext s; simp only [mem_inter_iff, mem_Icc, mem_Iic]
          constructor
          · intro h; exact ⟨h.1.1, h.2⟩
          · intro h; exact ⟨⟨h.1, h.2.trans hu.2⟩, h.2⟩
        rw [hset, measureReal_Icc Z hZ u hu.1, smul_eq_mul, mul_comm]

lemma integrableOn_mul_Z (Z : ℝ → ℝ) (hZ : ServiceLaw.IsI0 Z) (t : ℝ) (a : ℝ → ℝ)
    (ha : IntegrableOn a (Icc 0 t)) : IntegrableOn (fun s => a s * Z s) (Icc 0 t) := by
  obtain ⟨hF, _⟩ := stieltjes_facts Z hZ
  have hb : Integrable (fun s => Z (max s 0) * a s) (volume.restrict (Icc 0 t)) := by
    refine Integrable.bdd_mul (c := |Z t|) ha hF.1.measurable.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have h0 : 0 ≤ Z (max s 0) := by
      have := hZ.1 ((Set.mem_Ici.mpr (le_refl (0:ℝ)))) (Set.mem_Ici.mpr (le_max_right s 0))
        (le_max_right s 0)
      rw [hZ.2.1] at this; exact this
    have h1 : Z (max s 0) ≤ Z t :=
      hZ.1 (Set.mem_Ici.mpr (le_max_right s 0)) (Set.mem_Ici.mpr (hs.1.trans hs.2))
        (max_le hs.2 (hs.1.trans hs.2))
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1.trans (le_abs_self _)
  refine IntegrableOn.congr_fun hb (fun s hs => ?_) measurableSet_Icc
  rw [max_eq_left (show (0:ℝ) ≤ s from hs.1), mul_comm]

end MSFRem43

open MSFRem43 in
theorem remark_4_3_correct (S : ServiceLaw) (Z₁ Z₂ : ℝ → ℝ) (hZ₁ : ServiceLaw.IsI0 Z₁)
    (hZ₂ : ServiceLaw.IsI0 Z₂) (f : ℝ → ℝ) (hf : IsCb1 f) (t : ℝ) (ht : 0 ≤ t) :
    bvInt Z₁ Z₂ (Icc 0 t) (fun s => f (t - s) * (1 - S.G (t - s))) =
      f 0 * (Z₁ t - Z₂ t)
      + (∫ s in Icc 0 t, deriv f (t - s) * (1 - S.G (t - s)) * (Z₁ s - Z₂ s))
      - (∫ s in Icc 0 t, f (t - s) * S.g (t - s) * (Z₁ s - Z₂ s)) := by
  have hfc : Continuous f := hf.1.continuous
  have hdfc : Continuous (deriv f) := hf.1.continuous_deriv le_rfl
  have hGc := G_continuous S
  set a1 : ℝ → ℝ := fun s => deriv f (t - s) * (1 - S.G (t - s)) with ha1
  set a2 : ℝ → ℝ := fun s => f (t - s) * S.g (t - s) with ha2
  have hc1 : Continuous a1 := by
    simp only [ha1]; fun_prop
  have hi1 : IntegrableOn a1 (Icc 0 t) := hc1.integrableOn_Icc
  have hi2 : IntegrableOn a2 (Icc 0 t) := by
    have hg' : IntegrableOn (fun s => S.g (t - s)) (Icc 0 t) :=
      (S.integrable_g.comp_sub_left t).integrableOn
    exact IntegrableOn.continuousOn_mul (by fun_prop) hg' isCompact_Icc
  set ψ : ℝ → ℝ := fun s => a1 s - a2 s with hψdef
  have hψ : IntegrableOn ψ (Icc 0 t) := hi1.sub hi2
  -- φ(s) = f 0 + ∫_s^t ψ
  have hφ : ∀ s ∈ Icc 0 t, f (t - s) * (1 - S.G (t - s)) = f 0 + ∫ u in s..t, ψ u := by
    intro s hs
    have hw : 0 ≤ t - s := by linarith [hs.2]
    set w := t - s
    have hsub : ∫ u in s..t, ψ u =
        ∫ v in (0:ℝ)..w, (deriv f v * (1 - S.G v) - f v * S.g v) := by
      have := intervalIntegral.integral_comp_sub_left
        (fun v => deriv f v * (1 - S.G v) - f v * S.g v) (a := s) (b := t) t
      simp only [sub_self] at this
      rw [← this]
    rw [hsub]
    have hfac : AbsolutelyContinuousOnInterval f 0 w :=
      hf.1.contDiffOn.absolutelyContinuousOnInterval
    have hGac : AbsolutelyContinuousOnInterval (fun v => 1 - S.G v) 0 w := by
      have h1 := (S.integrable_g.intervalIntegrable (a := 0) (b := w)
        ).absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
      have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) 0 w := by
        apply LipschitzOnWith.absolutelyContinuousOnInterval (K := 0)
        exact LipschitzWith.lipschitzOnWith (LipschitzWith.const _)
      have := hc.fun_sub h1
      rw [G_fun_eq]
      exact this
    have hIBP := hfac.integral_deriv_mul_eq_sub hGac
    have hcongr : ∫ v in (0:ℝ)..w, (deriv f v * (1 - S.G v) - f v * S.g v) =
        ∫ v in (0:ℝ)..w, (deriv f v * (1 - S.G v) + f v * deriv (fun v => 1 - S.G v) v) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [G_hasDerivAt_ae S] with v hv _
      have : deriv (fun v => 1 - S.G v) v = -S.g v := by
        exact (hv.const_sub 1).deriv
      rw [this]; ring
    rw [hcongr, hIBP, G_zero]
    ring
  have e1 := ibp_single Z₁ hZ₁ t ht _ ψ (f 0) hψ hφ
  have e2 := ibp_single Z₂ hZ₂ t ht _ ψ (f 0) hψ hφ
  unfold bvInt
  rw [e1, e2]
  have j11 := integrableOn_mul_Z Z₁ hZ₁ t a1 hi1
  have j12 := integrableOn_mul_Z Z₂ hZ₂ t a1 hi1
  have j21 := integrableOn_mul_Z Z₁ hZ₁ t a2 hi2
  have j22 := integrableOn_mul_Z Z₂ hZ₂ t a2 hi2
  have k1 : ∫ s in Icc 0 t, a1 s * (Z₁ s - Z₂ s) =
      (∫ s in Icc 0 t, a1 s * Z₁ s) - ∫ s in Icc 0 t, a1 s * Z₂ s := by
    calc ∫ s in Icc 0 t, a1 s * (Z₁ s - Z₂ s) = ∫ s in Icc 0 t, (a1 s * Z₁ s - a1 s * Z₂ s) := by
          congr 1; funext s; ring
      _ = _ := integral_sub j11 j12
  have k2 : ∫ s in Icc 0 t, a2 s * (Z₁ s - Z₂ s) =
      (∫ s in Icc 0 t, a2 s * Z₁ s) - ∫ s in Icc 0 t, a2 s * Z₂ s := by
    calc ∫ s in Icc 0 t, a2 s * (Z₁ s - Z₂ s) = ∫ s in Icc 0 t, (a2 s * Z₁ s - a2 s * Z₂ s) := by
          congr 1; funext s; ring
      _ = _ := integral_sub j21 j22
  have k3 : ∫ s in Icc 0 t, ψ s * Z₁ s =
      (∫ s in Icc 0 t, a1 s * Z₁ s) - ∫ s in Icc 0 t, a2 s * Z₁ s := by
    calc ∫ s in Icc 0 t, ψ s * Z₁ s = ∫ s in Icc 0 t, (a1 s * Z₁ s - a2 s * Z₁ s) := by
          congr 1; funext s; simp only [hψdef]; ring
      _ = _ := integral_sub j11 j21
  have k4 : ∫ s in Icc 0 t, ψ s * Z₂ s =
      (∫ s in Icc 0 t, a1 s * Z₂ s) - ∫ s in Icc 0 t, a2 s * Z₂ s := by
    calc ∫ s in Icc 0 t, ψ s * Z₂ s = ∫ s in Icc 0 t, (a1 s * Z₂ s - a2 s * Z₂ s) := by
          congr 1; funext s; simp only [hψdef]; ring
      _ = _ := integral_sub j12 j22
  have k1' : ∫ s in Icc 0 t, deriv f (t - s) * (1 - S.G (t - s)) * (Z₁ s - Z₂ s) =
      ∫ s in Icc 0 t, a1 s * (Z₁ s - Z₂ s) := rfl
  have k2' : ∫ s in Icc 0 t, f (t - s) * S.g (t - s) * (Z₁ s - Z₂ s) =
      ∫ s in Icc 0 t, a2 s * (Z₁ s - Z₂ s) := rfl
  rw [k1', k2', k1, k2, k3, k4]
  ring

namespace MSFExpLaw

lemma mean_fun_eq : (fun x : ℝ => x * (Ici (0:ℝ)).indicator (fun x => Real.exp (-x)) x) =
    (Ici (0:ℝ)).indicator (fun x => Real.exp (-x) * x ^ ((2:ℝ) - 1)) := by
  funext x
  by_cases hx : 0 ≤ x
  · have : x ^ ((2:ℝ) - 1) = x := by norm_num
    simp [hx, this, mul_comm]
  · simp [hx]

/-- The exponential service law with mean one: g(x) = e^{-x} on [0, ∞). -/
noncomputable def expLaw : ServiceLaw where
  g := (Ici (0:ℝ)).indicator (fun x => Real.exp (-x))
  measurable_g := (Real.measurable_exp.comp measurable_neg).indicator measurableSet_Ici
  g_nonneg := fun x => Set.indicator_nonneg (fun y _ => (Real.exp_pos _).le) x
  g_eq_zero_of_neg := fun x hx => Set.indicator_of_notMem (by simpa using hx) _
  integrable_g := by
    rw [integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    simpa using exp_neg_integrableOn_Ioi 0 one_pos
  integral_g := by
    rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      integral_exp_neg_Ioi_zero]
  integrable_mean := by
    rw [mean_fun_eq, integrable_indicator_iff measurableSet_Ici,
      integrableOn_Ici_iff_integrableOn_Ioi]
    exact Real.GammaIntegral_convergent (by norm_num)
  mean_one := by
    rw [mean_fun_eq, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      ← Real.Gamma_eq_integral (by norm_num), Real.Gamma_two]

lemma expLaw_g_of_nonneg {x : ℝ} (hx : 0 ≤ x) : expLaw.g x = Real.exp (-x) := by
  show (Ici (0:ℝ)).indicator (fun x => Real.exp (-x)) x = _
  simp [hx]

end MSFExpLaw

open MSFRem43 MSFExpLaw in
theorem solution : ¬ (∀ (S : ServiceLaw) (Z₁ Z₂ : ℝ → ℝ) (hZ₁ : ServiceLaw.IsI0 Z₁)
    (hZ₂ : ServiceLaw.IsI0 Z₂) (f : ℝ → ℝ) (hf : IsCb1 f) (t : ℝ) (ht : 0 ≤ t),
    bvInt Z₁ Z₂ (Icc 0 t) (fun s => f (t - s) * (1 - S.G (t - s))) =
      f 0 * (Z₁ t - Z₂ t)
      + ∫ s in Icc 0 t, deriv f (t - s) * (1 - S.G (t - s)) * (Z₁ s - Z₂ s)
      - ∫ s in Icc 0 t, f (t - s) * S.g (t - s) * (Z₁ s - Z₂ s)) := by
  intro H
  have hZ1 : ServiceLaw.IsI0 (fun s : ℝ => s) :=
    ⟨fun a _ b _ hab => hab, rfl,
      fun t _ => continuous_id.continuousWithinAt, fun t _ => ⟨t, continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩⟩
  have hZ2 : ServiceLaw.IsI0 (fun _ : ℝ => (0:ℝ)) :=
    ⟨fun a _ b _ _ => le_rfl, rfl,
      fun t _ => continuousWithinAt_const, fun t _ => ⟨0, tendsto_const_nhds⟩⟩
  have hf1 : IsCb1 (fun _ : ℝ => (1:ℝ)) := ⟨contDiff_const, 1, fun x _ => by simp⟩
  have h1 := H expLaw _ _ hZ1 hZ2 _ hf1 2 (by norm_num)
  have h2 := remark_4_3_correct expLaw _ _ hZ1 hZ2 _ hf1 2 (by norm_num)
  rw [h2] at h1
  set I := ∫ s in Icc (0:ℝ) 2, (fun _ : ℝ => (1:ℝ)) (2 - s) * expLaw.g (2 - s) * (s - 0) with hI
  have hIpos : 0 < I := by
    have hint : IntegrableOn (fun s : ℝ => (fun _ : ℝ => (1:ℝ)) (2 - s) * expLaw.g (2 - s) * (s - 0))
        (Icc 0 2) := by
      have hg' : IntegrableOn (fun s => expLaw.g (2 - s)) (Icc (0:ℝ) 2) :=
        (expLaw.integrable_g.comp_sub_left 2).integrableOn
      have := hg'.mul_continuousOn (g' := fun s : ℝ => s - 0) (by fun_prop) isCompact_Icc
      refine this.congr_fun (fun s _ => by simp) measurableSet_Icc
    rw [hI, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr hint
    · intro s hs
      simp only [one_mul, sub_zero]
      rw [expLaw_g_of_nonneg (by linarith [hs.2])]
      exact mul_pos (Real.exp_pos _) hs.1
    · norm_num
  have hzero : ∀ s : ℝ, deriv (fun _ : ℝ => (1:ℝ)) (2 - s) = 0 := fun s => by simp
  simp only [hzero, zero_mul, integral_zero, add_zero] at h1
  have hc : ∫ s in Icc (0:ℝ) 2, ((0:ℝ) - I) = 2 * (0 - I) := by
    rw [setIntegral_const]
    rw [Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul]; ring
  rw [hc] at h1
  linarith
