-- Prove2me | solution 1 for ManyServerFluid.Uniqueness.theorem_4_1
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-05T19:59:30.623578+00:00
-- url     : https://prove2.me/submissions/d2ddbe94-c98f-4d56-9e6b-482af43f9a15

import Mathlib
import Definitions.Def_ManyServerFluid_Uniqueness_Model
import Definitions.Def_ManyServerFluid_Uniqueness_AgeEquation
open MeasureTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction

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

end MSFRem43
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

namespace MSF35
open MSFRem43 MSFExpLaw

lemma integral_exp_neg_Icc {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in Icc 0 t, Real.exp (-s) = 1 - Real.exp (-t) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_comp_neg (fun x => Real.exp x), integral_exp]
  simp

lemma G_exp {x : ℝ} (hx : 0 ≤ x) : expLaw.G x = 1 - Real.exp (-x) := by
  rw [G_eq_intervalIntegral]
  have : ∫ y in (0:ℝ)..x, expLaw.g y = ∫ y in (0:ℝ)..x, Real.exp (-y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hx] at hy
    exact expLaw_g_of_nonneg hy.1
  rw [this, intervalIntegral.integral_comp_neg (fun x => Real.exp x), integral_exp]
  simp

lemma h_exp {x : ℝ} (hx : 0 ≤ x) : expLaw.h x = 1 := by
  unfold ServiceLaw.h
  rw [G_exp hx, expLaw_g_of_nonneg hx]
  have := Real.exp_pos (-x)
  field_simp
  ring

lemma M_exp : expLaw.M = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro r
  unfold ServiceLaw.M
  have hG : expLaw.G (r : ℝ) < 1 := by
    rw [G_exp r.coe_nonneg]; have := Real.exp_pos (-(r:ℝ)); linarith
  refine le_trans ?_ (le_iSup₂ (f := fun (x : ℝ) (_ : 0 ≤ x ∧ expLaw.G x < 1) =>
    ENNReal.ofReal x) (r : ℝ) ⟨r.coe_nonneg, hG⟩)
  simp

lemma mem_Ages {x : ℝ} (hx : 0 ≤ x) : x ∈ expLaw.Ages :=
  ⟨hx, by rw [M_exp]; exact ENNReal.ofReal_lt_top⟩

lemma Ages_eq : expLaw.Ages = Ici 0 := by
  ext x
  exact ⟨fun h => h.1, fun h => mem_Ages h⟩

lemma measurableSet_Ages : MeasurableSet expLaw.Ages := by
  rw [Ages_eq]; exact measurableSet_Ici

/-- The pure-decay path ν_t = e^{-t} δ_t. -/
noncomputable def nu (t : ℝ) : FiniteMeasure ℝ :=
  ⟨(Real.toNNReal (Real.exp (-t))) • Measure.dirac t, inferInstance⟩

lemma nu_coe (t : ℝ) :
    (nu t : Measure ℝ) = (Real.toNNReal (Real.exp (-t))) • Measure.dirac t := rfl

lemma integral_nu (F : ℝ → ℝ) (t : ℝ) :
    ∫ x, F x ∂(nu t : Measure ℝ) = Real.exp (-t) * F t := by
  rw [nu_coe]
  simp only [integral_smul_nnreal_measure, integral_dirac]
  rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le, smul_eq_mul]

lemma lintegral_nu (F : ℝ → ℝ≥0∞) (t : ℝ) :
    ∫⁻ x, F x ∂(nu t : Measure ℝ) = ENNReal.ofReal (Real.exp (-t)) * F t := by
  rw [nu_coe]
  simp only [lintegral_smul_measure, lintegral_dirac]
  rw [ENNReal.smul_def, smul_eq_mul]
  rfl

lemma mass_nu (t : ℝ) : ((nu t).mass : ℝ) = Real.exp (-t) := by
  rw [FiniteMeasure.mass, nu]
  simp [(Real.exp_pos _).le]

lemma nu_cont : Continuous nu := by
  rw [continuous_iff_continuousAt]
  intro t
  unfold ContinuousAt
  rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  simp only [integral_nu]
  exact ((Real.continuous_exp.comp continuous_neg).mul f.continuous).continuousAt.tendsto

lemma cadlag_of_continuous {α : Type*} [TopologicalSpace α] {p : ℝ → α} (hp : Continuous p) :
    ServiceLaw.IsCadlag p :=
  ⟨fun t _ => hp.continuousWithinAt,
    fun t _ => ⟨p t, hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩⟩

lemma hInt_nu {t : ℝ} (ht : 0 ≤ t) :
    expLaw.hInt nu t = ENNReal.ofReal (1 - Real.exp (-t)) := by
  unfold ServiceLaw.hInt
  rw [setLIntegral_congr_fun measurableSet_Icc (g := fun s => ENNReal.ofReal (Real.exp (-s)))
    (fun s hs => by
      simp only
      rw [lintegral_nu, h_exp hs.1, ENNReal.ofReal_one, mul_one])]
  rw [← ofReal_integral_eq_lintegral_ofReal, integral_exp_neg_Icc ht]
  · exact (Real.continuous_exp.comp continuous_neg).integrableOn_Icc
  · exact Eventually.of_forall (fun s => (Real.exp_pos _).le)

lemma exp_neg_le_one {t : ℝ} (ht : 0 ≤ t) : Real.exp (-t) ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)

lemma hInt_nu_lt_top {t : ℝ} (ht : 0 ≤ t) : expLaw.hInt nu t < ⊤ := by
  rw [hInt_nu ht]; exact ENNReal.ofReal_lt_top

lemma Dbar_nu {t : ℝ} (ht : 0 ≤ t) : expLaw.Dbar nu t = 1 - Real.exp (-t) := by
  unfold ServiceLaw.Dbar
  rw [hInt_nu ht, ENNReal.toReal_ofReal]
  linarith [exp_neg_le_one ht]

lemma Kbar_nu {t : ℝ} (ht : 0 ≤ t) : expLaw.Kbar nu t = 0 := by
  unfold ServiceLaw.Kbar
  rw [mass_nu, mass_nu, Dbar_nu ht]
  simp

lemma Kbar_I0 : ServiceLaw.IsI0 (expLaw.Kbar nu) := by
  refine ⟨fun a ha b hb _ => by rw [Kbar_nu ha, Kbar_nu hb], Kbar_nu le_rfl, ?_, ?_⟩
  · intro t ht
    exact continuousWithinAt_const.congr (fun s hs => Kbar_nu (ht.trans hs)) (Kbar_nu ht)
  · intro t ht
    refine ⟨0, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs
    exact (Kbar_nu hs.1.le).symm

lemma stieltjes_zero {t : ℝ} (ht : 0 ≤ t) :
    (stieltjes (expLaw.Kbar nu)).restrict (Icc 0 t) = 0 := by
  have hfin := finite_restrict _ Kbar_I0 t
  have h := measureReal_Icc _ Kbar_I0 t ht
  rw [Kbar_nu ht] at h
  rw [Measure.restrict_eq_zero]
  have hlt : stieltjes (expLaw.Kbar nu) (Icc 0 t) < ⊤ := by
    have := hfin.measure_univ_lt_top
    rwa [Measure.restrict_apply_univ] at this
  exact (measureReal_eq_zero_iff hlt.ne).mp h

/-- A smooth bump on ℝ, equal to 1 on [-1, 1], positive on (-3, 3), zero outside. -/
noncomputable def bmp : ContDiffBump (0 : ℝ) := ⟨1, 3, by norm_num, by norm_num⟩

lemma bmp_hasDerivAt (x : ℝ) : HasDerivAt bmp (deriv bmp x) x :=
  ((bmp.contDiff (n := 1)).differentiable (by norm_num) x).hasDerivAt

lemma bmp_deriv_cont : Continuous (deriv bmp) :=
  (bmp.contDiff (n := 1)).continuous_deriv le_rfl

lemma bmp_zero {x : ℝ} (hx : 3 < x) : bmp x = 0 ∧ deriv bmp x = 0 := by
  have hd : 3 < dist x 0 := by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; exact hx
  refine ⟨bmp.zero_of_le_dist (by show (3:ℝ) ≤ dist x 0; linarith), ?_⟩
  by_contra hne
  have := support_deriv_subset (f := bmp) (Function.mem_support.mpr hne)
  rw [bmp.tsupport_eq] at this
  have h3 : dist x 0 ≤ 3 := this
  linarith

lemma bmp_pos {x : ℝ} (hx : |x| < 3) : 0 < bmp x :=
  bmp.pos_of_mem_ball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact hx)

noncomputable def phiT (p : ℝ × ℝ) : ℝ := bmp p.1 * bmp p.2

noncomputable def DphiT (p : ℝ × ℝ) : ℝ := deriv bmp p.1 * bmp p.2 + bmp p.1 * deriv bmp p.2

lemma phiT_cont : Continuous phiT := by
  unfold phiT
  exact (bmp.continuous.comp continuous_fst).mul (bmp.continuous.comp continuous_snd)

lemma DphiT_cont : Continuous DphiT := by
  unfold DphiT
  exact ((bmp_deriv_cont.comp continuous_fst).mul (bmp.continuous.comp continuous_snd)).add
    ((bmp.continuous.comp continuous_fst).mul (bmp_deriv_cont.comp continuous_snd))

lemma isTestFn : expLaw.IsTestFn phiT DphiT := by
  refine ⟨phiT_cont.continuousOn, DphiT_cont.continuousOn,
    ⟨3, 3, by rw [M_exp]; exact ENNReal.ofReal_lt_top, ?_⟩, ?_⟩
  · intro p _ h
    unfold phiT DphiT
    rcases h with h | h
    · obtain ⟨h1, h2⟩ := bmp_zero h; simp [h1, h2]
    · obtain ⟨h1, h2⟩ := bmp_zero h; simp [h1, h2]
  · intro p _
    have hA : HasDerivAt (fun ε : ℝ => bmp (p.1 + ε)) (deriv bmp p.1) 0 := by
      have h1 : HasDerivAt (fun ε : ℝ => p.1 + ε) 1 0 := by
        simpa using (hasDerivAt_id (0:ℝ)).const_add p.1
      have h := (bmp_hasDerivAt (p.1 + 0)).comp (0:ℝ) h1
      rw [add_zero, mul_one] at h
      exact h
    have hB : HasDerivAt (fun ε : ℝ => bmp (p.2 + ε)) (deriv bmp p.2) 0 := by
      have h1 : HasDerivAt (fun ε : ℝ => p.2 + ε) 1 0 := by
        simpa using (hasDerivAt_id (0:ℝ)).const_add p.2
      have h := (bmp_hasDerivAt (p.2 + 0)).comp (0:ℝ) h1
      rw [add_zero, mul_one] at h
      exact h
    have hAB := (hA.mul hB).tendsto_slope_zero_right
    simp only [add_zero, zero_add, smul_eq_mul] at hAB
    unfold phiT DphiT
    refine hAB.congr (fun ε => ?_)
    simp only [Pi.mul_apply, add_zero]
    rw [div_eq_inv_mul]

lemma ftc_identity :
    (∫ s in Icc (0:ℝ) 2, Real.exp (-s) * DphiT (s, s))
      - ∫ s in Icc (0:ℝ) 2, Real.exp (-s) * phiT (s, s)
      = Real.exp (-2) * phiT (2, 2) - phiT (0, 0) := by
  have hc1 : Continuous (fun s : ℝ => Real.exp (-s) * DphiT (s, s)) :=
    (Real.continuous_exp.comp continuous_neg).mul
      (DphiT_cont.comp (continuous_id.prodMk continuous_id))
  have hc2 : Continuous (fun s : ℝ => Real.exp (-s) * phiT (s, s)) :=
    (Real.continuous_exp.comp continuous_neg).mul
      (phiT_cont.comp (continuous_id.prodMk continuous_id))
  rw [← integral_sub hc1.integrableOn_Icc hc2.integrableOn_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  have hderiv : ∀ x ∈ uIcc (0:ℝ) 2, HasDerivAt (fun s => Real.exp (-s) * phiT (s, s))
      (Real.exp (-x) * DphiT (x, x) - Real.exp (-x) * phiT (x, x)) x := by
    intro x _
    have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-x)) x := by
      have := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
      rw [mul_neg_one] at this
      exact this
    have hp := (bmp_hasDerivAt x).mul (bmp_hasDerivAt x)
    have := he.mul hp
    unfold phiT DphiT
    show HasDerivAt (fun s => Real.exp (-s) * (bmp s * bmp s)) _ x
    exact this.congr_deriv (by simp only [Pi.mul_apply]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((hc1.sub hc2).intervalIntegrable _ _)]
  simp

lemma J_pos : 0 < ∫ s in Icc (0:ℝ) 2, Real.exp (-s) * phiT (s, s) := by
  have hc2 : Continuous (fun s : ℝ => Real.exp (-s) * phiT (s, s)) :=
    (Real.continuous_exp.comp continuous_neg).mul
      (phiT_cont.comp (continuous_id.prodMk continuous_id))
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (hc2.intervalIntegrable _ _)
  · intro x hx
    have hb : 0 < bmp x := bmp_pos (by rw [abs_of_pos hx.1]; linarith [hx.2])
    unfold phiT
    exact mul_pos (Real.exp_pos _) (mul_pos hb hb)
  · norm_num


lemma not_age : ¬ expLaw.AgeEq (Measure.dirac 0) (fun _ => 0) (fun _ => 0)
    (fun t => (nu t : Measure ℝ)) := by
  intro hage
  have h := hage phiT DphiT isTestFn 2 (by norm_num)
  simp only [bvInt, sub_self, add_zero, integral_nu, integral_dirac] at h
  have hJ : ∫ s in Icc (0:ℝ) 2, Real.exp (-s) * (expLaw.h s * phiT (s, s)) =
      ∫ s in Icc (0:ℝ) 2, Real.exp (-s) * phiT (s, s) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    simp only
    rw [h_exp hs.1, one_mul]
  rw [hJ] at h
  set J := ∫ s in Icc (0:ℝ) 2, Real.exp (-s) * phiT (s, s) with hJdef
  have hc1 : Continuous (fun s : ℝ => Real.exp (-s) * DphiT (s, s)) :=
    (Real.continuous_exp.comp continuous_neg).mul
      (DphiT_cont.comp (continuous_id.prodMk continuous_id))
  have hsplit : ∫ s in Icc (0:ℝ) 2, (Real.exp (-s) * DphiT (s, s) - J) =
      (∫ s in Icc (0:ℝ) 2, Real.exp (-s) * DphiT (s, s)) - 2 * J := by
    rw [integral_sub hc1.integrableOn_Icc (integrableOn_const (by simp)), setIntegral_const,
      Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul]
    ring
  rw [hsplit] at h
  have hftc := ftc_identity
  have hJp := J_pos
  rw [← hJdef] at hftc hJp
  linarith

lemma radon_nu {t : ℝ} (ht : 0 ≤ t) : expLaw.IsRadonAges (nu t : Measure ℝ) := by
  refine ⟨?_, fun m _ => measure_lt_top _ _⟩
  rw [nu_coe]
  simp only [Measure.smul_apply]
  rw [Measure.dirac_apply' _ (measurableSet_Ages).compl]
  simp [mem_Ages ht]

lemma vague_nu : expLaw.IsVagueCadlag (fun t => (nu t : Measure ℝ)) := by
  refine ⟨fun t ht => radon_nu ht, fun f hf => ?_⟩
  simp only [integral_nu]
  have hfc : ContinuousOn f (Ici 0) := by rw [← Ages_eq]; exact hf.1
  have hc : ContinuousOn (fun t => Real.exp (-t) * f t) (Ici 0) :=
    ((Real.continuous_exp.comp continuous_neg).continuousOn).mul hfc
  refine ⟨fun t ht => (hc t ht).mono (Ici_subset_Ici.mpr ht), fun t ht => ?_⟩
  refine ⟨Real.exp (-t) * f t, ?_⟩
  have := (hc t (le_of_lt ht)).continuousAt (Ici_mem_nhds ht)
  exact this.tendsto.mono_left nhdsWithin_le_nhds

lemma hazard_nu : expLaw.HazardBound (fun t => (nu t : Measure ℝ)) := by
  intro m T _
  refine ⟨max T 0, le_max_right _ _, fun φ _ hvan c hc => ?_⟩
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc (0, 0) ⟨mem_Ages le_rfl, Set.mem_Ici.mpr le_rfl⟩)
  simp only [lintegral_nu]
  calc ∫⁻ s in Ici 0, ENNReal.ofReal (Real.exp (-s)) * ENNReal.ofReal (|φ (s, s)| * expLaw.h s)
      ≤ ∫⁻ s in Ici 0, (Iic T).indicator (fun _ => ENNReal.ofReal c) s := by
        apply setLIntegral_mono' measurableSet_Ici
        intro s hs
        have hs' : (0:ℝ) ≤ s := hs
        rw [h_exp hs', mul_one]
        by_cases hsT : s ≤ T
        · rw [Set.indicator_of_mem (show s ∈ Iic T from hsT), ← ENNReal.ofReal_mul
            (Real.exp_pos _).le]
          apply ENNReal.ofReal_le_ofReal
          have h1 := hc (s, s) ⟨mem_Ages hs', hs⟩
          have h2 := exp_neg_le_one hs'
          calc Real.exp (-s) * |φ (s, s)| ≤ 1 * c :=
                mul_le_mul h2 h1 (abs_nonneg _) zero_le_one
            _ = c := one_mul c
        · have h0 := hvan (s, s) ⟨mem_Ages hs', hs⟩ (Or.inr (lt_of_not_ge hsT))
          simp [h0]
    _ = ENNReal.ofReal c * ENNReal.ofReal (T - 0) := by
        rw [lintegral_indicator measurableSet_Iic, setLIntegral_const,
          Measure.restrict_apply measurableSet_Iic, Set.Iic_inter_Ici, Real.volume_Icc]
    _ ≤ ENNReal.ofReal (max T 0 * c) := by
        rw [← ENNReal.ofReal_mul hc0]
        apply ENNReal.ofReal_le_ofReal
        rw [sub_zero, mul_comm]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hc0

end MSF35

open MSFRem43 MSFExpLaw MSF35 in
theorem solution : ¬ (∀ (S : ServiceLaw) (ν : ℝ → Measure ℝ) (hν : S.IsVagueCadlag ν)
    (hh : S.HazardBound ν) (υ0 : Measure ℝ) (hυ0 : S.IsRadonAges υ0)
    (Z₁ Z₂ : ℝ → ℝ) (hZ₁ : ServiceLaw.IsI0 Z₁) (hZ₂ : ServiceLaw.IsI0 Z₂),
    (S.AgeEq υ0 Z₁ Z₂ ν ↔
      ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → ∀ t, 0 ≤ t →
        ∫ x, f x ∂(ν t) = S.ageRep υ0 Z₁ Z₂ f t) ∧
    (IsFiniteMeasure υ0 → S.AgeEq υ0 Z₁ Z₂ ν →
      ∀ f : ℝ →ᵇ ℝ, ∀ t, 0 ≤ t → ∫ x, f x ∂(ν t) = S.ageRep υ0 Z₁ Z₂ f t)) := by
  intro H
  have hZ : ServiceLaw.IsI0 (fun _ : ℝ => (0:ℝ)) :=
    ⟨fun a _ b _ _ => le_rfl, rfl, cadlag_of_continuous continuous_const⟩
  have hυ : expLaw.IsRadonAges (Measure.dirac 0) := by
    have := radon_nu (le_refl (0:ℝ))
    rw [nu_coe] at this
    simpa using this
  have h := (H expLaw _ vague_nu hazard_nu _ hυ _ _ hZ hZ).1
  apply not_age
  apply h.mpr
  intro f _ _ t ht
  unfold ServiceLaw.ageRep
  simp only [bvInt, sub_self, add_zero, integral_nu, integral_dirac, zero_add]
  rw [G_exp ht, G_exp (le_refl (0:ℝ))]
  simp only [zero_add, neg_zero, Real.exp_zero, sub_sub_cancel, sub_self, div_one]
  ring
