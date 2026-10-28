-- Prove2me | solution 1 for MDPFinance.LPDuality.theorem_7_5_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:56:58.559475+00:00
-- url     : https://prove2.me/submissions/4388d8b6-4bab-460e-be44-31827427d580

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Bounding
import Definitions.Def_MDPFinance_LPDuality_LP


open MeasureTheory ProbabilityTheory
open MDPFinance.LPDuality

namespace LP756Aux

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

theorem ae_mem_D (M : MarkovDecisionModel E A) (b : E → ℝ) (hb1 : ∀ x, 1 ≤ b x)
    (μ : Measure (E × A)) (hμ : μ ∈ Mb M b) : ∀ᵐ xa ∂μ, xa ∈ M.D := by
  have hfin : μ Set.univ ≠ ⊤ := by
    refine ne_top_of_le_ne_top hμ.2.ne ?_
    calc μ Set.univ = ∫⁻ _, 1 ∂μ := by simp
      _ ≤ ∫⁻ xa, ENNReal.ofReal (b xa.1) ∂μ := by
        apply lintegral_mono; intro xa
        simpa using ENNReal.ofReal_le_ofReal (hb1 xa.1)
  rw [ae_iff]
  have : {a | ¬ a ∈ M.D} = M.Dᶜ := rfl
  rw [this, measure_compl M.hD_meas (ne_top_of_le_ne_top hfin (measure_mono (Set.subset_univ _))),
    hμ.1, tsub_self]

theorem integrable_of_bound (M : MarkovDecisionModel E A) (b : E → ℝ) (hbm : Measurable b)
    (hb0 : ∀ x, 0 ≤ b x) (hb1 : ∀ x, 1 ≤ b x)
    (μ : Measure (E × A)) (hμ : μ ∈ Mb M b) (f : E × A → ℝ) (hf : AEStronglyMeasurable f μ)
    (C : ℝ) (hC : ∀ xa ∈ M.D, |f xa| ≤ C * b xa.1) : Integrable f μ := by
  have hbI : Integrable (fun xa : E × A => b xa.1) μ :=
    ⟨(hbm.comp measurable_fst).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => hb0 _)).2 hμ.2⟩
  refine (hbI.const_mul C).mono' hf ?_
  filter_upwards [ae_mem_D M b hb1 μ hμ] with xa hxa
  simpa [Real.norm_eq_abs] using hC xa hxa

theorem int_bound (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (v : E → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hv : ∀ x, |v x| ≤ c * b x) (xa : E × A) (hxa : xa ∈ M.D) :
    |∫ x', v x' ∂(M.Q xa)| ≤ c * (αb * b xa.1) := by
  have := M.isMarkovQ
  have hlt : ∫⁻ x', ENNReal.ofReal (b x') ∂(M.Q xa) < ⊤ :=
    lt_of_le_of_lt (hb.hQ xa hxa) ENNReal.ofReal_lt_top
  have hbI : Integrable b (M.Q xa) :=
    ⟨hb.hb_meas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => hb.hb_nonneg _)).2 hlt⟩
  have h1 : ‖∫ x', v x' ∂(M.Q xa)‖ ≤ ∫ x', c * b x' ∂(M.Q xa) :=
    norm_integral_le_of_norm_le (hbI.const_mul c) (ae_of_all _ fun x => by
      simpa [Real.norm_eq_abs] using hv x)
  have h2 : ∫ x', b x' ∂(M.Q xa) ≤ αb * b xa.1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hb.hb_nonneg)
      hb.hb_meas.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hb.hαb (hb.hb_nonneg _)) (hb.hQ xa hxa)
  rw [integral_const_mul] at h1
  rw [← Real.norm_eq_abs]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hc)

/-- integrability of `xa ↦ v xa.1 - β ∫ v dQ(xa)` and of `r`. -/
theorem integrable_gv (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (hb1 : ∀ x, 1 ≤ b x)
    (μ : Measure (E × A)) (hμ : μ ∈ Mb M b) (v : E → ℝ) (hv : v ∈ IBb b) :
    Integrable (fun xa : E × A => v xa.1 - M.β * ∫ x', v x' ∂(M.Q xa)) μ := by
  obtain ⟨hvm, c, hc, hvc⟩ := hv
  refine integrable_of_bound M b hb.hb_meas hb.hb_nonneg hb1 μ hμ _ ?_ (c + M.β * (c * αb)) ?_
  · refine ((hvm.comp measurable_fst).stronglyMeasurable.sub
      (stronglyMeasurable_const.mul ?_)).aestronglyMeasurable
    exact hvm.stronglyMeasurable.integral_kernel
  · intro xa hxa
    have h1 := int_bound M b cr αb hb v c hc hvc xa hxa
    have h2 := hvc xa.1
    have hβ := M.hβ0
    calc |v xa.1 - M.β * ∫ x', v x' ∂(M.Q xa)|
        ≤ |v xa.1| + |M.β * ∫ x', v x' ∂(M.Q xa)| := abs_sub _ _
      _ = |v xa.1| + M.β * |∫ x', v x' ∂(M.Q xa)| := by rw [abs_mul, abs_of_pos hβ]
      _ ≤ c * b xa.1 + M.β * (c * (αb * b xa.1)) := by gcongr
      _ = (c + M.β * (c * αb)) * b xa.1 := by ring

theorem integrable_r (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (hb1 : ∀ x, 1 ≤ b x)
    (μ : Measure (E × A)) (hμ : μ ∈ Mb M b) : Integrable M.r μ :=
  integrable_of_bound M b hb.hb_meas hb.hb_nonneg hb1 μ hμ _
    M.hr_meas.aestronglyMeasurable cr hb.hr

theorem weak (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (hb1 : ∀ x, 1 ≤ b x)
    (IMs : Set (E → ℝ)) (hIM : IsClosedSubspaceOf b IMs) (p : Measure E)
    (v : E → ℝ) (hv : v ∈ ZP M IMs) (μ : Measure (E × A)) (hμ : μ ∈ ZD M b IMs p) :
    ∫ xa, M.r xa ∂μ ≤ ∫ x, v x ∂p := by
  rw [← hμ.2 v hv.1]
  apply integral_mono_ae (integrable_r M b cr αb hb hb1 μ hμ.1)
    (integrable_gv M b cr αb hb hb1 μ hμ.1 v (hIM.1 hv.1))
  filter_upwards [ae_mem_D M b hb1 μ hμ.1] with xa hxa
  have := hv.2 xa hxa
  linarith

theorem pk_succ (M : MarkovDecisionModel E A) (f : E → A) (k : ℕ) :
    ∀ p : Measure E, pkStep M f (k + 1) p = (pkStep M f k p).bind (fun x => M.Q (x, f x)) := by
  induction k with
  | zero => intro p; rfl
  | succ k ih =>
    intro p
    show pkStep M f (k + 1) (p.bind (fun x => M.Q (x, f x))) = _
    rw [ih]; rfl

theorem lint_bind_le (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (f : E → A) (hf : Measurable f)
    (hfD : ∀ x, (x, f x) ∈ M.D) (q : Measure E) :
    ∫⁻ x, ENNReal.ofReal (b x) ∂(q.bind (fun x => M.Q (x, f x))) ≤
      ENNReal.ofReal αb * ∫⁻ x, ENNReal.ofReal (b x) ∂q := by
  have hK : (fun x => M.Q (x, f x)) = ⇑(M.Q.comap (fun x => (x, f x)) (measurable_id.prodMk hf)) := by
    funext x; rw [Kernel.comap_apply]
  rw [hK, Measure.lintegral_bind (Kernel.aemeasurable _) (hb.hb_meas.ennreal_ofReal).aemeasurable,
    ← lintegral_const_mul _ (hb.hb_meas.ennreal_ofReal)]
  apply lintegral_mono
  intro x
  simp only [Kernel.comap_apply]
  rw [← ENNReal.ofReal_mul hb.hαb]
  exact hb.hQ _ (hfD x)

theorem lint_pk_le (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (f : E → A) (hf : Measurable f)
    (hfD : ∀ x, (x, f x) ∈ M.D) (p : Measure E) (k : ℕ) :
    ∫⁻ x, ENNReal.ofReal (b x) ∂(pkStep M f k p) ≤
      ENNReal.ofReal αb ^ k * ∫⁻ x, ENNReal.ofReal (b x) ∂p := by
  induction k with
  | zero => simp [pkStep]
  | succ k ih =>
    rw [pk_succ]
    refine (lint_bind_le M b cr αb hb f hf hfD _).trans ?_
    rw [pow_succ', mul_assoc]
    gcongr

theorem occ_Mb (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (hαb : M.β * αb < 1) (f : E → A) (hf : Measurable f)
    (hfD : ∀ x, (x, f x) ∈ M.D) (p : Measure E)
    (hpb : ∫⁻ x, ENNReal.ofReal (b x) ∂p < ⊤) : occMeasure M f p ∈ Mb M b := by
  have hφ : Measurable (fun x : E => (x, f x)) := measurable_id.prodMk hf
  have hβ0 := M.hβ0
  constructor
  · have h0 : occMeasure M f p M.Dᶜ = 0 := by
      unfold occMeasure
      rw [Measure.sum_apply _ M.hD_meas.compl]
      apply ENNReal.tsum_eq_zero.2
      intro k
      rw [Measure.smul_apply, Measure.map_apply hφ M.hD_meas.compl]
      have : (fun x : E => (x, f x)) ⁻¹' M.Dᶜ = ∅ := by
        ext x; simp [hfD x]
      simp [this]
    rw [← measure_add_measure_compl M.hD_meas, h0, add_zero]
  · unfold occMeasure
    rw [lintegral_sum_measure]
    simp_rw [lintegral_smul_measure]
    have hm : Measurable (fun xa : E × A => ENNReal.ofReal (b xa.1)) :=
      (hb.hb_meas.comp measurable_fst).ennreal_ofReal
    simp_rw [lintegral_map hm hφ]
    calc ∑' k, ENNReal.ofReal (M.β ^ k) • ∫⁻ x, ENNReal.ofReal (b x) ∂(pkStep M f k p)
        ≤ ∑' k, ENNReal.ofReal (M.β * αb) ^ k * ∫⁻ x, ENNReal.ofReal (b x) ∂p := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          rw [ENNReal.ofReal_mul hβ0.le, mul_pow, ← ENNReal.ofReal_pow hβ0.le, mul_assoc,
            smul_eq_mul]
          gcongr
          exact lint_pk_le M b cr αb hb f hf hfD p k
      _ = (1 - ENNReal.ofReal (M.β * αb))⁻¹ * ∫⁻ x, ENNReal.ofReal (b x) ∂p := by
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
      _ < ⊤ := ENNReal.mul_lt_top
          (ENNReal.inv_lt_top.2 (tsub_pos_of_lt (ENNReal.ofReal_lt_one.2 hαb))) hpb

theorem occ_ident (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (hb1 : ∀ x, 1 ≤ b x) (hαb : M.β * αb < 1)
    (f : E → A) (hf : Measurable f)
    (hfD : ∀ x, (x, f x) ∈ M.D) (p : Measure E)
    (hpb : ∫⁻ x, ENNReal.ofReal (b x) ∂p < ⊤) (v : E → ℝ) (hv : v ∈ IBb b) :
    ∫ xa, (v xa.1 - M.β * ∫ x', v x' ∂(M.Q xa)) ∂(occMeasure M f p) = ∫ x, v x ∂p := by
  have hφ : Measurable (fun x : E => (x, f x)) := measurable_id.prodMk hf
  have hβ0 := M.hβ0
  have hMb := occ_Mb M b cr αb hb hαb f hf hfD p hpb
  have hgI := integrable_gv M b cr αb hb hb1 _ hMb v hv
  obtain ⟨hvm, c, hc, hvc⟩ := hv
  obtain ⟨K, hK⟩ : ∃ K : Kernel E E, ∀ x, K x = M.Q (x, f x) :=
    ⟨M.Q.comap _ hφ, fun x => Kernel.comap_apply _ _ _⟩
  have hKf : (fun x => M.Q (x, f x)) = ⇑K := by funext x; rw [hK]
  have hIk : ∀ k, ∫⁻ x, ENNReal.ofReal (b x) ∂(pkStep M f k p) < ⊤ := fun k =>
    (lint_pk_le M b cr αb hb f hf hfD p k).trans_lt
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hpb)
  have hbI : ∀ k, Integrable b (pkStep M f k p) := fun k =>
    ⟨hb.hb_meas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ hb.hb_nonneg)).2 (hIk k)⟩
  have hbint : ∀ k, ∫ x, b x ∂(pkStep M f k p) ≤
      αb ^ k * (∫⁻ x, ENNReal.ofReal (b x) ∂p).toReal := by
    intro k
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hb.hb_nonneg)
      hb.hb_meas.aestronglyMeasurable]
    have := ENNReal.toReal_mono
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hpb).ne
      (lint_pk_le M b cr αb hb f hf hfD p k)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hb.hαb] at this
  have hvI : ∀ k, Integrable v (pkStep M f k p) := fun k =>
    ((hbI k).const_mul c).mono' hvm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hvc x)
  have hwI : ∀ k, Integrable (fun x => ∫ x', v x' ∂(M.Q (x, f x))) (pkStep M f k p) := fun k =>
    ((hbI k).const_mul (c * αb)).mono'
      ((hvm.stronglyMeasurable.integral_kernel).comp_measurable hφ).aestronglyMeasurable
      (ae_of_all _ fun x => by
        have := int_bound M b cr αb hb v c hc hvc (x, f x) (hfD x)
        rw [Real.norm_eq_abs]
        calc _ ≤ _ := this
          _ = _ := by ring)
  have hstep : ∀ k, ∫ x, (∫ x', v x' ∂(M.Q (x, f x))) ∂(pkStep M f k p) =
      ∫ x, v x ∂(pkStep M f (k + 1) p) := by
    intro k
    have e : pkStep M f (k + 1) p = (K ∘ₖ Kernel.const Unit (pkStep M f k p)) () := by
      rw [← Measure.comp_eq_comp_const_apply, pk_succ, hKf]
    have hi : Integrable v ((K ∘ₖ Kernel.const Unit (pkStep M f k p)) ()) := e ▸ hvI (k + 1)
    rw [e, Kernel.integral_comp hi, Kernel.const_apply]
    simp only [hK]
  have hgm : StronglyMeasurable (fun xa : E × A => v xa.1 - M.β * ∫ x', v x' ∂(M.Q xa)) :=
    (hvm.comp measurable_fst).stronglyMeasurable.sub
      (stronglyMeasurable_const.mul hvm.stronglyMeasurable.integral_kernel)
  have hterm : ∀ k, ∫ xa, (v xa.1 - M.β * ∫ x', v x' ∂(M.Q xa))
      ∂(ENNReal.ofReal (M.β ^ k) • (pkStep M f k p).map (fun x => (x, f x))) =
      M.β ^ k * ∫ x, v x ∂(pkStep M f k p) -
        M.β ^ (k + 1) * ∫ x, v x ∂(pkStep M f (k + 1) p) := by
    intro k
    rw [integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg hβ0.le k),
      integral_map hφ.aemeasurable hgm.aestronglyMeasurable, smul_eq_mul,
      integral_sub (hvI k) ((hwI k).const_mul _), integral_const_mul, hstep]
    ring
  have hs := (hasSum_integral_measure (μ := fun k =>
    ENNReal.ofReal (M.β ^ k) • (pkStep M f k p).map (fun x => (x, f x))) hgI).tendsto_sum_nat
  simp_rw [hterm] at hs
  set F : ℕ → ℝ := fun k => M.β ^ k * ∫ x, v x ∂(pkStep M f k p) with hF
  have hs' : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (F i - F (i + 1)))
      Filter.atTop (nhds (∫ xa, (v xa.1 - M.β * ∫ x', v x' ∂(M.Q xa)) ∂(occMeasure M f p))) := hs
  simp_rw [Finset.sum_range_sub'] at hs'
  have hF0 : Filter.Tendsto F Filter.atTop (nhds 0) := by
    set I0 := (∫⁻ x, ENNReal.ofReal (b x) ∂p).toReal
    have hlim : Filter.Tendsto (fun n => c * I0 * (M.β * αb) ^ n) Filter.atTop (nhds 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg hβ0.le hb.hαb) hαb
      simpa using this.const_mul (c * I0)
    refine squeeze_zero_norm (fun n => ?_) hlim
    have ha : ‖∫ x, v x ∂(pkStep M f n p)‖ ≤ c * ∫ x, b x ∂(pkStep M f n p) := by
      rw [← integral_const_mul]
      exact norm_integral_le_of_norm_le ((hbI n).const_mul c)
        (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hvc x)
    have hb' := hbint n
    simp only [hF, norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hβ0] at ha ⊢
    calc M.β ^ n * |∫ x, v x ∂(pkStep M f n p)|
        ≤ M.β ^ n * (c * (αb ^ n * I0)) := by
          gcongr; exact ha.trans (mul_le_mul_of_nonneg_left hb' hc)
      _ = c * I0 * (M.β * αb) ^ n := by ring
  have := tendsto_nhds_unique hs' (tendsto_const_nhds.sub hF0)
  rw [this]
  simp [hF, pkStep]

end LP756Aux

open LP756Aux in
theorem solution {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (hb1 : ∀ x, 1 ≤ b x)
    (hαb : M.β * αb < 1) (IMs : Set (E → ℝ)) (hIM : IsClosedSubspaceOf b IMs) (hbIM : b ∈ IMs)
    (p : Measure E) (hpb : ∫⁻ x, ENNReal.ofReal (b x) ∂p < ⊤) :
    (ZP M IMs).Nonempty ∧ (ZD M b IMs p).Nonempty ∧
      (⊥ : EReal) < valD M b IMs p ∧ valD M b IMs p ≤ valP M IMs p ∧
      valP M IMs p < (⊤ : EReal) := by
  obtain ⟨f, hf, hfD⟩ := M.hD_graph
  have hβ0 := M.hβ0
  have hμ : occMeasure M f p ∈ ZD M b IMs p :=
    ⟨occ_Mb M b cr αb hb hαb f hf hfD p hpb,
      fun v hv => occ_ident M b cr αb hb hb1 hαb f hf hfD p hpb v (hIM.1 hv)⟩
  have hpos : 0 < 1 - M.β * αb := by linarith
  have hC : 0 ≤ cr / (1 - M.β * αb) := div_nonneg hb.hcr hpos.le
  have hCe : cr / (1 - M.β * αb) * (1 - M.β * αb) = cr := div_mul_cancel₀ _ hpos.ne'
  have hw : (cr / (1 - M.β * αb)) • b ∈ ZP M IMs := by
    refine ⟨hIM.2.2.2.1 _ b hbIM, fun xa hxa => ?_⟩
    have h1 := (le_abs_self _).trans (hb.hr xa hxa)
    have h2 := int_bound M b cr αb hb b 1 zero_le_one
      (fun x => by rw [abs_of_nonneg (hb.hb_nonneg x)]; simp) xa hxa
    have h3 := mul_le_mul_of_nonneg_left ((le_abs_self _).trans h2) (mul_nonneg hβ0.le hC)
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul]
    have h4 : cr * b xa.1 = cr / (1 - M.β * αb) * b xa.1 -
        M.β * (cr / (1 - M.β * αb)) * (1 * (αb * b xa.1)) := by
      calc cr * b xa.1 = (cr / (1 - M.β * αb) * (1 - M.β * αb)) * b xa.1 := by rw [hCe]
        _ = _ := by ring
    nlinarith
  have hDP : valD M b IMs p ≤ valP M IMs p :=
    iSup₂_le fun μ' hμ' => le_iInf₂ fun v' hv' =>
      EReal.coe_le_coe_iff.2 (weak M b cr αb hb hb1 IMs hIM p v' hv' μ' hμ')
  refine ⟨⟨_, hw⟩, ⟨_, hμ⟩, ?_, hDP, ?_⟩
  · exact (EReal.bot_lt_coe _).trans_le
      (le_iSup₂ (f := fun μ' _ => ((∫ xa, M.r xa ∂μ' : ℝ) : EReal)) _ hμ)
  · exact (iInf₂_le _ hw).trans_lt (EReal.coe_lt_top _)
