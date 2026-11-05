-- Prove2me | solution 1 for NondomArb.Superhedge.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T07:02:15.182965+00:00
-- url     : https://prove2.me/submissions/b0ab905e-f09c-49ae-af1c-9542b2e011e0

import Mathlib
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_OnePeriod
open MeasureTheory Filter Topology NondomArb.Superhedge.OnePeriod
open NondomArb.Superhedge

namespace L35Aux

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

lemma qs_mono {Pset : Set (Measure Ω)} {p q : Ω → Prop} (hp : QS Pset p)
    (h : ∀ ω, p ω → q ω) : QS Pset q := by
  obtain ⟨A, hA, hsub, h0⟩ := hp
  exact ⟨A, hA, fun ω hω => hsub (fun hp => hω (h ω hp)), h0⟩

lemma qs_and {Pset : Set (Measure Ω)} {p q : Ω → Prop} (hp : QS Pset p) (hq : QS Pset q) :
    QS Pset (fun ω => p ω ∧ q ω) := by
  obtain ⟨A, hA, hsub, h0⟩ := hp
  obtain ⟨B, hB, hsubB, h0B⟩ := hq
  refine ⟨A ∪ B, hA.union hB, fun ω hω => ?_,
    fun P hP => measure_union_null (h0 P hP) (h0B P hP)⟩
  by_cases h1 : p ω
  · exact Or.inr (hsubB fun h2 => hω ⟨h1, h2⟩)
  · exact Or.inl (hsub h1)

lemma qs_always {Pset : Set (Measure Ω)} (p : Ω → Prop) (h : ∀ ω, p ω) : QS Pset p :=
  ⟨∅, MeasurableSet.empty, fun ω hω => (hω (h ω)).elim, fun _ _ => measure_empty⟩

lemma qs_exists {Pset : Set (Measure Ω)} (hP : IsConvexModelSet Pset) {p : Ω → Prop}
    (hp : QS Pset p) : ∃ ω, p ω := by
  obtain ⟨A, _, hsub, h0⟩ := hp
  obtain ⟨⟨P, hP0⟩, hprob, _⟩ := hP
  haveI := hprob P hP0
  by_contra hcon
  have hU : (Set.univ : Set Ω) ⊆ A := fun ω _ => hsub (not_exists.mp hcon ω)
  have h1 := measure_mono (μ := P) hU
  rw [measure_univ, h0 P hP0] at h1
  exact absurd h1 (by norm_num)

lemma theta_integrable {Pset : Set (Measure Ω)} {ΔS : Ω → (Fin d → ℝ)} {f : Ω → ℝ}
    {R : Measure Ω} (hR : R ∈ Theta Pset ΔS f) (hΔS : Measurable ΔS) (hf : Measurable f) :
    Integrable ΔS R ∧ Integrable f R := by
  obtain ⟨_, _, hfin⟩ := hR
  refine ⟨⟨hΔS.aestronglyMeasurable, ?_⟩, ⟨hf.aestronglyMeasurable, ?_⟩⟩
  · refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) hfin
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by linarith [abs_nonneg (f ω)])
  · refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) hfin
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (by linarith [norm_nonneg (ΔS ω)])

/-- The argument preceding (3.1): an inequality holding in `R`-expectation for every `R ∈ Θ`
holds `𝒫`-quasi surely. -/
lemma qs_of_forall_theta {Pset : Set (Measure Ω)} (hP : IsConvexModelSet Pset)
    {ΔS : Ω → (Fin d → ℝ)} (hΔS : Measurable ΔS) {f : Ω → ℝ} (hf : Measurable f)
    (X : Ω → ℝ) (hX : Measurable X) (α : ℝ)
    (hint : ∀ R ∈ Theta Pset ΔS f, Integrable X R)
    (h : ∀ R ∈ Theta Pset ΔS f, α ≤ ∫ ω, X ω ∂ R) : QS Pset (fun ω => α ≤ X ω) := by
  set B := {ω | X ω < α} with hBdef
  have hBm : MeasurableSet B := measurableSet_lt hX measurable_const
  refine ⟨B, hBm, fun ω hω => by simpa [B] using hω, fun P hP0 => ?_⟩
  by_contra hPB
  haveI := hP.2.1 P hP0
  let g : Ω → ℝ := fun ω => 1 + ‖ΔS ω‖ + |f ω|
  have hg1 : ∀ ω, 1 ≤ g ω := fun ω => by
    simp only [g]; linarith [norm_nonneg (ΔS ω), abs_nonneg (f ω)]
  have hgm : Measurable g := (measurable_const.add hΔS.norm).add hf.abs
  let w : Ω → ENNReal := B.indicator fun ω => ENNReal.ofReal (g ω)⁻¹
  have hwm : Measurable w := (ENNReal.measurable_ofReal.comp hgm.inv).indicator hBm
  let R0 := P.withDensity w
  set c := R0 Set.univ with hc
  have hc_eq : c = ∫⁻ ω, w ω ∂P := by simp [c, R0, withDensity_apply _ MeasurableSet.univ]
  have hw1 : ∀ ω, w ω ≤ 1 := by
    intro ω
    simp only [w]
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ (hg1 ω))
    · rw [Set.indicator_of_notMem hω]; exact zero_le_one
  have hctop : c ≠ ⊤ := by
    rw [hc_eq]
    refine ne_top_of_le_ne_top (b := ∫⁻ _, (1 : ENNReal) ∂P) ?_ (lintegral_mono hw1)
    simp
  have hc0 : c ≠ 0 := by
    rw [hc_eq]
    intro h0
    rw [lintegral_eq_zero_iff hwm] at h0
    apply hPB
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.mp h0)
    show ¬ (w ω = (0 : Ω → ENNReal) ω)
    simp only [w, Set.indicator_of_mem hω, Pi.zero_apply]
    exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr (by linarith [hg1 ω]))).ne'
  let R : Measure Ω := c⁻¹ • R0
  have hRprob : IsProbabilityMeasure R := by
    constructor
    simp only [R, Measure.smul_apply, smul_eq_mul]
    rw [← hc]; exact ENNReal.inv_mul_cancel hc0 hctop
  have hRP : R ≪ P := fun s hs => by
    simp only [R, Measure.smul_apply, smul_eq_mul]
    rw [withDensity_absolutelyContinuous P w hs, mul_zero]
  have hFm : Measurable fun ω => ENNReal.ofReal (‖ΔS ω‖ + |f ω|) :=
    ENNReal.measurable_ofReal.comp (hΔS.norm.add hf.abs)
  have hRθ : R ∈ Theta Pset ΔS f := by
    refine ⟨hRprob, ⟨P, hP0, hRP⟩, ?_⟩
    simp only [R, lintegral_smul_measure, smul_eq_mul]
    rw [lintegral_withDensity_eq_lintegral_mul _ hwm hFm]
    have hle : ∫⁻ ω, (w * fun ω => ENNReal.ofReal (‖ΔS ω‖ + |f ω|)) ω ∂P ≤ 1 := by
      calc ∫⁻ ω, (w * fun ω => ENNReal.ofReal (‖ΔS ω‖ + |f ω|)) ω ∂P
          ≤ ∫⁻ _, (1 : ENNReal) ∂P := by
            refine lintegral_mono fun ω => ?_
            simp only [Pi.mul_apply, w]
            by_cases hω : ω ∈ B
            · rw [Set.indicator_of_mem hω, ← ENNReal.ofReal_mul (inv_nonneg.mpr
                (by linarith [hg1 ω])), ← ENNReal.ofReal_one]
              refine ENNReal.ofReal_le_ofReal ?_
              have hgpos : 0 < g ω := by linarith [hg1 ω]
              rw [inv_mul_le_iff₀ hgpos, mul_one]
              simp only [g]; linarith
            · rw [Set.indicator_of_notMem hω, zero_mul]; exact zero_le_one
        _ = 1 := by simp
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hc0))
      (lt_of_le_of_lt hle ENNReal.one_lt_top)
  have hRBc : R Bᶜ = 0 := by
    simp only [R, Measure.smul_apply, smul_eq_mul]
    have : R0 Bᶜ = 0 := by
      simp only [R0]
      rw [withDensity_apply _ hBm.compl]
      have : ∫⁻ ω in Bᶜ, w ω ∂P = ∫⁻ ω in Bᶜ, (0 : ENNReal) ∂P :=
        setLIntegral_congr_fun hBm.compl (fun ω hω => Set.indicator_of_notMem hω _)
      rw [this, lintegral_zero]
    rw [this, mul_zero]
  have hRB : R B = 1 := by
    have := measure_add_measure_compl (μ := R) hBm
    rw [hRBc, add_zero, measure_univ] at this; exact this
  have hXR := hint R hRθ
  have hαX := h R hRθ
  have hY : 0 ≤ᵐ[R] fun ω => α - X ω := by
    have : ∀ᵐ ω ∂ R, ω ∈ B := by
      rw [ae_iff]
      have hs : {a | ¬ a ∈ B} = Bᶜ := rfl
      rw [hs, hRBc]
    filter_upwards [this] with ω hω
    have : X ω < α := hω
    simp only [Pi.zero_apply]; linarith
  have hYi : Integrable (fun ω => α - X ω) R := (integrable_const α).sub hXR
  have hpos : 0 < ∫ ω, (α - X ω) ∂ R := by
    rw [integral_pos_iff_support_of_nonneg_ae hY hYi]
    refine lt_of_lt_of_le (by rw [hRB]; exact one_pos) (measure_mono fun ω hω => ?_)
    have : X ω < α := hω
    simp only [Function.mem_support]; linarith
  rw [integral_sub (integrable_const α) hXR] at hpos
  simp at hpos
  linarith

lemma theta_convex {Pset : Set (Measure Ω)} (hP : IsConvexModelSet Pset)
    {ΔS : Ω → (Fin d → ℝ)} (hΔS : Measurable ΔS) {f : Ω → ℝ} (hf : Measurable f) :
    Convex ℝ {p : (Fin d → ℝ) × ℝ |
      ∃ R ∈ Theta Pset ΔS f, p = (∫ ω, ΔS ω ∂ R, ∫ ω, f ω ∂ R)} := by
  rintro _ ⟨R1, hR1, rfl⟩ _ ⟨R2, hR2, rfl⟩ a b ha hb hab
  let a' : NNReal := ⟨a, ha⟩
  have ha1 : a' ≤ 1 := by show a ≤ 1; linarith
  have ha' : ((a' : NNReal) : ℝ) = a := rfl
  have hb' : ((1 - a' : NNReal) : ℝ) = b := by
    rw [NNReal.coe_sub ha1, ha']; simp; linarith
  obtain ⟨i1, i1f⟩ := theta_integrable hR1 hΔS hf
  obtain ⟨i2, i2f⟩ := theta_integrable hR2 hΔS hf
  obtain ⟨hp1, ⟨P1, hP1, hac1⟩, hfin1⟩ := hR1
  obtain ⟨hp2, ⟨P2, hP2, hac2⟩, hfin2⟩ := hR2
  refine ⟨a' • R1 + (1 - a') • R2, ⟨⟨?_⟩, ⟨a' • P1 + (1 - a') • P2,
    hP.2.2 P1 hP1 P2 hP2 a' ha1, ?_⟩, ?_⟩, ?_⟩
  · simp only [Measure.add_apply, Measure.smul_apply, measure_univ, ENNReal.smul_def,
      smul_eq_mul, mul_one]
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le ha1, ENNReal.coe_one]
  · intro s hs
    simp only [Measure.add_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
      add_eq_zero, mul_eq_zero] at hs ⊢
    obtain ⟨h1, h2⟩ := hs
    refine ⟨?_, ?_⟩
    · rcases h1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (hac1 h1)
    · rcases h2 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (hac2 h2)
  · rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
    simp only [ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.coe_lt_top hfin1,
      ENNReal.mul_lt_top ENNReal.coe_lt_top hfin2⟩
  · rw [integral_add_measure i1.smul_measure_nnreal i2.smul_measure_nnreal,
      integral_add_measure i1f.smul_measure_nnreal i2f.smul_measure_nnreal,
      integral_smul_nnreal_measure, integral_smul_nnreal_measure,
      integral_smul_nnreal_measure, integral_smul_nnreal_measure]
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, NNReal.smul_def, ha', hb']
    · simp only [Prod.snd_add, Prod.smul_snd, NNReal.smul_def, ha', hb']

end L35Aux

theorem solution {Ω : Type*} [MeasurableSpace Ω] (Pset : Set (Measure Ω))
    (hP : IsConvexModelSet Pset) {d : ℕ} (ΔS : Ω → (Fin d → ℝ)) (hΔS : Measurable ΔS)
    (hNA : NA Pset ΔS) (f : Ω → ℝ) (hf : Measurable f) (hπ : price Pset ΔS f = 0) :
    ∃ R : ℕ → Measure Ω, (∀ n, R n ∈ Theta Pset ΔS f) ∧
      Tendsto (fun n => ∫ ω, ΔS ω ∂ (R n)) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ ω, f ω ∂ (R n)) atTop (𝓝 0) := by
  classical
  set Γ : Set ((Fin d → ℝ) × ℝ) :=
    {p | ∃ R ∈ Theta Pset ΔS f, p = (∫ ω, ΔS ω ∂ R, ∫ ω, f ω ∂ R)} with hΓ
  have hconv : Convex ℝ Γ := L35Aux.theta_convex hP hΔS hf
  have h0 : (0 : (Fin d → ℝ) × ℝ) ∈ closure Γ := by
    by_contra h0
    obtain ⟨L, u, hLu, hLb⟩ :=
      geometric_hahn_banach_point_closed hconv.closure isClosed_closure h0
    rw [map_zero] at hLu
    let X : Ω → ℝ := fun ω => L (ΔS ω, f ω)
    have hXm : Measurable X := L.continuous.measurable.comp (hΔS.prodMk hf)
    have hXint : ∀ R ∈ Theta Pset ΔS f, Integrable X R ∧
        ∫ ω, X ω ∂ R = L (∫ ω, ΔS ω ∂ R, ∫ ω, f ω ∂ R) := by
      intro R hR
      obtain ⟨h1, h2⟩ := L35Aux.theta_integrable hR hΔS hf
      have hpair : Integrable (fun ω => (ΔS ω, f ω)) R := h1.prodMk h2
      exact ⟨L.integrable_comp hpair, by rw [L.integral_comp_comm hpair, integral_pair h1 h2]⟩
    have hqs := L35Aux.qs_of_forall_theta hP hΔS hf X hXm u (fun R hR => (hXint R hR).1)
      (fun R hR => by rw [(hXint R hR).2]; exact (hLb _ (subset_closure ⟨R, hR, rfl⟩)).le)
    let y : Fin d → ℝ := fun i => L (fun j => if i = j then 1 else 0, 0)
    let z : ℝ := L (0, 1)
    have hdec : ∀ ω, X ω = y ⬝ᵥ ΔS ω + z * f ω := by
      intro ω
      have e1 : (ΔS ω, f ω) = (ΔS ω, (0:ℝ)) + f ω • ((0 : Fin d → ℝ), (1:ℝ)) := by
        ext <;> simp
      simp only [X]
      rw [e1, map_add, map_smul, smul_eq_mul]
      congr 1
      · have := LinearMap.pi_apply_eq_sum_univ
          ((L : ((Fin d → ℝ) × ℝ) →L[ℝ] ℝ).toLinearMap.comp
            (LinearMap.inl ℝ (Fin d → ℝ) ℝ)) (ΔS ω)
        simp only [LinearMap.comp_apply, LinearMap.inl_apply, ContinuousLinearMap.coe_coe,
          smul_eq_mul] at this
        rw [this, dotProduct]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [y]; ring
      · simp only [z]; ring
    have hu : 0 < u := hLu
    by_cases hz : z < 0
    · have hz' : 0 < -z := by linarith
      have hle : price Pset ΔS f ≤ ((u / z : ℝ) : EReal) := by
        refine sInf_le ⟨u / z, rfl, (-1/z) • y, L35Aux.qs_mono hqs fun ω h => ?_⟩
        rw [hdec] at h
        rw [smul_dotProduct, smul_eq_mul]
        have e : (-z) * (u / z + (-1/z) * (y ⬝ᵥ ΔS ω)) = y ⬝ᵥ ΔS ω - u := by
          have hzne : z ≠ 0 := hz.ne
          field_simp; ring
        refine le_of_mul_le_mul_left ?_ hz'
        rw [e]; linarith
      rw [hπ] at hle
      have : (0:ℝ) ≤ u / z := by exact_mod_cast hle
      have : u / z < 0 := div_neg_of_pos_of_neg hu hz
      linarith
    · have hz0 : 0 ≤ z := not_lt.mp hz
      have hH : ∃ H : Fin d → ℝ, QS Pset (fun ω => z * f ω ≤ u / 2 + H ⬝ᵥ ΔS ω) := by
        by_cases hzz : z = 0
        · refine ⟨0, L35Aux.qs_always _ fun ω => ?_⟩
          rw [hzz]; simp; linarith
        · have hzp : 0 < z := lt_of_le_of_ne hz0 (Ne.symm hzz)
          have hlt : price Pset ΔS f < ((u / (2 * z) : ℝ) : EReal) := by
            rw [hπ]; exact_mod_cast (by positivity : (0:ℝ) < u / (2 * z))
          obtain ⟨_, ⟨x', rfl, H', hq⟩, hxlt⟩ := sInf_lt_iff.mp hlt
          have hx' : x' < u / (2 * z) := by exact_mod_cast hxlt
          refine ⟨z • H', L35Aux.qs_mono hq fun ω h => ?_⟩
          rw [smul_dotProduct, smul_eq_mul]
          have h1 : z * x' < u / 2 := by
            have := mul_lt_mul_of_pos_left hx' hzp
            rwa [show z * (u / (2 * z)) = u / 2 by field_simp] at this
          nlinarith
      obtain ⟨H, hH⟩ := hH
      have hge : QS Pset (fun ω => u / 2 ≤ (y + H) ⬝ᵥ ΔS ω) :=
        L35Aux.qs_mono (L35Aux.qs_and hqs hH) fun ω h => by
          rw [hdec] at h; rw [add_dotProduct]; linarith [h.1, h.2]
      have hzero := hNA (y + H) (L35Aux.qs_mono hge fun ω h => by linarith)
      obtain ⟨ω, h1, h2⟩ := L35Aux.qs_exists hP (L35Aux.qs_and hge hzero)
      linarith
  have hseq : ∀ n : ℕ, ∃ R ∈ Theta Pset ΔS f,
      ‖((∫ ω, ΔS ω ∂ R, ∫ ω, f ω ∂ R) : (Fin d → ℝ) × ℝ)‖ < 1 / ((n:ℝ)+1) := by
    intro n
    obtain ⟨p, hpΓ, hp⟩ := Metric.mem_closure_iff.mp h0 (1/((n:ℝ)+1)) (by positivity)
    obtain ⟨R, hR, rfl⟩ := hpΓ
    refine ⟨R, hR, ?_⟩
    rwa [dist_comm, dist_zero_right] at hp
  choose R hR hRn using hseq
  refine ⟨R, hR, ?_, ?_⟩
  · exact squeeze_zero_norm (fun n => (norm_fst_le _).trans (hRn n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · exact squeeze_zero_norm (fun n => (norm_snd_le _).trans (hRn n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
