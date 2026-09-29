-- Prove2me | solution 1 for HighDimStat.Concentration.bernstein_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T15:54:49.580488+00:00
-- url     : https://prove2.me/submissions/5f671789-fb9d-4540-a17b-353de9de0563

import Mathlib
import Definitions.Def_HighDimStat_Concentration_phiEntropy

open MeasureTheory
open MeasureTheory ProbabilityTheory Filter Topology

namespace HighDimStat.Concentration

lemma exp_secant_ge (ε y : ℝ) (hε : 0 < ε) : y ≤ (Real.exp (ε * y) - 1) / ε := by
  rw [le_div_iff₀ hε]
  have := Real.add_one_le_exp (ε * y)
  linarith

lemma exp_secant_mono (ε δ y : ℝ) (hε : 0 < ε) (hεδ : ε ≤ δ) :
    (Real.exp (ε * y) - 1) / ε ≤ (Real.exp (δ * y) - 1) / δ := by
  have hδ : 0 < δ := lt_of_lt_of_le hε hεδ
  set s := ε / δ with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : 0 ≤ 1 - s := by rw [sub_nonneg, hs, div_le_one hδ]; exact hεδ
  have hc := convexOn_exp.2 (Set.mem_univ (δ * y)) (Set.mem_univ 0) hs0 hs1 (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hc
  have he : s * (δ * y) = ε * y := by rw [hs]; field_simp
  rw [he] at hc
  rw [div_le_div_iff₀ hε hδ]
  have : ε = s * δ := by rw [hs]; field_simp
  rw [this] at hc ⊢
  nlinarith [Real.exp_pos (δ * y)]

lemma exp_secant_tendsto (y : ℝ) :
    Tendsto (fun ε => (Real.exp (ε * y) - 1) / ε) (𝓝[>] 0) (𝓝 y) := by
  have hd : HasDerivAt (fun t => Real.exp (t * y)) (Real.exp (0 * y) * y) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).mul_const y).exp
    simpa using this
  have := hd.tendsto_slope_zero_right
  simp only [zero_mul, Real.exp_zero, one_mul, zero_add, smul_eq_mul] at this
  refine this.congr (fun ε => ?_)
  rw [div_eq_inv_mul]

lemma aemeas_of_exp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (X : Ω → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (h : Integrable (fun ω => Real.exp (δ * X ω)) P) : AEMeasurable X P := by
  have h1 := h.aestronglyMeasurable.aemeasurable
  have : X = fun ω => Real.log (Real.exp (δ * X ω)) / δ := by
    funext ω; rw [Real.log_exp]; field_simp
  rw [this]; exact h1.log.div_const δ

lemma mgf_tendsto_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hint : ∀ ε ∈ Set.Ioc 0 δ, Integrable (fun ω => Real.exp (ε * X ω)) P) :
    Tendsto (fun ε => ∫ ω, Real.exp (ε * X ω) ∂P) (𝓝[>] 0) (𝓝 1) := by
  have hXm := aemeas_of_exp X hδ (hint δ ⟨hδ, le_rfl⟩)
  have h1 : (1 : ℝ) = ∫ ω, Real.exp (0 * X ω) ∂P := by simp
  rw [h1]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ω => 1 + Real.exp (δ * X ω)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall (fun ε => by fun_prop)
  · filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    refine Eventually.of_forall (fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rcases le_or_gt 0 (X ω) with hx | hx
    · have : Real.exp (ε * X ω) ≤ Real.exp (δ * X ω) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hε.2.le hx)
      linarith [Real.exp_pos (δ * X ω)]
    · have : Real.exp (ε * X ω) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hε.1])
      linarith [Real.exp_pos (δ * X ω)]
  · exact (integrable_const 1).add (hint δ ⟨hδ, le_rfl⟩)
  · refine Eventually.of_forall (fun ω => ?_)
    have : Continuous (fun ε : ℝ => Real.exp (ε * X ω)) := by fun_prop
    exact (this.tendsto 0).mono_left nhdsWithin_le_nhds

/-- Key limit lemma: a lower bound on the right difference quotients of the mgf at `0`
forces integrability of `X` and the same lower bound on its mean. -/
lemma key_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hint : ∀ ε ∈ Set.Ioc 0 δ, Integrable (fun ω => Real.exp (ε * X ω)) P)
    (c : ℝ) (r : ℝ → ℝ) (hr : Tendsto r (𝓝[>] 0) (𝓝 0))
    (hc : ∀ ε ∈ Set.Ioo 0 δ, c ≤ (∫ ω, Real.exp (ε * X ω) ∂P - 1) / ε + r ε) :
    Integrable X P ∧ c ≤ ∫ ω, X ω ∂P := by
  have hXm := aemeas_of_exp X hδ (hint δ ⟨hδ, le_rfl⟩)
  set F : Ω → ℝ := fun ω => (Real.exp (δ * X ω) - 1) / δ with hF
  have hfi : ∀ ε ∈ Set.Ioc 0 δ,
      Integrable (fun ω => (Real.exp (ε * X ω) - 1) / ε) P :=
    fun ε hε => ((hint ε hε).sub (integrable_const 1)).div_const ε
  have hfint : ∀ ε ∈ Set.Ioc 0 δ,
      ∫ ω, (Real.exp (ε * X ω) - 1) / ε ∂P = (∫ ω, Real.exp (ε * X ω) ∂P - 1) / ε := by
    intro ε hε
    rw [integral_div, integral_sub (hint ε hε) (integrable_const 1)]
    simp
  have hFi : Integrable F P := hfi δ ⟨hδ, le_rfl⟩
  have hFint := hfint δ ⟨hδ, le_rfl⟩
  -- c ≤ ∫ F
  have hcF : c ≤ ∫ ω, F ω ∂P := by
    have ht : Tendsto (fun ε => (∫ ω, F ω ∂P) + r ε) (𝓝[>] 0) (𝓝 ((∫ ω, F ω ∂P) + 0)) :=
      tendsto_const_nhds.add hr
    rw [add_zero] at ht
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    have hε' : ε ∈ Set.Ioc 0 δ := ⟨hε.1, hε.2.le⟩
    have := hc ε hε
    have hm : ∫ ω, (Real.exp (ε * X ω) - 1) / ε ∂P ≤ ∫ ω, F ω ∂P :=
      integral_mono (hfi ε hε') hFi (fun ω => exp_secant_mono ε δ (X ω) hε.1 hε.2.le)
    rw [hfint ε hε'] at hm
    linarith
  -- Fatou
  set g : ℝ → Ω → ENNReal := fun ε ω =>
    ENNReal.ofReal (F ω - (Real.exp (ε * X ω) - 1) / ε) with hg
  have hgm : ∀ ε, AEMeasurable (g ε) P := by
    intro ε
    have : AEMeasurable (fun ω => F ω - (Real.exp (ε * X ω) - 1) / ε) P := by
      simp only [hF]; fun_prop
    exact ENNReal.measurable_ofReal.comp_aemeasurable this
  have hfat := lintegral_liminf_le' (μ := P) (u := 𝓝[>] (0:ℝ)) hgm
  have hlim : ∀ ω, liminf (fun ε => g ε ω) (𝓝[>] 0) = ENNReal.ofReal (F ω - X ω) := by
    intro ω
    apply Tendsto.liminf_eq
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_const_nhds.sub (exp_secant_tendsto (X ω)))
  simp_rw [hlim] at hfat
  have hbound : liminf (fun ε => ∫⁻ ω, g ε ω ∂P) (𝓝[>] 0) ≤
      ENNReal.ofReal ((∫ ω, F ω ∂P) - c) := by
    have ht : Tendsto (fun ε => ENNReal.ofReal ((∫ ω, F ω ∂P) - c + r ε)) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal ((∫ ω, F ω ∂P) - c))) := by
      have := (ENNReal.continuous_ofReal.tendsto _).comp
        ((tendsto_const_nhds (x := (∫ ω, F ω ∂P) - c)).add hr)
      rw [add_zero] at this
      exact this
    rw [← ht.liminf_eq]
    refine liminf_le_liminf ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    have hε' : ε ∈ Set.Ioc 0 δ := ⟨hε.1, hε.2.le⟩
    have hnn : 0 ≤ᵐ[P] fun ω => F ω - (Real.exp (ε * X ω) - 1) / ε :=
      Eventually.of_forall (fun ω => sub_nonneg.2 (exp_secant_mono ε δ (X ω) hε.1 hε.2.le))
    simp only [hg]
    have hsi : Integrable (fun ω => F ω - (Real.exp (ε * X ω) - 1) / ε) P :=
      hFi.sub (hfi ε hε')
    rw [← ofReal_integral_eq_lintegral_ofReal hsi hnn,
      integral_sub hFi (hfi ε hε'), hfint ε hε']
    apply ENNReal.ofReal_le_ofReal
    have := hc ε hε
    linarith
  have hL := hfat.trans hbound
  have hnn : 0 ≤ᵐ[P] fun ω => F ω - X ω :=
    Eventually.of_forall (fun ω => sub_nonneg.2 (exp_secant_ge δ (X ω) hδ))
  have hFXi : Integrable (fun ω => F ω - X ω) P := by
    refine ⟨?_, (hasFiniteIntegral_iff_ofReal hnn).2 (lt_of_le_of_lt hL ENNReal.ofReal_lt_top)⟩
    exact (hFi.aestronglyMeasurable.aemeasurable.sub hXm).aestronglyMeasurable
  have hXi : Integrable X P := by
    have : X = fun ω => F ω - (F ω - X ω) := by funext ω; ring
    rw [this]; exact hFi.sub hFXi
  refine ⟨hXi, ?_⟩
  have h1 : ∫ ω, (F ω - X ω) ∂P ≤ (∫ ω, F ω ∂P) - c := by
    rw [integral_eq_lintegral_of_nonneg_ae hnn hFXi.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (sub_nonneg.2 hcF) hL
  rw [integral_sub hFi hXi] at h1
  linarith

lemma antitone_of_hasDeriv {K K' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt K (K' x) x) (hn : ∀ x ∈ Set.Ioo a b, K' x ≤ 0) :
    AntitoneOn K (Set.Ioo a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo a b)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioo]; exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    rw [(hd x hx).deriv]; exact hn x hx

lemma entropy_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (t : ℝ) :
    phiEntropy (fun ω => Real.exp (t * X ω)) P =
      t * (∫ ω, X ω * Real.exp (t * X ω) ∂P) - mgf X P t * Real.log (mgf X P t) := by
  unfold phiEntropy
  simp_rw [Real.log_exp]
  have : ∫ ω, Real.exp (t * X ω) * (t * X ω) ∂P = t * ∫ ω, X ω * Real.exp (t * X ω) ∂P := by
    rw [← integral_const_mul]; congr 1; funext ω; ring
  rw [this]; rfl

lemma log_centered {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℝ) (lam m : ℝ) (hi : Integrable (fun ω => Real.exp (lam * X ω)) P) :
    Real.log (∫ ω, Real.exp (lam * (X ω - m)) ∂P) = Real.log (mgf X P lam) - lam * m := by
  have : (fun ω => Real.exp (lam * (X ω - m))) =
      fun ω => Real.exp (lam * X ω) * Real.exp (-(lam * m)) := by
    funext ω; rw [← Real.exp_add]; ring_nf
  rw [this, integral_mul_const, Real.log_mul (integral_exp_pos hi).ne' (Real.exp_pos _).ne',
    Real.log_exp]
  rfl

lemma hasDerivAt_log_div {f : ℝ → ℝ} {f' t : ℝ} (hf : HasDerivAt f f' t) (hpos : 0 < f t)
    (ht : t ≠ 0) :
    HasDerivAt (fun s => Real.log (f s) / s) (((f' / f t) * t - Real.log (f t)) / t ^ 2) t := by
  have := (hf.log hpos.ne').div (hasDerivAt_id' t) ht
  exact this.congr_deriv (by ring)

theorem herbst_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℝ) (sigma : ℝ)
    (hInt : ∀ lam : ℝ, 0 ≤ lam → Integrable (fun ω => Real.exp (lam * X ω)) P)
    (hEnt : ∀ lam : ℝ, 0 ≤ lam → phiEntropy (fun ω => Real.exp (lam * X ω)) P ≤
        1 / 2 * sigma ^ 2 * lam ^ 2 * ∫ ω, Real.exp (lam * X ω) ∂P) :
    ∀ lam : ℝ, 0 ≤ lam →
      Real.log (∫ ω, Real.exp (lam * (X ω - ∫ ω', X ω' ∂P)) ∂P) ≤
        1 / 2 * lam ^ 2 * sigma ^ 2 := by
  intro lam hlam
  rcases hlam.eq_or_lt with h0 | hpos
  · subst h0; simp
  set φ := mgf X P with hφ
  have hφpos : ∀ t, 0 ≤ t → 0 < φ t := fun t ht => integral_exp_pos (hInt t ht)
  have hder : ∀ t, 0 < t → HasDerivAt φ (∫ ω, X ω * Real.exp (t * X ω) ∂P) t := by
    intro t ht
    apply hasDerivAt_mgf
    have hsub : Set.Ici (0:ℝ) ⊆ integrableExpSet X P := fun s hs => hInt s hs
    exact interior_mono hsub (by rw [interior_Ici]; exact ht)
  set K : ℝ → ℝ := fun t => Real.log (φ t) / t - sigma ^ 2 * t / 2 with hK
  have hanti : AntitoneOn K (Set.Ioo 0 (lam + 1)) := by
    refine antitone_of_hasDeriv (K' := fun t =>
      (((∫ ω, X ω * Real.exp (t * X ω) ∂P) / φ t) * t - Real.log (φ t)) / t ^ 2
        - sigma ^ 2 / 2) ?_ ?_
    · intro t ht
      have h1 := hasDerivAt_log_div (hder t ht.1) (hφpos t ht.1.le) ht.1.ne'
      have h2 : HasDerivAt (fun s : ℝ => sigma ^ 2 * s / 2) (sigma ^ 2 / 2) t := by
        simpa using ((hasDerivAt_id t).const_mul (sigma ^ 2)).div_const 2
      exact h1.sub h2
    · intro t ht
      have hE := hEnt t ht.1.le
      rw [entropy_eq] at hE
      have hp := hφpos t ht.1.le
      have ht0 := ht.1
      try dsimp only
      change _ ≤ 1 / 2 * sigma ^ 2 * t ^ 2 * φ t at hE
      set d := ∫ ω, X ω * Real.exp (t * X ω) ∂P
      set L := Real.log (φ t)
      rw [sub_nonpos, div_le_iff₀ (by positivity)]
      have : d / φ t * t - L = (t * d - φ t * L) / φ t := by
        field_simp
      rw [this, div_le_iff₀ hp]
      nlinarith
  set m := ∫ ω, X ω ∂P
  have hkey := key_limit (P := P) X hpos (fun ε hε => hInt ε hε.1.le) (K lam)
    (fun ε => -(sigma ^ 2 * ε / 2)) ?_ ?_
  · obtain ⟨_, hcm⟩ := hkey
    rw [log_centered X lam m (hInt lam hlam)]
    have hc : K lam * lam = Real.log (φ lam) - sigma ^ 2 * lam ^ 2 / 2 := by
      simp only [hK]; field_simp; try ring
    nlinarith [mul_le_mul_of_nonneg_right hcm hlam]
  · have : Continuous (fun ε : ℝ => -(sigma ^ 2 * ε / 2)) := by fun_prop
    have := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  · intro ε hε
    have h1 : K lam ≤ K ε := hanti ⟨hε.1, by linarith [hε.2]⟩ ⟨hpos, by linarith⟩ hε.2.le
    have h2 : Real.log (φ ε) / ε ≤ (φ ε - 1) / ε :=
      div_le_div_of_nonneg_right (Real.log_le_sub_one_of_pos (hφpos ε hε.1.le)) hε.1.le
    change K lam ≤ (φ ε - 1) / ε + -(sigma ^ 2 * ε / 2)
    have hKl : K lam = Real.log (φ lam) / lam - sigma ^ 2 * lam / 2 := rfl
    have hKe : K ε = Real.log (φ ε) / ε - sigma ^ 2 * ε / 2 := rfl
    linarith

theorem herbst_argument {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob] (X : Ω → ℝ) (sigma : ℝ) (I : Set ℝ)
    (hI : I = Set.Ici 0 ∨ I = Set.univ)
    (hInt : ∀ lam ∈ I, Integrable (fun ω => Real.exp (lam * X ω)) Prob ∧
      Integrable (fun ω => Real.exp (lam * X ω) * Real.log (Real.exp (lam * X ω))) Prob)
    (hEntropy : ∀ lam ∈ I,
      phiEntropy (fun ω => Real.exp (lam * X ω)) Prob ≤
        1 / 2 * sigma ^ 2 * lam ^ 2 * ∫ ω, Real.exp (lam * X ω) ∂Prob) :
    ∀ lam ∈ I,
      Real.log (∫ ω, Real.exp (lam * (X ω - ∫ ω', X ω' ∂Prob)) ∂Prob) ≤
        1 / 2 * lam ^ 2 * sigma ^ 2 := by
  rcases hI with rfl | rfl
  · intro lam hlam
    exact herbst_pos X sigma (fun l hl => (hInt l hl).1) (fun l hl => hEntropy l hl) lam hlam
  · intro lam _
    rcases le_or_gt 0 lam with hl | hl
    · exact herbst_pos X sigma (fun l _ => (hInt l trivial).1)
        (fun l _ => hEntropy l trivial) lam hl
    · have e1 : ∀ l : ℝ, (fun ω => Real.exp (l * -X ω)) = fun ω => Real.exp (-l * X ω) := by
        intro l; funext ω; ring_nf
      have h := herbst_pos (P := Prob) (fun ω => -X ω) sigma
        (fun l _ => by rw [e1]; exact (hInt (-l) trivial).1)
        (fun l _ => by
          rw [e1]
          have := hEntropy (-l) trivial
          rw [neg_sq] at this
          exact this) (-lam) (by linarith)
      have e2 : (fun ω => Real.exp (-lam * (-X ω - ∫ ω', -X ω' ∂Prob))) =
          fun ω => Real.exp (lam * (X ω - ∫ ω', X ω' ∂Prob)) := by
        funext ω; rw [integral_neg]; ring_nf
      rw [e2, neg_sq] at h
      exact h

theorem bernstein_entropy_bound {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob] (X : Ω → ℝ) (b sigma : ℝ) (hb : 0 < b) (hsigma : 0 < sigma)
    (hInt : ∀ lam : ℝ, 0 ≤ lam → lam < 1 / b →
      Integrable (fun ω => Real.exp (lam * X ω)) Prob ∧
      Integrable (fun ω => Real.exp (lam * X ω) * Real.log (Real.exp (lam * X ω))) Prob)
    (hEntropy : ∀ lam : ℝ, 0 ≤ lam → lam < 1 / b →
      phiEntropy (fun ω => Real.exp (lam * X ω)) Prob ≤
        lam ^ 2 * (b * deriv (fun l : ℝ => ∫ ω, Real.exp (l * X ω) ∂Prob) lam +
          (∫ ω, Real.exp (lam * X ω) ∂Prob) * (sigma ^ 2 - b * ∫ ω, X ω ∂Prob))) :
    ∀ lam : ℝ, 0 ≤ lam → lam < 1 / b →
      Real.log (∫ ω, Real.exp (lam * (X ω - ∫ ω', X ω' ∂Prob)) ∂Prob) ≤
        sigma ^ 2 * lam ^ 2 * (1 - b * lam)⁻¹ := by
  intro lam hlam hlb
  rcases hlam.eq_or_lt with h0 | hpos
  · subst h0; simp
  have hbl : b * lam < 1 := by rw [lt_div_iff₀ hb] at hlb; linarith
  set φ := mgf X Prob with hφ
  set m := ∫ ω, X ω ∂Prob with hm
  have hI : ∀ t, 0 ≤ t → t < 1 / b → Integrable (fun ω => Real.exp (t * X ω)) Prob :=
    fun t h1 h2 => (hInt t h1 h2).1
  have hφpos : ∀ t, 0 ≤ t → t < 1 / b → 0 < φ t :=
    fun t h1 h2 => integral_exp_pos (hI t h1 h2)
  have hder : ∀ t ∈ Set.Ioo 0 (1 / b),
      HasDerivAt φ (∫ ω, X ω * Real.exp (t * X ω) ∂Prob) t := by
    intro t ht
    apply hasDerivAt_mgf
    have hsub : Set.Ico (0:ℝ) (1 / b) ⊆ integrableExpSet X Prob :=
      fun s hs => hI s hs.1 hs.2
    exact interior_mono hsub (by rw [interior_Ico]; exact ht)
  set K : ℝ → ℝ := fun t => Real.log (φ t) / t - b * Real.log (φ t) - (sigma ^ 2 - b * m) * t
    with hK
  have hanti : AntitoneOn K (Set.Ioo 0 (1 / b)) := by
    refine antitone_of_hasDeriv (K' := fun t =>
      (((∫ ω, X ω * Real.exp (t * X ω) ∂Prob) / φ t) * t - Real.log (φ t)) / t ^ 2
        - b * ((∫ ω, X ω * Real.exp (t * X ω) ∂Prob) / φ t) - (sigma ^ 2 - b * m)) ?_ ?_
    · intro t ht
      have hp := hφpos t ht.1.le ht.2
      have h1 := hasDerivAt_log_div (hder t ht) hp ht.1.ne'
      have h2 := ((hder t ht).log hp.ne').const_mul b
      have h3 : HasDerivAt (fun s : ℝ => (sigma ^ 2 - b * m) * s) (sigma ^ 2 - b * m) t := by
        simpa using (hasDerivAt_id t).const_mul (sigma ^ 2 - b * m)
      exact (h1.sub h2).sub h3
    · intro t ht
      have hE := hEntropy t ht.1.le ht.2
      rw [entropy_eq] at hE
      have hfun : (fun l : ℝ => ∫ ω, Real.exp (l * X ω) ∂Prob) = φ := rfl
      rw [hfun, (hder t ht).deriv] at hE
      change _ ≤ t ^ 2 * (b * _ + φ t * (sigma ^ 2 - b * m)) at hE
      have hp := hφpos t ht.1.le ht.2
      have ht0 := ht.1
      try dsimp only
      set d := ∫ ω, X ω * Real.exp (t * X ω) ∂Prob
      set L := Real.log (φ t)
      have e1 : (d / φ t * t - L) / t ^ 2 = (t * d - φ t * L) / (t ^ 2 * φ t) := by
        field_simp
      have e2 : b * (d / φ t) + (sigma ^ 2 - b * m) =
          t ^ 2 * (b * d + φ t * (sigma ^ 2 - b * m)) / (t ^ 2 * φ t) := by
        field_simp
      have e3 : (t * d - φ t * L) / (t ^ 2 * φ t) ≤
          t ^ 2 * (b * d + φ t * (sigma ^ 2 - b * m)) / (t ^ 2 * φ t) :=
        div_le_div_of_nonneg_right hE (by positivity)
      rw [e1]
      linarith
  have hmgf := mgf_tendsto_one (P := Prob) X hpos (fun ε hε => hI ε hε.1.le (by linarith [hε.2]))
  have hkey := key_limit (P := Prob) X hpos (fun ε hε => hI ε hε.1.le (by linarith [hε.2]))
    (K lam) (fun ε => -b * Real.log (φ ε) - (sigma ^ 2 - b * m) * ε) ?_ ?_
  · obtain ⟨_, hcm⟩ := hkey
    rw [log_centered X lam m (hI lam hlam hlb)]
    have hc : K lam * lam = Real.log (φ lam) - b * lam * Real.log (φ lam)
        - (sigma ^ 2 - b * m) * lam ^ 2 := by
      simp only [hK]; field_simp; try ring
    have h1 := mul_le_mul_of_nonneg_right hcm hlam
    have hpos' : 0 < 1 - b * lam := by linarith
    rw [← div_eq_mul_inv, le_div_iff₀ hpos']
    nlinarith
  · have h1 : Tendsto (fun ε => Real.log (φ ε)) (𝓝[>] 0) (𝓝 0) := by
      have := hmgf.log one_ne_zero
      rw [Real.log_one] at this
      exact this
    have h2 : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have := (h1.const_mul (-b)).sub (h2.const_mul (sigma ^ 2 - b * m))
    simpa using this
  · intro ε hε
    have hε1 : ε < 1 / b := by linarith [hε.2]
    have h1 : K lam ≤ K ε := hanti ⟨hε.1, hε1⟩ ⟨hpos, hlb⟩ hε.2.le
    have h2 : Real.log (φ ε) / ε ≤ (φ ε - 1) / ε :=
      div_le_div_of_nonneg_right (Real.log_le_sub_one_of_pos (hφpos ε hε.1.le hε1)) hε.1.le
    change K lam ≤ (φ ε - 1) / ε + (-b * Real.log (φ ε) - (sigma ^ 2 - b * m) * ε)
    have hKe : K ε = Real.log (φ ε) / ε - b * Real.log (φ ε) - (sigma ^ 2 - b * m) * ε := rfl
    linarith

end HighDimStat.Concentration

open HighDimStat.Concentration

theorem solution {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob] (X : Ω → ℝ) (b sigma : ℝ) (hb : 0 < b) (hsigma : 0 < sigma)
    (hInt : ∀ lam : ℝ, 0 ≤ lam → lam < 1 / b →
      Integrable (fun ω => Real.exp (lam * X ω)) Prob ∧
      Integrable (fun ω => Real.exp (lam * X ω) * Real.log (Real.exp (lam * X ω))) Prob)
    (hEntropy : ∀ lam : ℝ, 0 ≤ lam → lam < 1 / b →
      phiEntropy (fun ω => Real.exp (lam * X ω)) Prob ≤
        lam ^ 2 * (b * deriv (fun l : ℝ => ∫ ω, Real.exp (l * X ω) ∂Prob) lam +
          (∫ ω, Real.exp (lam * X ω) ∂Prob) * (sigma ^ 2 - b * ∫ ω, X ω ∂Prob))) :
    ∀ lam : ℝ, 0 ≤ lam → lam < 1 / b →
      Real.log (∫ ω, Real.exp (lam * (X ω - ∫ ω', X ω' ∂Prob)) ∂Prob) ≤
        sigma ^ 2 * lam ^ 2 * (1 - b * lam)⁻¹ := by
  exact bernstein_entropy_bound X b sigma hb hsigma hInt hEntropy
