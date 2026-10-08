-- Prove2me | solution 1 for KingmanSubadditive.Continuous.gamma_limit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:36:56.728975+00:00
-- url     : https://prove2.me/submissions/d406e6a4-b196-4062-b836-7be7bab4234e

import Mathlib
import Definitions.Def_KingmanSubadditive_Continuous_Process



namespace KingmanSubadditive.Continuous

open MeasureTheory Filter Topology

variable {S : Type*} [MeasurableSpace S]

/-- a single admissible pair inside `I` is bounded by the oscillation over `I`. -/
lemma abs_le_osc_toReal
    (x : ℝ → ℝ → S → ℝ) (I : Set ℝ) (ω : S)
    (hfinite : oscillation x I ω < ⊤)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s < t) (hsI : s ∈ I) (htI : t ∈ I) :
    |x s t ω| ≤ (oscillation x I ω).toReal := by
  have h1 : ENNReal.ofReal (|x s t ω|) ≤ oscillation x I ω := by
    unfold oscillation
    exact le_iSup₂ (f := fun (p : TimePair) (_ : p.1.1 ∈ I ∧ p.1.2 ∈ I) =>
      ENNReal.ofReal (|x p.1.1 p.1.2 ω|)) (⟨(s, t), hs, hst⟩ : TimePair) ⟨hsI, htI⟩
  have h2 := ENNReal.toReal_mono hfinite.ne h1
  rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at h2

lemma measurable_procMap (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    Measurable (fun ω : S => fun p : TimePair => x (p.1.1 + τ) (p.1.2 + τ) ω) := by
  refine measurable_pi_iff.2 fun p => ?_
  exact hproc.1 _ _ (by linarith [p.2.1]) (by linarith [p.2.2])

lemma measurable_procMap0 (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x) :
    Measurable (fun ω : S => fun p : TimePair => x p.1.1 p.1.2 ω) := by
  refine measurable_pi_iff.2 fun p => ?_
  exact hproc.1 _ _ p.2.1 p.2.2

/-- law transfer for a single coordinate under a nonnegative time shift. -/
lemma shift_coord (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x)
    (s t τ : ℝ) (hs : 0 ≤ s) (hst : s < t) (hτ : 0 ≤ τ) :
    (Integrable (x (s + τ) (t + τ)) P ↔ Integrable (x s t) P) ∧
    ∫ ω, x (s + τ) (t + τ) ω ∂P = ∫ ω, x s t ω ∂P := by
  have hmap := hproc.2.2.1 τ hτ
  have hev : Measurable (fun f : TimePair → ℝ => f (⟨(s, t), hs, hst⟩ : TimePair)) :=
    measurable_pi_apply _
  have h1 := measurable_procMap P x hproc τ hτ
  have h0 := measurable_procMap0 P x hproc
  constructor
  · have A := integrable_map_measure (μ := P)
      (f := fun ω : S => fun p : TimePair => x (p.1.1 + τ) (p.1.2 + τ) ω)
      hev.aestronglyMeasurable h1.aemeasurable
    have B := integrable_map_measure (μ := P)
      (f := fun ω : S => fun p : TimePair => x p.1.1 p.1.2 ω)
      hev.aestronglyMeasurable h0.aemeasurable
    rw [hmap] at A
    exact A.symm.trans B
  · have A := integral_map (μ := P)
      (φ := fun ω : S => fun p : TimePair => x (p.1.1 + τ) (p.1.2 + τ) ω)
      h1.aemeasurable hev.aestronglyMeasurable
    have B := integral_map (μ := P)
      (φ := fun ω : S => fun p : TimePair => x p.1.1 p.1.2 ω)
      h0.aemeasurable hev.aestronglyMeasurable
    rw [hmap] at A
    exact A.symm.trans B

lemma integrable_shift (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 < t) :
    Integrable (x s (s + t)) P ∧ ∫ ω, x s (s + t) ω ∂P = mean P x t := by
  have h := shift_coord P x hproc 0 t s le_rfl ht hs
  rw [zero_add, add_comm t s] at h
  exact ⟨h.1.2 (hproc.2.2.2.1 t ht), h.2⟩

lemma mean_subadd (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    mean P x (s + t) ≤ mean P x s + mean P x t := by
  obtain ⟨hint, heq⟩ := integrable_shift P x hproc s t hs.le ht
  have hi1 := hproc.2.2.2.1 s hs
  have hi2 := hproc.2.2.2.1 (s + t) (by linarith)
  unfold mean at heq ⊢
  rw [← heq, ← integral_add hi1 hint]
  apply integral_mono hi2 (hi1.add hint)
  intro ω
  exact hproc.2.1 0 s (s + t) le_rfl hs (by linarith) ω

lemma mean_iter (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x)
    (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    ∀ k : ℕ, mean P x (k * s + r) ≤ k * mean P x s + mean P x r := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h : ((k + 1 : ℕ) : ℝ) * s + r = s + (k * s + r) := by push_cast; ring
    rw [h]
    have hpos : 0 < (k : ℝ) * s + r :=
      add_pos_of_nonneg_of_pos (mul_nonneg (Nat.cast_nonneg k) hs.le) hr
    calc mean P x (s + (k * s + r)) ≤ mean P x s + mean P x (k * s + r) :=
          mean_subadd P x hproc s _ hs hpos
      _ ≤ ((k + 1 : ℕ) : ℝ) * mean P x s + mean P x r := by push_cast; linarith

lemma mean_bdd_Ioc (P : Measure S) [IsProbabilityMeasure P] (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hosc : FiniteOscillation P x (Set.Icc a b)) :
    ∃ M : ℝ, ∀ r, a < r → r ≤ b → mean P x r ≤ M := by
  obtain ⟨hmeas, hfin⟩ := hosc
  have hintO : Integrable (fun ω => (oscillation x (Set.Icc a b) ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hmeas hfin.ne
  have hae : ∀ᵐ ω ∂P, oscillation x (Set.Icc a b) ω < ⊤ := ae_lt_top' hmeas hfin.ne
  have key : ∀ r, a < r → r ≤ b →
      (∀ᵐ ω ∂P, |x a r ω| ≤ (oscillation x (Set.Icc a b) ω).toReal) := by
    intro r har hrb
    filter_upwards [hae] with ω hω
    exact abs_le_osc_toReal x _ ω hω a r ha har ⟨le_rfl, hab.le⟩ ⟨har.le, hrb⟩
  rcases eq_or_lt_of_le ha with h0 | hpos
  · subst h0
    refine ⟨∫ ω, (oscillation x (Set.Icc 0 b) ω).toReal ∂P, fun r har hrb => ?_⟩
    unfold mean
    apply integral_mono_ae (hproc.2.2.2.1 r har) hintO
    filter_upwards [key r har hrb] with ω hω
    exact le_trans (le_abs_self _) hω
  · refine ⟨mean P x a + ∫ ω, (oscillation x (Set.Icc a b) ω).toReal ∂P,
      fun r har hrb => ?_⟩
    have hint_ar : Integrable (x a r) P := by
      refine Integrable.mono' hintO (hproc.1 a r ha har).aestronglyMeasurable ?_
      filter_upwards [key r har hrb] with ω hω
      simpa [Real.norm_eq_abs] using hω
    have hia := hproc.2.2.2.1 a hpos
    have h2 : ∫ ω, x a r ω ∂P ≤ ∫ ω, (oscillation x (Set.Icc a b) ω).toReal ∂P := by
      apply integral_mono_ae hint_ar hintO
      filter_upwards [key r har hrb] with ω hω
      exact le_trans (le_abs_self _) hω
    unfold mean
    calc ∫ ω, x 0 r ω ∂P ≤ ∫ ω, (x 0 a ω + x a r ω) ∂P :=
          integral_mono (hproc.2.2.2.1 r (by linarith)) (hia.add hint_ar)
            (fun ω => hproc.2.1 0 a r le_rfl hpos har ω)
      _ = ∫ ω, x 0 a ω ∂P + ∫ ω, x a r ω ∂P := integral_add hia hint_ar
      _ ≤ _ := by linarith

lemma mean_bdd_Ioc_gen (P : Measure S) [IsProbabilityMeasure P] (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hosc : FiniteOscillation P x (Set.Icc a b)) (L : ℝ) :
    ∃ M : ℝ, ∀ r, a < r → r ≤ a + L → mean P x r ≤ M := by
  obtain ⟨M₀, hM₀⟩ := mean_bdd_Ioc P x hproc a b ha hab hosc
  have hδpos : 0 < b - a := by linarith
  have hj : ∀ j : ℕ, ∀ r, a < r → r ≤ a + j * (b - a) →
      mean P x r ≤ M₀ + j * |mean P x (b - a)| := by
    intro j
    induction j with
    | zero =>
      intro r har hr
      simp at hr
      linarith
    | succ j ih =>
      intro r har hr
      push_cast at hr ⊢
      have habs := abs_nonneg (mean P x (b - a))
      by_cases hle : r ≤ a + j * (b - a)
      · have := ih r har hle
        linarith
      · push_neg at hle
        have hr' : a < r - j * (b - a) := by linarith
        have hr'b : r - j * (b - a) ≤ b := by linarith
        have h1 := mean_iter P x hproc (b - a) (r - j * (b - a)) hδpos (by linarith) j
        have h2 := hM₀ _ hr' hr'b
        have h3 : (j : ℝ) * (b - a) + (r - j * (b - a)) = r := by ring
        rw [h3] at h1
        have h4 : (j : ℝ) * mean P x (b - a) ≤ j * |mean P x (b - a)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg j)
        linarith
  obtain ⟨j, hjL⟩ := exists_nat_gt (L / (b - a))
  have hL : L < j * (b - a) := (div_lt_iff₀ hδpos).1 hjL
  exact ⟨M₀ + j * |mean P x (b - a)|, fun r har hr => hj j r har (by linarith)⟩

lemma mean_div_bdd (P : Measure S) (x : ℝ → ℝ → S → ℝ) (hproc : IsProcess P x) :
    BddBelow (Set.range (fun t : {t : ℝ // 0 < t} => mean P x t / (t : ℝ))) := by
  obtain ⟨A, hA⟩ := hproc.2.2.2.2
  refine ⟨-A, ?_⟩
  rintro _ ⟨t, rfl⟩
  have := hA t t.2
  show -A ≤ mean P x t / (t : ℝ)
  unfold mean
  rw [le_div_iff₀ t.2]
  exact this

theorem gamma_limit_core (P : Measure S) [IsProbabilityMeasure P]
    (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hosc : FiniteOscillation P x (Set.Icc a b)) :
    BddBelow (Set.range (fun t : {t : ℝ // 0 < t} => mean P x t / (t : ℝ))) ∧
      Tendsto (fun t : ℝ => mean P x t / t) atTop (𝓝 (gamma P x)) := by
  have hbdd := mean_div_bdd P x hproc
  refine ⟨hbdd, ?_⟩
  have hlow : ∀ t : ℝ, 0 < t → gamma P x ≤ mean P x t / t := fun t ht =>
    ciInf_le hbdd ⟨t, ht⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlt : ⨅ t : {t : ℝ // 0 < t}, mean P x t / (t : ℝ) < gamma P x + ε := by
    unfold gamma; linarith
  obtain ⟨⟨s, hs⟩, hsq⟩ := exists_lt_of_ciInf_lt hlt
  simp only at hsq
  set q := mean P x s / s with hq
  have hqs : mean P x s = q * s := (div_mul_cancel₀ _ hs.ne').symm
  obtain ⟨M, hM⟩ := mean_bdd_Ioc_gen P x hproc a b ha hab hosc (2 * s)
  set η := gamma P x + ε - q with hη
  have hηpos : 0 < η := by linarith
  have hηne : η ≠ 0 := hηpos.ne'
  set K := |q| * (a + 2 * s) + |M| with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨max (a + 2 * s + 1) (K / η + 1), fun t ht => ?_⟩
  have ht1 : a + 2 * s + 1 ≤ t := le_trans (le_max_left _ _) ht
  have ht2 : K / η + 1 ≤ t := le_trans (le_max_right _ _) ht
  have htpos : 0 < t := by linarith
  have htne : t ≠ 0 := htpos.ne'
  set k := ⌊(t - a - s) / s⌋₊ with hk
  have hnn : 0 ≤ (t - a - s) / s := by apply div_nonneg <;> linarith
  have hk1 : (k : ℝ) ≤ (t - a - s) / s := Nat.floor_le hnn
  have hk2 : (t - a - s) / s < k + 1 := Nat.lt_floor_add_one _
  have hks1 : (k : ℝ) * s ≤ t - a - s := by rwa [le_div_iff₀ hs] at hk1
  have hks2 : t - a - s < (k : ℝ) * s + s := by
    rw [div_lt_iff₀ hs] at hk2; linarith
  have hr1 : a < t - k * s := by linarith
  have hr2 : t - k * s ≤ a + 2 * s := by linarith
  have hgr := hM _ hr1 hr2
  have hiter := mean_iter P x hproc s (t - k * s) hs (by linarith) k
  have htr : (k : ℝ) * s + (t - k * s) = t := by ring
  rw [htr] at hiter
  have hqk : q * ((k : ℝ) * s) ≤ q * t + |q| * (a + 2 * s) := by
    have h2 : q * ((k : ℝ) * s - t) ≤ |q| * (a + 2 * s) := by
      calc q * ((k : ℝ) * s - t) ≤ |q * ((k : ℝ) * s - t)| := le_abs_self _
        _ = |q| * |(k : ℝ) * s - t| := abs_mul _ _
        _ ≤ |q| * (a + 2 * s) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg q)
            rw [abs_le]; constructor <;> linarith
    linarith
  have hgt : mean P x t ≤ q * t + K := by
    rw [hqs] at hiter
    have h3 : (k : ℝ) * (q * s) = q * ((k : ℝ) * s) := by ring
    rw [h3] at hiter
    have := le_abs_self M
    linarith
  have hupper : mean P x t / t ≤ q + K / t := by
    rw [div_le_iff₀ htpos]
    have h4 : (q + K / t) * t = q * t + K := by field_simp
    rw [h4]; exact hgt
  have hKt : K / t < η := by
    rw [div_lt_iff₀ htpos]
    have h5 : η * (K / η + 1) = K + η := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left ht2 hηpos.le]
  rw [Real.dist_eq, abs_lt]
  constructor
  · have := hlow t htpos; linarith
  · linarith

end KingmanSubadditive.Continuous

open KingmanSubadditive.Continuous
open MeasureTheory Filter Topology

theorem solution {S : Type*} [MeasurableSpace S]
    (P : Measure S) [IsProbabilityMeasure P]
    (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hosc : FiniteOscillation P x (Set.Icc a b)) :
    BddBelow (Set.range (fun t : {t : ℝ // 0 < t} => mean P x t / (t : ℝ))) ∧
      Tendsto (fun t : ℝ => mean P x t / t) atTop (𝓝 (gamma P x)) := by
  exact gamma_limit_core P x hproc a b ha hab hosc
