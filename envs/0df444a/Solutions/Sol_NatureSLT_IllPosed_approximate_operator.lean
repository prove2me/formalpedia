-- Prove2me | solution 1 for NatureSLT.IllPosed.approximate_operator
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:49:53.199192+00:00
-- url     : https://prove2.me/submissions/acd42c35-b3b8-4f1e-b226-6955680c317d

import Mathlib
import Definitions.Def_NatureSLT_IllPosed_IsRegularizer
import Definitions.Def_NatureSLT_IllPosed_tikhonovFunctional
import Definitions.Def_NatureSLT_IllPosed_operatorDistance

open NatureSLT.IllPosed
open Filter Topology MeasureTheory
open scoped ENNReal

/-- Compactness: on a compact set, `A g` close to `A f` forces `g` close to `f`. -/
theorem g69f_compact_stab {E₁ E₂ : Type*} [MetricSpace E₁] [MetricSpace E₂]
    (A : E₁ → E₂) (hA : Continuous A) (hAinj : Function.Injective A) (K : Set E₁)
    (hK : IsCompact K) (f : E₁) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ g ∈ K, dist (A g) (A f) < δ → dist g f ≤ ε := by
  have hK' : IsCompact (K ∩ {g | ε ≤ dist g f}) :=
    hK.inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
  by_cases hne : (K ∩ {g | ε ≤ dist g f}).Nonempty
  · obtain ⟨g0, hg0, hmin⟩ := hK'.exists_isMinOn hne
      ((hA.dist continuous_const).continuousOn (s := K ∩ {g | ε ≤ dist g f}))
    have hpos : 0 < dist (A g0) (A f) := by
      apply dist_pos.mpr
      intro heq
      have := hAinj heq
      have h2 : ε ≤ dist g0 f := hg0.2
      rw [this, dist_self] at h2; linarith
    refine ⟨_, hpos, fun g hg hlt => ?_⟩
    by_contra hc
    push_neg at hc
    have := hmin ⟨hg, hc.le⟩
    simp only [Set.mem_setOf_eq] at this
    linarith
  · refine ⟨1, one_pos, fun g hg _ => ?_⟩
    by_contra hc
    push_neg at hc
    exact hne ⟨g, hg, hc.le⟩

theorem g69f_ineq (a b γ : ℝ) (X Y : ℝ≥0∞) (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ : 0 < γ) (hY : Y ≠ ⊤)
    (h : ENNReal.ofReal a + ENNReal.ofReal γ * X ≤ ENNReal.ofReal b + ENNReal.ofReal γ * Y) :
    X ≠ ⊤ ∧ a + γ * X.toReal ≤ b + γ * Y.toReal := by
  have hX : X ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by simp [hγ])] at h
    simp at h
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hY h
  refine ⟨hX, ?_⟩
  rw [← ENNReal.ofReal_toReal hX, ← ENNReal.ofReal_toReal hY,
    ← ENNReal.ofReal_mul hγ.le, ← ENNReal.ofReal_mul hγ.le,
    ← ENNReal.ofReal_add ha (by positivity),
    ← ENNReal.ofReal_add hb (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  exact h

theorem g69f_opdist {E₁ E₂ : Type*} [MetricSpace E₂] (B A : E₁ → E₂) (Ω : E₁ → ℝ≥0∞)
    (K : ℝ) (hK : 0 ≤ K) (h : operatorDistance B A Ω ≤ ENNReal.ofReal K) (g : E₁) (hg : Ω g ≠ ⊤) :
    dist (B g) (A g) ≤ K * Real.sqrt (Ω g).toReal := by
  have h1 : ENNReal.ofReal (dist (B g) (A g)) / Ω g ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal K :=
    le_trans (le_iSup₂_of_le (f := fun (g : E₁) (_ : Ω g ≠ ⊤) =>
      ENNReal.ofReal (dist (B g) (A g)) / Ω g ^ ((1 : ℝ) / 2)) g hg le_rfl) h
  have hpow : Ω g ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt (Ω g).toReal) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hg]
    rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num), Real.sqrt_eq_rpow]
  rw [hpow, ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_mul hK, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  exact h1

theorem solution {E₁ E₂ S : Type*}
    [MetricSpace E₁] [MeasurableSpace E₁] [BorelSpace E₁]
    [MetricSpace E₂] [MeasurableSpace E₂] [BorelSpace E₂]
    [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (A : E₁ → E₂) (hA : Continuous A) (hAinj : Function.Injective A)
    (Ω : E₁ → ℝ≥0∞) (hΩ : IsRegularizer Ω)
    (F : E₂) (f : E₁) (hf : A f = F) (hfΩ : Ω f ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε → ∀ C₁ C₂ : ℝ, 0 < C₁ → 0 < C₂ → ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      ∀ (F' : S → E₂) (A' : S → E₁ → E₂) (f' : S → E₁),
        Measurable F' → (∀ ω, Continuous (A' ω)) →
        Measurable (fun ω => operatorDistance (A' ω) A Ω) → Measurable f' →
        (∀ (ω : S) (g : E₁),
          tikhonovFunctional (A' ω) Ω γ (F' ω) (f' ω) ≤ tikhonovFunctional (A' ω) Ω γ (F' ω) g) →
        P {ω | ε < dist (f' ω) f} ≤
          P {ω | C₁ * Real.sqrt γ < dist (F' ω) F} +
            P {ω | ENNReal.ofReal (C₂ * Real.sqrt γ) < operatorDistance (A' ω) A Ω} := by
  intro ε hε C₁ C₂ hC₁ hC₂
  set y := (Ω f).toReal with hy
  have hy0 : 0 ≤ y := ENNReal.toReal_nonneg
  set c := (C₂ * Real.sqrt y + C₁) ^ 2 + y with hc
  have hcpos : 0 < c := by positivity
  obtain ⟨δ, hδ, hstab⟩ := g69f_compact_stab A hA hAinj {g | Ω g ≤ ENNReal.ofReal c}
    (hΩ.2 c hcpos) f ε hε
  set M := C₂ * Real.sqrt c + Real.sqrt c + C₁ with hM
  have hMpos : 0 < M := by positivity
  refine ⟨(δ / (2 * M)) ^ 2, by positivity, ?_⟩
  intro γ hγ hγ0 F' A' f' _ _ _ _ hmin
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hsγ : 0 ≤ Real.sqrt γ := Real.sqrt_nonneg _
  have hK : 0 ≤ C₂ * Real.sqrt γ := by positivity
  -- dist (A' f) F' bound
  have hAf : dist (A' ω f) (A f) ≤ C₂ * Real.sqrt γ * Real.sqrt y := g69f_opdist _ _ _ _ hK h2 f hfΩ
  have hd0 : dist (A' ω f) (F' ω) ≤ Real.sqrt γ * (C₂ * Real.sqrt y + C₁) := by
    have := dist_triangle (A' ω f) (A f) (F' ω)
    rw [hf] at hAf this
    rw [dist_comm F] at this
    nlinarith
  have hd0sq : dist (A' ω f) (F' ω) ^ 2 ≤ γ * (C₂ * Real.sqrt y + C₁) ^ 2 := by
    calc dist (A' ω f) (F' ω) ^ 2 ≤ (Real.sqrt γ * (C₂ * Real.sqrt y + C₁)) ^ 2 := by gcongr
      _ = γ * (C₂ * Real.sqrt y + C₁) ^ 2 := by rw [mul_pow, Real.sq_sqrt hγ.le]
  have hm := hmin ω f
  unfold tikhonovFunctional at hm
  obtain ⟨hfin, hineq⟩ := g69f_ineq _ _ γ _ _ (sq_nonneg _) (sq_nonneg _) hγ hfΩ hm
  have hx0 : 0 ≤ (Ω (f' ω)).toReal := ENNReal.toReal_nonneg
  have hΩc : (Ω (f' ω)).toReal ≤ c := by
    have := sq_nonneg (dist (A' ω (f' ω)) (F' ω))
    by_contra hcc; push_neg at hcc
    have : γ * c < γ * (Ω (f' ω)).toReal := mul_lt_mul_of_pos_left hcc hγ
    nlinarith
  have hK1 : Ω (f' ω) ≤ ENNReal.ofReal c := by
    rw [← ENNReal.ofReal_toReal hfin]; exact ENNReal.ofReal_le_ofReal hΩc
  have hd1sq : dist (A' ω (f' ω)) (F' ω) ^ 2 ≤ γ * c := by
    have hgx : 0 ≤ γ * (Ω (f' ω)).toReal := by positivity
    rw [← hy] at hineq
    rw [hc]; nlinarith
  have hd1 : dist (A' ω (f' ω)) (F' ω) ≤ Real.sqrt γ * Real.sqrt c := by
    rw [← Real.sqrt_mul hγ.le, ← Real.sqrt_sq dist_nonneg]; exact Real.sqrt_le_sqrt hd1sq
  have hd2 : dist (A' ω (f' ω)) (A (f' ω)) ≤ C₂ * Real.sqrt γ * Real.sqrt c := by
    have := g69f_opdist _ _ _ _ hK h2 (f' ω) hfin
    have hs : Real.sqrt (Ω (f' ω)).toReal ≤ Real.sqrt c := Real.sqrt_le_sqrt hΩc
    calc _ ≤ _ := this
      _ ≤ C₂ * Real.sqrt γ * Real.sqrt c := mul_le_mul_of_nonneg_left hs hK
  have hsγ0 : Real.sqrt γ ≤ δ / (2 * M) := by
    calc Real.sqrt γ ≤ Real.sqrt ((δ / (2 * M)) ^ 2) := Real.sqrt_le_sqrt hγ0
      _ = δ / (2 * M) := Real.sqrt_sq (by positivity)
  have hclose : dist (A (f' ω)) (A f) < δ := by
    rw [hf]
    have t1 := dist_triangle (A (f' ω)) (A' ω (f' ω)) F
    have t2 := dist_triangle (A' ω (f' ω)) (F' ω) F
    rw [dist_comm (A (f' ω)) (A' ω (f' ω))] at t1
    have hsum : dist (A (f' ω)) F ≤ Real.sqrt γ * M := by
      rw [hM]; nlinarith
    have : Real.sqrt γ * M ≤ δ / 2 := by
      calc Real.sqrt γ * M ≤ δ / (2 * M) * M := mul_le_mul_of_nonneg_right hsγ0 hMpos.le
        _ = δ / 2 := by field_simp
    linarith
  have := hstab (f' ω) hK1 hclose
  linarith
