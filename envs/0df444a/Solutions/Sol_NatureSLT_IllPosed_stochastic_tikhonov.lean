-- Prove2me | solution 1 for NatureSLT.IllPosed.stochastic_tikhonov
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:41:28.970465+00:00
-- url     : https://prove2.me/submissions/eb3cba46-b3d9-414e-92db-4d70f47a62e7

import Mathlib
import Definitions.Def_NatureSLT_IllPosed_IsRegularizer
import Definitions.Def_NatureSLT_IllPosed_tikhonovFunctional

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

/-- The deterministic estimate behind (7.21). -/
theorem g69f_det {E₁ E₂ : Type*} [MetricSpace E₂] (A : E₁ → E₂) (Ω : E₁ → ℝ≥0∞)
    (F G : E₂) (f g : E₁) (hf : A f = F) (hfΩ : Ω f ≠ ⊤) (γ μ : ℝ) (hγ : 0 < γ)
    (hmin : tikhonovFunctional A Ω γ G g ≤ tikhonovFunctional A Ω γ G f)
    (hG : dist G F ≤ Real.sqrt (γ * μ)) (hμ : 0 < μ) :
    Ω g ≤ ENNReal.ofReal (μ + (Ω f).toReal) ∧
      dist (A g) G ^ 2 ≤ γ * (μ + (Ω f).toReal) := by
  unfold tikhonovFunctional at hmin
  rw [hf] at hmin
  have hb : dist F G ^ 2 ≤ γ * μ := by
    rw [dist_comm]
    calc dist G F ^ 2 ≤ Real.sqrt (γ * μ) ^ 2 := by gcongr
      _ = γ * μ := Real.sq_sqrt (by positivity)
  have hgfin : Ω g ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by simp [hγ])] at hmin
    simp at hmin
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfΩ hmin
  rw [← ENNReal.ofReal_toReal hgfin, ← ENNReal.ofReal_toReal hfΩ,
    ← ENNReal.ofReal_mul hγ.le, ← ENNReal.ofReal_mul hγ.le,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hmin
  have hx := ENNReal.toReal_nonneg (a := Ω g)
  have ha := sq_nonneg (dist (A g) G)
  constructor
  · rw [← ENNReal.ofReal_toReal hgfin]
    apply ENNReal.ofReal_le_ofReal
    by_contra hc; push_neg at hc
    nlinarith
  · nlinarith

theorem solution {E₁ E₂ S : Type*}
    [MetricSpace E₁] [MeasurableSpace E₁] [BorelSpace E₁]
    [MetricSpace E₂] [MeasurableSpace E₂] [BorelSpace E₂]
    [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (A : E₁ → E₂) (hA : Continuous A) (hAinj : Function.Injective A)
    (Ω : E₁ → ℝ≥0∞) (hΩ : IsRegularizer Ω)
    (F : E₂) (f : E₁) (hf : A f = F) (hfΩ : Ω f ≠ ⊤)
    (Fl : ℕ → S → E₂) (hFl_meas : ∀ ℓ, Measurable (Fl ℓ))
    (hFl : ∀ ε : ℝ, 0 < ε → Tendsto (fun ℓ => P {ω | ε < dist (Fl ℓ ω) F}) atTop (𝓝 0))
    (γ : ℕ → ℝ) (hγpos : ∀ ℓ, 0 < γ ℓ) (hγ : Tendsto γ atTop (𝓝 0))
    (fl : ℕ → S → E₁) (hfl_meas : ∀ ℓ, Measurable (fl ℓ))
    (hmin : ∀ ℓ (ω : S) (g : E₁),
      tikhonovFunctional A Ω (γ ℓ) (Fl ℓ ω) (fl ℓ ω) ≤ tikhonovFunctional A Ω (γ ℓ) (Fl ℓ ω) g) :
    ∀ ε : ℝ, 0 < ε → ∀ μ : ℝ, 0 < μ → ∃ n : ℕ, 0 < n ∧ ∀ ℓ : ℕ, n < ℓ →
      P {ω | ε < dist (fl ℓ ω) f} ≤ P {ω | Real.sqrt (γ ℓ * μ) < dist (Fl ℓ ω) F} := by
  intro ε hε μ hμ
  set c := μ + (Ω f).toReal with hc
  have hcpos : 0 < c := by have := ENNReal.toReal_nonneg (a := Ω f); linarith
  have hμc : μ ≤ c := by have := ENNReal.toReal_nonneg (a := Ω f); linarith
  obtain ⟨δ, hδ, hstab⟩ := g69f_compact_stab A hA hAinj {g | Ω g ≤ ENNReal.ofReal c}
    (hΩ.2 c hcpos) f ε hε
  -- eventually 2 √(γ c) < δ
  have hev : ∀ᶠ ℓ in atTop, 2 * Real.sqrt (γ ℓ * c) < δ := by
    have ht : Tendsto (fun ℓ => 2 * Real.sqrt (γ ℓ * c)) atTop (𝓝 (2 * Real.sqrt (0 * c))) :=
      ((hγ.mul_const c).sqrt).const_mul 2
    simp only [zero_mul, Real.sqrt_zero, mul_zero] at ht
    exact ht.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N + 1, Nat.succ_pos _, fun ℓ hℓ => measure_mono ?_⟩
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := g69f_det A Ω F (Fl ℓ ω) f (fl ℓ ω) hf hfΩ (γ ℓ) μ (hγpos ℓ)
    (hmin ℓ ω f) hcon hμ
  have hγc : 0 ≤ γ ℓ * c := by have := hγpos ℓ; positivity
  have hd1 : dist (A (fl ℓ ω)) (Fl ℓ ω) ≤ Real.sqrt (γ ℓ * c) := by
    rw [← Real.sqrt_sq dist_nonneg]; exact Real.sqrt_le_sqrt h2
  have hd2 : Real.sqrt (γ ℓ * μ) ≤ Real.sqrt (γ ℓ * c) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hμc (hγpos ℓ).le)
  have hlt := hN ℓ (by omega)
  have hclose : dist (A (fl ℓ ω)) (A f) < δ := by
    rw [hf]
    calc dist (A (fl ℓ ω)) F ≤ dist (A (fl ℓ ω)) (Fl ℓ ω) + dist (Fl ℓ ω) F := dist_triangle _ _ _
      _ ≤ Real.sqrt (γ ℓ * c) + Real.sqrt (γ ℓ * c) := by linarith
      _ < δ := by linarith
  have := hstab (fl ℓ ω) h1 hclose
  linarith
