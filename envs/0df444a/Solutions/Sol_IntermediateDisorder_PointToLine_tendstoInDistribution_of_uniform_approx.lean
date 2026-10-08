-- Prove2me | solution 1 for IntermediateDisorder.PointToLine.tendstoInDistribution_of_uniform_approx
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T13:09:28.511785+00:00
-- url     : https://prove2.me/submissions/485e0779-0014-427b-a8c2-5ae55b74b1c7

import Mathlib

set_option autoImplicit false

namespace P022ed0de

open MeasureTheory ProbabilityTheory Filter Topology

lemma key {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (F : ℝ → ℝ) (M : ℝ)
    (hFb : ∀ x y, dist (F x) (F y) ≤ M) (L : NNReal) (hFl : LipschitzWith L F)
    (δ : ℝ) (hδ : 0 < δ) :
    |∫ ω, F ω ∂(μ.map Y) - ∫ ω, F ω ∂(μ.map X)|
      ≤ L * δ + M * μ.real {a | δ < |X a - Y a|} := by
  have hFc : Continuous F := hFl.continuous
  have hM : 0 ≤ M := by simpa using hFb 0 0
  have hS : NullMeasurableSet {a | δ < |X a - Y a|} μ :=
    nullMeasurableSet_lt (by fun_prop) (by fun_prop)
  have h_int_Y : Integrable (fun x ↦ F (Y x)) μ := by
    refine Integrable.of_bound (by fun_prop) (‖F 0‖ + M) (ae_of_all _ fun a ↦ ?_)
    specialize hFb (Y a) 0
    rw [← sub_le_iff_le_add']
    exact (abs_sub_abs_le_abs_sub (F (Y a)) (F 0)).trans hFb
  have h_int_X : Integrable (fun x ↦ F (X x)) μ := by
    refine Integrable.of_bound (by fun_prop) (‖F 0‖ + M) (ae_of_all _ fun a ↦ ?_)
    specialize hFb (X a) 0
    rw [← sub_le_iff_le_add']
    exact (abs_sub_abs_le_abs_sub (F (X a)) (F 0)).trans hFb
  have h_int_ind : Integrable (fun a ↦ (L : ℝ) * δ + M * {a | δ < |X a - Y a|}.indicator 1 a) μ :=
    (integrable_const _).add (((integrable_const (1 : ℝ)).indicator₀ hS).const_mul M)
  rw [integral_map hY (by fun_prop), integral_map hX (by fun_prop),
    ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
  calc ‖∫ a, F (Y a) - F (X a) ∂μ‖
      ≤ ∫ a, ‖F (Y a) - F (X a)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ a, ((L : ℝ) * δ + M * {a | δ < |X a - Y a|}.indicator 1 a) ∂μ := by
        refine integral_mono (h_int_Y.sub h_int_X).norm h_int_ind fun a ↦ ?_
        by_cases ha : δ < |X a - Y a|
        · have : {a | δ < |X a - Y a|}.indicator (1 : Ω → ℝ) a = 1 :=
            Set.indicator_of_mem (show a ∈ {a | δ < |X a - Y a|} from ha) _
          rw [this, mul_one, ← dist_eq_norm]
          have := hFb (Y a) (X a)
          have : 0 ≤ (L : ℝ) * δ := by positivity
          linarith
        · have : {a | δ < |X a - Y a|}.indicator (1 : Ω → ℝ) a = 0 :=
            Set.indicator_of_notMem (show a ∉ {a | δ < |X a - Y a|} from ha) _
          rw [this, mul_zero, add_zero, ← dist_eq_norm]
          refine (hFl.dist_le_mul _ _).trans ?_
          gcongr
          rw [Real.dist_eq, abs_sub_comm]
          exact not_lt.1 ha
    _ = L * δ + M * μ.real {a | δ < |X a - Y a|} := by
        have h2 : Integrable (fun a ↦ M * {a | δ < |X a - Y a|}.indicator (1 : Ω → ℝ) a) μ :=
          ((integrable_const (1 : ℝ)).indicator₀ hS).const_mul M
        rw [integral_add (integrable_const _) h2, integral_const_mul M, integral_indicator₀ hS]
        simp

lemma lip_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {X : ∀ i, Ω i → ℝ} {Z : Ω' → ℝ} (h : TendstoInDistribution X l Z μ μ')
    (F : ℝ → ℝ) (hb : ∃ C : ℝ, ∀ x y, dist (F x) (F y) ≤ C) (hl : ∃ L, LipschitzWith L F) :
    Tendsto (fun i ↦ ∫ ω, F ω ∂((μ i).map (X i))) l (𝓝 (∫ ω, F ω ∂(μ'.map Z))) := by
  have := (tendsto_iff_forall_lipschitz_integral_tendsto.1 h.tendsto) F hb hl
  simpa using this

set_option backward.isDefEq.respectTransparency.types false in
lemma of_lip {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {X : ∀ i, Ω i → ℝ} {Z : Ω' → ℝ} (hX : ∀ i, AEMeasurable (X i) (μ i))
    (hZ : AEMeasurable Z μ')
    (h : ∀ F : ℝ → ℝ, (∃ C : ℝ, ∀ x y, dist (F x) (F y) ≤ C) → (∃ L, LipschitzWith L F) →
      Tendsto (fun i ↦ ∫ ω, F ω ∂((μ i).map (X i))) l (𝓝 (∫ ω, F ω ∂(μ'.map Z)))) :
    TendstoInDistribution X l Z μ μ' := by
  refine ⟨hX, hZ, ?_⟩
  rwa [tendsto_iff_forall_lipschitz_integral_tendsto]

end P022ed0de

open MeasureTheory ProbabilityTheory Filter Topology in
theorem solution
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    {Ωk : ℕ → Type*} [∀ k, MeasurableSpace (Ωk k)] (Pk : ∀ k, Measure (Ωk k))
    [∀ k, IsProbabilityMeasure (Pk k)]
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Ykn : ℕ → ∀ n, Ω n → ℝ) (Yk : ∀ k, Ωk k → ℝ) (Yn : ∀ n, Ω n → ℝ) (Y : Ω' → ℝ)
    (hYn : ∀ n, AEMeasurable (Yn n) (P n))
    (h_row : ∀ k, TendstoInDistribution (Ykn k) atTop (Yk k) P (Pk k))
    (h_unif : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun k => ⨆ n, P n {a | ε < |Ykn k n a - Yn n a|}) atTop (𝓝 0))
    (h_col : TendstoInDistribution Yk atTop Y Pk P') :
    TendstoInDistribution Yn atTop Y P P' := by
  refine P022ed0de.of_lip hYn h_col.aemeasurable_limit ?_
  rintro F ⟨M, hb⟩ ⟨L, hl⟩
  rw [Metric.tendsto_nhds]
  intro η hη
  have hM : 0 ≤ M := by simpa using hb 0 0
  set δ : ℝ := η / (4 * ((L : ℝ) + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hLδ : (L : ℝ) * δ ≤ η / 4 := by
    have h1 : ((L : ℝ) + 1) * δ = η / 4 := by rw [hδdef]; field_simp
    have h2 : (L : ℝ) * δ ≤ ((L : ℝ) + 1) * δ := by nlinarith
    linarith
  set θ : ℝ := η / (4 * (M + 1)) with hθdef
  have hθ : 0 < θ := by positivity
  have hMθ : M * θ ≤ η / 4 := by
    have h1 : (M + 1) * θ = η / 4 := by rw [hθdef]; field_simp
    have h2 : M * θ ≤ (M + 1) * θ := by nlinarith
    linarith
  have hA := (h_unif δ hδ).eventually_lt_const (u := ENNReal.ofReal θ) (by simpa using hθ)
  have hB := Metric.tendsto_nhds.1 (P022ed0de.lip_tendsto h_col F ⟨M, hb⟩ ⟨L, hl⟩) (η / 4)
    (by positivity)
  obtain ⟨k, hk1, hk2⟩ := (hA.and hB).exists
  have hC := Metric.tendsto_nhds.1 (P022ed0de.lip_tendsto (h_row k) F ⟨M, hb⟩ ⟨L, hl⟩) (η / 4)
    (by positivity)
  filter_upwards [hC] with n hn
  have hK := P022ed0de.key (P n) (Ykn k n) (Yn n) ((h_row k).forall_aemeasurable n) (hYn n)
    F M hb L hl δ hδ
  have hS : (P n).real {a | δ < |Ykn k n a - Yn n a|} ≤ θ := by
    have : P n {a | δ < |Ykn k n a - Yn n a|} ≤ ENNReal.ofReal θ :=
      (le_iSup (fun n ↦ P n {a | δ < |Ykn k n a - Yn n a|}) n).trans hk1.le
    exact ENNReal.toReal_le_of_le_ofReal hθ.le this
  have hMS : M * (P n).real {a | δ < |Ykn k n a - Yn n a|} ≤ η / 4 :=
    (mul_le_mul_of_nonneg_left hS hM).trans hMθ
  rw [Real.dist_eq] at hn hk2 ⊢
  have tri := abs_sub_le (∫ ω, F ω ∂((P n).map (Yn n))) (∫ ω, F ω ∂((P n).map (Ykn k n)))
    (∫ ω, F ω ∂(P'.map Y))
  have tri2 := abs_sub_le (∫ ω, F ω ∂((P n).map (Ykn k n))) (∫ ω, F ω ∂((Pk k).map (Yk k)))
    (∫ ω, F ω ∂(P'.map Y))
  linarith
