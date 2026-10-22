-- Prove2me | solution 1 for NatureSLT.Margin.optimal_hyperplane_max_margin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:12:52.417435+00:00
-- url     : https://prove2.me/submissions/831ec3ac-8150-4fe0-821b-dde4ec02c569

import Mathlib
import Definitions.Def_NatureSLT_Margin_optimalHyperplane
open scoped InnerProductSpace
open NatureSLT.Margin

theorem g69w_infDist_hyper {n : ℕ} (w p : EuclideanSpace ℝ (Fin n)) (b : ℝ) (hw : w ≠ 0) :
    Metric.infDist p {v | ⟪w, v⟫_ℝ - b = 0} = |⟪w, p⟫_ℝ - b| / ‖w‖ := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hn2 : ⟪w, w⟫_ℝ = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
  set v0 := p - ((⟪w, p⟫_ℝ - b) / ‖w‖ ^ 2) • w with hv0
  have hv0mem : v0 ∈ {v | ⟪w, v⟫_ℝ - b = 0} := by
    simp only [Set.mem_ofPred_eq, hv0, inner_sub_right, real_inner_smul_right, hn2]
    field_simp; ring
  apply le_antisymm
  · refine (Metric.infDist_le_dist_of_mem hv0mem).trans (le_of_eq ?_)
    rw [dist_eq_norm, hv0, sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0:ℝ) < ‖w‖ ^ 2)]
    field_simp
  · by_contra hlt
    push Not at hlt
    obtain ⟨v, hv, hd⟩ := (Metric.infDist_lt_iff ⟨v0, hv0mem⟩).mp hlt
    simp only [Set.mem_ofPred_eq] at hv
    have h1 : ⟪w, p⟫_ℝ - b = ⟪w, p - v⟫_ℝ := by rw [inner_sub_right]; linarith
    have h2 : |⟪w, p - v⟫_ℝ| ≤ ‖w‖ * ‖p - v‖ := abs_real_inner_le_norm w (p - v)
    rw [h1, lt_div_iff₀ hn, dist_eq_norm] at hd
    linarith

theorem g69w_ne_zero {n ℓ : ℕ} (x : Fin ℓ → EuclideanSpace ℝ (Fin n))
    (y : Fin ℓ → ℝ) (hboth : (∃ i, y i = 1) ∧ ∃ j, y j = -1)
    (w : EuclideanSpace ℝ (Fin n)) (b : ℝ) (hs : ∀ i, 0 < y i * (⟪w, x i⟫_ℝ - b)) : w ≠ 0 := by
  rintro rfl
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hboth
  have h1 := hs i
  have h2 := hs j
  simp [hi, hj] at h1 h2
  linarith

/-- the margin of a separating hyperplane -/
theorem g69w_margin {n ℓ : ℕ} (x : Fin ℓ → EuclideanSpace ℝ (Fin n))
    (y : Fin ℓ → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) (hne : Nonempty (Fin ℓ))
    (w : EuclideanSpace ℝ (Fin n)) (b : ℝ) (hw : w ≠ 0)
    (hs : ∀ i, 0 < y i * (⟪w, x i⟫_ℝ - b)) :
    0 < (⨅ i, y i * (⟪w, x i⟫_ℝ - b)) ∧
    (∀ i, (⨅ i, y i * (⟪w, x i⟫_ℝ - b)) ≤ y i * (⟪w, x i⟫_ℝ - b)) ∧
    (⨅ i, Metric.infDist (x i) {v | ⟪w, v⟫_ℝ - b = 0}) =
      (⨅ i, y i * (⟪w, x i⟫_ℝ - b)) / ‖w‖ := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hd : ∀ i, Metric.infDist (x i) {v | ⟪w, v⟫_ℝ - b = 0} = y i * (⟪w, x i⟫_ℝ - b) / ‖w‖ := by
    intro i
    rw [g69w_infDist_hyper _ _ _ hw]
    congr 1
    have := hs i
    rcases hy i with h | h <;> rw [h] at this ⊢
    · rw [one_mul, abs_of_pos (by linarith)]
    · rw [abs_of_neg (by linarith)]; ring
  obtain ⟨i0, hi0⟩ := exists_eq_ciInf_of_finite (f := fun i => y i * (⟪w, x i⟫_ℝ - b))
  have hle : ∀ i, (⨅ i, y i * (⟪w, x i⟫_ℝ - b)) ≤ y i * (⟪w, x i⟫_ℝ - b) :=
    fun i => ciInf_le (Finite.bddBelow_range _) i
  refine ⟨by rw [← hi0]; exact hs i0, hle, ?_⟩
  simp only [hd]
  apply le_antisymm
  · rw [← hi0]; exact ciInf_le (Finite.bddBelow_range _) i0
  · exact le_ciInf fun i => div_le_div_of_nonneg_right (hle i) hn.le

theorem solution {n ℓ : ℕ} (x : Fin ℓ → EuclideanSpace ℝ (Fin n))
    (y : Fin ℓ → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) (hboth : (∃ i, y i = 1) ∧ ∃ j, y j = -1) :
    (∀ (w₀ : EuclideanSpace ℝ (Fin n)) (b₀ : ℝ), IsOptimalHyperplane x y w₀ b₀ →
      w₀ ≠ 0 ∧ (∀ i, 0 < y i * (⟪w₀, x i⟫_ℝ - b₀)) ∧
      ∀ (w : EuclideanSpace ℝ (Fin n)) (b : ℝ), w ≠ 0 → (∀ i, 0 < y i * (⟪w, x i⟫_ℝ - b)) →
        (⨅ i, Metric.infDist (x i) {v | ⟪w, v⟫_ℝ - b = 0}) ≤
          ⨅ i, Metric.infDist (x i) {v | ⟪w₀, v⟫_ℝ - b₀ = 0}) ∧
    (∀ (w : EuclideanSpace ℝ (Fin n)) (b : ℝ), w ≠ 0 → (∀ i, 0 < y i * (⟪w, x i⟫_ℝ - b)) →
      (∀ (w' : EuclideanSpace ℝ (Fin n)) (b' : ℝ), w' ≠ 0 →
        (∀ i, 0 < y i * (⟪w', x i⟫_ℝ - b')) →
        (⨅ i, Metric.infDist (x i) {v | ⟪w', v⟫_ℝ - b' = 0}) ≤
          ⨅ i, Metric.infDist (x i) {v | ⟪w, v⟫_ℝ - b = 0}) →
      IsOptimalHyperplane x y ((⨅ i, y i * (⟪w, x i⟫_ℝ - b))⁻¹ • w)
        ((⨅ i, y i * (⟪w, x i⟫_ℝ - b))⁻¹ * b)) := by
  have hne : Nonempty (Fin ℓ) := ⟨hboth.1.choose⟩
  -- canonical => separating
  have hcs : ∀ w b, IsCanonicalSeparating x y w b → ∀ i, 0 < y i * (⟪w, x i⟫_ℝ - b) :=
    fun w b h i => lt_of_lt_of_le one_pos (h i)
  -- rescaling a separating hyperplane gives a canonical one
  have hresc : ∀ w b, w ≠ 0 → (∀ i, 0 < y i * (⟪w, x i⟫_ℝ - b)) →
      IsCanonicalSeparating x y ((⨅ i, y i * (⟪w, x i⟫_ℝ - b))⁻¹ • w)
        ((⨅ i, y i * (⟪w, x i⟫_ℝ - b))⁻¹ * b) := by
    intro w b hw hs i
    obtain ⟨hμ, hle, _⟩ := g69w_margin x y hy hne w b hw hs
    set μ := ⨅ i, y i * (⟪w, x i⟫_ℝ - b)
    rw [real_inner_smul_left, ← mul_sub, mul_left_comm, ← div_eq_inv_mul, le_div_iff₀ hμ, one_mul]
    exact hle i
  -- canonical => margin ≥ 1/‖w‖
  have hcan : ∀ w b, IsCanonicalSeparating x y w b →
      1 / ‖w‖ ≤ ⨅ i, Metric.infDist (x i) {v | ⟪w, v⟫_ℝ - b = 0} := by
    intro w b hc
    have hw := g69w_ne_zero x y hboth w b (hcs w b hc)
    obtain ⟨_, _, he⟩ := g69w_margin x y hy hne w b hw (hcs w b hc)
    rw [he]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    exact le_ciInf hc
  refine ⟨fun w₀ b₀ hopt => ?_, fun w b hw hs hmax => ?_⟩
  · have hw₀ := g69w_ne_zero x y hboth w₀ b₀ (hcs _ _ hopt.1)
    refine ⟨hw₀, hcs _ _ hopt.1, fun w b hw hs => ?_⟩
    obtain ⟨hμ, _, he⟩ := g69w_margin x y hy hne w b hw hs
    set μ := ⨅ i, y i * (⟪w, x i⟫_ℝ - b)
    have h1 := hopt.2 _ _ (hresc w b hw hs)
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hμ] at h1
    have hn0 : 0 < ‖w₀‖ := norm_pos_iff.mpr hw₀
    have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have h2 : ‖w₀‖ ≤ μ⁻¹ * ‖w‖ := by
      have := (pow_le_pow_iff_left₀ hn0.le (by positivity) (two_ne_zero)).mp h1
      exact this
    refine le_trans ?_ (hcan w₀ b₀ hopt.1)
    rw [he, div_le_div_iff₀ hn hn0, one_mul]
    rw [inv_mul_eq_div, le_div_iff₀ hμ] at h2
    linarith
  · obtain ⟨hμ, _, he⟩ := g69w_margin x y hy hne w b hw hs
    set μ := ⨅ i, y i * (⟪w, x i⟫_ℝ - b)
    refine ⟨hresc w b hw hs, fun w' b' hc' => ?_⟩
    have hw' := g69w_ne_zero x y hboth w' b' (hcs _ _ hc')
    have h1 := (hcan w' b' hc').trans (hmax w' b' hw' (hcs _ _ hc'))
    rw [he] at h1
    have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hn' : 0 < ‖w'‖ := norm_pos_iff.mpr hw'
    rw [div_le_div_iff₀ hn' hn, one_mul] at h1
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hμ]
    apply pow_le_pow_left₀ (by positivity)
    rw [inv_mul_eq_div, div_le_iff₀ hμ]
    linarith
