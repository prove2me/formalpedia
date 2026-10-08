-- Prove2me | solution 1 for MathieuM23.lemma_3_2_hyperbolic_triangle
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T10:13:28.335383+00:00
-- url     : https://prove2.me/submissions/d3754649-aad4-4cb8-aded-84d62abf1ccf

import Definitions.Def_MathieuM23_HyperbolicDisk

open MathieuM23

namespace MathieuM23Sol

/-- Basic trigonometric data. -/
lemma trig_data (θ : ℝ) (h0 : 0 < θ) (h1 : θ < Real.pi / 4) :
    0 < Real.tan θ ∧ Real.tan θ < 1 ∧ 0 < Real.cos θ ∧
    Real.cos θ ^ 2 * (1 + Real.tan θ ^ 2) = 1 ∧
    Real.tan (Real.pi / 4 - θ) = (1 - Real.tan θ) / (1 + Real.tan θ) ∧
    Real.cos (2 * θ) = (1 - Real.tan θ ^ 2) / (1 + Real.tan θ ^ 2) := by
  have hpi := Real.pi_pos
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have ht : Real.tan θ = Real.sin θ / Real.cos θ := Real.tan_eq_sin_div_cos θ
  have hsc : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hlt : Real.sin θ < Real.cos θ := by
    have : Real.sin θ < Real.sin (Real.pi / 2 - θ) := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two <;> linarith
    rwa [Real.sin_pi_div_two_sub] at this
  refine ⟨?_, ?_, hc, ?_, ?_, ?_⟩
  · rw [ht]; positivity
  · rw [ht, div_lt_one hc]; exact hlt
  · rw [ht]; field_simp; linarith
  · rw [Real.tan_eq_sin_div_cos, Real.sin_sub, Real.cos_sub, Real.cos_pi_div_four,
      Real.sin_pi_div_four, ht]
    have h2 : Real.sqrt 2 / 2 ≠ 0 := by positivity
    have : Real.cos θ + Real.sin θ ≠ 0 := by positivity
    field_simp
  · rw [Real.cos_two_mul, ht]
    field_simp
    nlinarith [hsc]


lemma normA_sq (θ : ℝ) (h0 : 0 < θ) (h1 : θ < Real.pi / 4) :
    ‖vertexA θ‖ ^ 2 = (1 - Real.tan θ) / (1 + Real.tan θ) := by
  obtain ⟨ht0, ht1, -, -, htan, -⟩ := trig_data θ h0 h1
  have hp : 0 ≤ (1 - Real.tan θ) / (1 + Real.tan θ) := by
    apply div_nonneg <;> linarith
  have : ‖Complex.exp (-(θ : ℂ) * Complex.I)‖ = 1 := by
    have : -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [vertexA, norm_mul, this, one_mul, Complex.norm_real, Real.norm_eq_abs, htan,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hp]

lemma normC_sq (θ : ℝ) (h0 : 0 < θ) (h1 : θ < Real.pi / 4) :
    ‖vertexC θ‖ ^ 2 = (1 - Real.tan θ ^ 2) / (1 + Real.tan θ ^ 2) := by
  obtain ⟨ht0, ht1, -, -, -, hcos⟩ := trig_data θ h0 h1
  have hp : 0 ≤ (1 - Real.tan θ ^ 2) / (1 + Real.tan θ ^ 2) := by
    apply div_nonneg <;> nlinarith
  rw [vertexC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), 
    Real.sq_sqrt (by rw [hcos]; exact hp), hcos]

lemma normAC_sq (θ : ℝ) (h0 : 0 < θ) (h1 : θ < Real.pi / 4) :
    ‖vertexA θ - vertexC θ‖ ^ 2 =
      2 * Real.tan θ ^ 2 * (1 - Real.tan θ) / ((1 + Real.tan θ) * (1 + Real.tan θ ^ 2)) := by
  obtain ⟨ht0, ht1, hc, hck, htan, hcos⟩ := trig_data θ h0 h1
  set t := Real.tan θ with htdef
  have hS : Real.sin θ = t * Real.cos θ := by
    rw [htdef, Real.tan_eq_sin_div_cos]; field_simp
  have hs : 0 ≤ (1 - t) / (1 + t) := by apply div_nonneg <;> linarith
  have hu : 0 ≤ (1 - t ^ 2) / (1 + t ^ 2) := by apply div_nonneg <;> nlinarith
  set r := Real.sqrt (Real.tan (Real.pi / 4 - θ)) with hr
  set k := Real.sqrt (Real.cos (2 * θ)) with hk
  have hr2 : r ^ 2 = (1 - t) / (1 + t) := by rw [hr, Real.sq_sqrt (by rw [htan]; exact hs), htan]
  have hk2 : k ^ 2 = (1 - t ^ 2) / (1 + t ^ 2) := by
    rw [hk, Real.sq_sqrt (by rw [hcos]; exact hu), hcos]
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  -- r * k = (1 - t) * cos θ
  have hrk : r * k = (1 - t) * Real.cos θ := by
    have h1' : (r * k) ^ 2 = ((1 - t) * Real.cos θ) ^ 2 := by
      rw [mul_pow, hr2, hk2, mul_pow]
      have : Real.cos θ ^ 2 = 1 / (1 + t ^ 2) := by
        field_simp; linarith
      rw [this]; field_simp; ring
    have : 0 ≤ (1 - t) * Real.cos θ := mul_nonneg (by linarith) hc.le
    exact (sq_eq_sq₀ (mul_nonneg hr0 hk0) this).1 h1'
  have hnorm : ‖vertexA θ - vertexC θ‖ ^ 2 = r ^ 2 + k ^ 2 - 2 * (r * k) * Real.cos θ := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [vertexA, vertexC, Complex.exp_re, Complex.exp_im, hr, hk]
    linear_combination (Real.sqrt (Real.tan (Real.pi / 4 - θ))) ^ 2 * Real.sin_sq_add_cos_sq θ
  rw [hnorm, hrk, hr2, hk2]
  have : Real.cos θ ^ 2 = 1 / (1 + t ^ 2) := by
    field_simp; linarith
  have e : 2 * ((1 - t) * Real.cos θ) * Real.cos θ = 2 * (1 - t) * Real.cos θ ^ 2 := by ring
  rw [e, this]
  field_simp
  ring


lemma ch_symm (z w : ℂ) : diskCoshDist z w = diskCoshDist w z := by
  unfold diskCoshDist
  rw [norm_sub_rev z w, mul_comm (1 - ‖z‖ ^ 2)]

lemma ch_OA (θ : ℝ) (h0 : 0 < θ) (h1 : θ < Real.pi / 4) :
    diskCoshDist 0 (vertexA θ) = 1 / Real.tan θ := by
  obtain ⟨ht0, ht1, -⟩ := trig_data θ h0 h1
  have := normA_sq θ h0 h1
  unfold diskCoshDist
  rw [zero_sub, norm_neg, norm_zero, this]
  generalize Real.tan θ = t at *
  have h2 : (1 + t) ≠ 0 := by linarith
  have h3 : t ≠ 0 := ht0.ne'
  have h : 1 - (1 - t) / (1 + t) = 2 * t / (1 + t) := by field_simp; ring
  rw [h]
  field_simp
  ring

lemma ch_OC (θ : ℝ) (h0 : 0 < θ) (h1 : θ < Real.pi / 4) :
    diskCoshDist 0 (vertexC θ) = 1 / Real.tan θ ^ 2 := by
  obtain ⟨ht0, ht1, -⟩ := trig_data θ h0 h1
  have := normC_sq θ h0 h1
  unfold diskCoshDist
  rw [zero_sub, norm_neg, norm_zero, this]
  generalize Real.tan θ = t at *
  have h2 : (1 + t ^ 2) ≠ 0 := by positivity
  have h3 : t ≠ 0 := ht0.ne'
  have h : 1 - (1 - t ^ 2) / (1 + t ^ 2) = 2 * t ^ 2 / (1 + t ^ 2) := by field_simp; ring
  rw [h]
  field_simp
  ring

lemma ch_AC (θ : ℝ) (h0 : 0 < θ) (h1 : θ < Real.pi / 4) :
    diskCoshDist (vertexA θ) (vertexC θ) = 1 / Real.tan θ := by
  obtain ⟨ht0, ht1, -⟩ := trig_data θ h0 h1
  unfold diskCoshDist
  rw [normAC_sq θ h0 h1, normA_sq θ h0 h1, normC_sq θ h0 h1]
  generalize Real.tan θ = t at *
  have h2 : (1 + t ^ 2) ≠ 0 := by positivity
  have h3 : t ≠ 0 := ht0.ne'
  have h4 : (1 + t) ≠ 0 := by linarith
  have h : 1 - (1 - t) / (1 + t) = 2 * t / (1 + t) := by field_simp; ring
  have h' : 1 - (1 - t ^ 2) / (1 + t ^ 2) = 2 * t ^ 2 / (1 + t ^ 2) := by field_simp; ring
  rw [h, h']
  field_simp
  ring

lemma key_angle (θ : ℝ) (h0 : 0 < θ) (h1 : θ < Real.pi / 4) :
    (1 / Real.tan θ * (1 / Real.tan θ ^ 2) - 1 / Real.tan θ) /
      (Real.sqrt ((1 / Real.tan θ) ^ 2 - 1) * Real.sqrt ((1 / Real.tan θ ^ 2) ^ 2 - 1)) =
    Real.cos θ := by
  obtain ⟨ht0, ht1, hc, hck, -⟩ := trig_data θ h0 h1
  set t := Real.tan θ
  set co := Real.cos θ
  have hq : 0 < 1 - t ^ 2 := by nlinarith
  have hD : Real.sqrt ((1 / t) ^ 2 - 1) * Real.sqrt ((1 / t ^ 2) ^ 2 - 1) =
      (1 - t ^ 2) / (t ^ 3 * co) := by
    have hnn : 0 ≤ (1 - t ^ 2) / (t ^ 3 * co) := by positivity
    rw [← Real.sqrt_mul (by
      have : (1 / t) ^ 2 - 1 = (1 - t ^ 2) / t ^ 2 := by field_simp
      rw [this]; positivity)]
    rw [← Real.sqrt_sq hnn]
    congr 1
    have : co ^ 2 = 1 / (1 + t ^ 2) := by field_simp; linarith
    have e : ((1 - t ^ 2) / (t ^ 3 * co)) ^ 2 = (1 - t ^ 2) ^ 2 / (t ^ 6 * co ^ 2) := by
      field_simp
    rw [e, this]
    field_simp
    ring
  rw [hD]
  field_simp

end MathieuM23Sol

open MathieuM23Sol in
theorem solution (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < Real.pi / 4) :
    ‖vertexA θ‖ < 1 ∧ ‖vertexB‖ < 1 ∧ ‖vertexC θ‖ < 1 ∧
      vertexA θ ≠ vertexB ∧ vertexB ≠ vertexC θ ∧ vertexA θ ≠ vertexC θ ∧
      diskAngle (vertexA θ) vertexB (vertexC θ) = Real.pi / 2 ∧
      diskAngle vertexB (vertexA θ) (vertexC θ) = θ ∧
      diskAngle (vertexC θ) (vertexA θ) vertexB = θ := by
  obtain ⟨ht0, ht1, hc, hck, -⟩ := trig_data θ hθ₀ hθ₁
  have hA := normA_sq θ hθ₀ hθ₁
  have hC := normC_sq θ hθ₀ hθ₁
  have hAC := normAC_sq θ hθ₀ hθ₁
  have hOA := ch_OA θ hθ₀ hθ₁
  have hOC := ch_OC θ hθ₀ hθ₁
  have hAC' := ch_AC θ hθ₀ hθ₁
  have hkey := key_angle θ hθ₀ hθ₁
  have hB : vertexB = 0 := rfl
  have hAs : ‖vertexA θ‖ ^ 2 < 1 ^ 2 := by
    rw [hA, one_pow, div_lt_one (by linarith)]; linarith
  have hCs : ‖vertexC θ‖ ^ 2 < 1 ^ 2 := by
    rw [hC, one_pow, div_lt_one (by positivity)]; nlinarith
  have hApos : 0 < ‖vertexA θ‖ ^ 2 := by
    rw [hA]; apply div_pos <;> linarith
  have hCpos : 0 < ‖vertexC θ‖ ^ 2 := by
    rw [hC]; apply div_pos <;> nlinarith
  have hACpos : 0 < ‖vertexA θ - vertexC θ‖ ^ 2 := by
    rw [hAC]; have : 0 < 1 + Real.tan θ := by linarith
    apply div_pos
    · have : 0 < 1 - Real.tan θ := by linarith
      positivity
    · positivity
  refine ⟨lt_of_pow_lt_pow_left₀ 2 zero_le_one hAs, by simp [hB], 
    lt_of_pow_lt_pow_left₀ 2 zero_le_one hCs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; rw [hB] at h; rw [h] at hApos; simp at hApos
  · intro h; rw [hB] at h; rw [← h] at hCpos; simp at hCpos
  · intro h; rw [h] at hACpos; simp at hACpos
  · unfold diskAngle
    rw [hB, ch_symm (vertexA θ) 0, hOA, hOC, hAC']
    have : 1 / Real.tan θ * (1 / Real.tan θ) - 1 / Real.tan θ ^ 2 = 0 := by
      field_simp; ring
    rw [this, zero_div, Real.arccos_zero]
  · unfold diskAngle
    rw [hB, hOA, hOC, hAC', hkey, Real.arccos_cos hθ₀.le (by linarith [Real.pi_pos])]
  · unfold diskAngle
    rw [hB, ch_symm (vertexC θ) (vertexA θ), ch_symm (vertexC θ) 0, ch_symm (vertexA θ) 0,
      hOA, hOC, hAC', hkey, Real.arccos_cos hθ₀.le (by linarith [Real.pi_pos])]
