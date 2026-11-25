-- Prove2me | solution 1 for GroundTheory.Automorphic.ArchWhittaker.tendsto_zero_of_moderate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:32.203482+00:00
-- url     : https://prove2.me/submissions/56f60939-c783-4406-b603-0719c3363824

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_WronskianEqZeroOfModerate
import Theorems.Thm_GroundTheory_Automorphic_ArchWhittaker_exp_growth_false
import Theorems.Thm_GroundTheory_Automorphic_ArchWhittaker_inner_mul_self
import Theorems.Thm_GroundTheory_Automorphic_ArchWhittaker_monotoneOn_Ici_of_hasDerivAt
import Theorems.Thm_GroundTheory_Automorphic_ArchWhittaker_antitoneOn_Ici_of_hasDerivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ArchWhittaker
open Filter Topology Set
namespace GroundTheory.Automorphic.ArchWhittaker
theorem _root_.solution {q f f' : ℝ → ℂ} {Y₀ c C : ℝ} {N : ℕ} (hc : 0 < c)
    (hq : ∀ y ≥ Y₀, c ^ 2 ≤ (q y).re)
    (hf : ∀ y ≥ Y₀, HasDerivAt f (f' y) y) (hf' : ∀ y ≥ Y₀, HasDerivAt f' (q y * f y) y)
    (hgr : ∀ y ≥ Y₀, ‖f y‖ ≤ C * y ^ N) : Tendsto f atTop (𝓝 0) := by
  set u : ℝ → ℝ := fun y => ‖f y‖ ^ 2 with hudef
  set u1 : ℝ → ℝ := fun y => 2 * inner ℝ (f y) (f' y) with hu1def
  set w : ℝ → ℝ := fun y => 2 * (inner ℝ (f y) (q y * f y) + inner ℝ (f' y) (f' y)) with hwdef
  have hu : ∀ y ≥ Y₀, HasDerivAt u (u1 y) y := fun y hy => (hf y hy).norm_sq
  have hu1 : ∀ y ≥ Y₀, HasDerivAt u1 (w y) y := fun y hy =>
    ((hf y hy).inner ℝ (hf' y hy)).const_mul 2
  have hw : ∀ y ≥ Y₀, 2 * c ^ 2 * u y ≤ w y := by
    intro y hy
    simp only [hwdef, hudef, inner_mul_self, real_inner_self_eq_norm_sq]
    have := hq y hy
    nlinarith [sq_nonneg ‖f y‖, sq_nonneg ‖f' y‖]
  have hu0 : ∀ y, 0 ≤ u y := fun y => sq_nonneg _
  have hwpos : ∀ y ≥ Y₀, 0 ≤ w y := fun y hy =>
    le_trans (mul_nonneg (by positivity) (hu0 y)) (hw y hy)

  have hug : ∀ y ≥ max Y₀ 0, u y ≤ C ^ 2 * y ^ (2 * N) := by
    intro y hy
    have h1 := hgr y (le_trans (le_max_left _ _) hy)
    have h0 : 0 ≤ ‖f y‖ := norm_nonneg _
    calc u y = ‖f y‖ ^ 2 := rfl
      _ ≤ (C * y ^ N) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = C ^ 2 * y ^ (2 * N) := by rw [mul_pow, ← pow_mul, mul_comm N 2]
  by_cases hpos : ∃ y₁ ≥ Y₀, 0 < u1 y₁
  · exfalso
    obtain ⟨y₁, hy₁, hpos₁⟩ := hpos
    have hmono1 : MonotoneOn u1 (Ici y₁) := monotoneOn_Ici_of_hasDerivAt
      (fun y hy => hu1 y (le_trans hy₁ hy)) (fun y hy => hwpos y (le_trans hy₁ hy))
    have hu1ge : ∀ y ≥ y₁, u1 y₁ ≤ u1 y := fun y hy => hmono1 (mem_Ici.2 le_rfl) hy hy

    have hlin : ∀ y ≥ y₁, u y₁ + u1 y₁ * (y - y₁) ≤ u y := by
      have hm : MonotoneOn (fun y => u y - u1 y₁ * y) (Ici y₁) := monotoneOn_Ici_of_hasDerivAt
        (fun y hy => ((hu y (le_trans hy₁ hy)).sub ((hasDerivAt_id y).const_mul (u1 y₁))))
        (fun y hy => by simpa using hu1ge y hy)
      intro y hy
      have := hm (mem_Ici.2 le_rfl) hy hy
      linarith

    have hQ : MonotoneOn (fun y => u1 y ^ 2 - 2 * c ^ 2 * u y ^ 2) (Ici y₁) := by
      refine monotoneOn_Ici_of_hasDerivAt
        (u' := fun y => 2 * u1 y * w y - 2 * c ^ 2 * (2 * u y * u1 y))
        (fun y hy => ?_) (fun y hy => ?_)
      · have h3 := ((hu1 y (le_trans hy₁ hy)).pow 2).sub
          (((hu y (le_trans hy₁ hy)).pow 2).const_mul (2 * c ^ 2))
        refine h3.congr_deriv ?_
        push_cast
        ring
      · have h1 : 0 ≤ u1 y := le_trans hpos₁.le (hu1ge y hy)
        have h2 := hw y (le_trans hy₁ hy)
        nlinarith [mul_nonneg h1 (sub_nonneg.2 h2)]
    set K₀ := u1 y₁ ^ 2 - 2 * c ^ 2 * u y₁ ^ 2 with hK₀
    have hQge : ∀ y ≥ y₁, K₀ ≤ u1 y ^ 2 - 2 * c ^ 2 * u y ^ 2 := fun y hy =>
      hQ (mem_Ici.2 le_rfl) hy hy
    set y₂ := y₁ + (|K₀| + 1) / (c * u1 y₁) with hy₂def
    have hy₂ : y₁ ≤ y₂ := by
      rw [hy₂def]; have : 0 ≤ (|K₀| + 1) / (c * u1 y₁) := by positivity
      linarith
    have hmonou : MonotoneOn u (Ici y₁) := monotoneOn_Ici_of_hasDerivAt
      (fun y hy => hu y (le_trans hy₁ hy)) (fun y hy => le_trans hpos₁.le (hu1ge y hy))
    have hcu₂ : |K₀| + 1 ≤ c * u y₂ := by
      have := hlin y₂ hy₂
      have e : u1 y₁ * (y₂ - y₁) = (|K₀| + 1) / c := by
        rw [hy₂def]; field_simp; ring
      have hu1 : 0 ≤ u y₁ := hu0 y₁
      rw [e] at this
      have : (|K₀| + 1) / c ≤ u y₂ := by linarith
      rwa [div_le_iff₀ hc, mul_comm] at this
    have hcu : ∀ y ≥ y₂, |K₀| + 1 ≤ c * u y := fun y hy =>
      le_trans hcu₂ (mul_le_mul_of_nonneg_left
        (hmonou (mem_Ici.2 hy₂) (mem_Ici.2 (le_trans hy₂ hy)) hy) hc.le)
    have hu1cu : ∀ y ≥ y₂, c * u y ≤ u1 y := by
      intro y hy
      have h1 := hQge y (le_trans hy₂ hy)
      have h2 := hcu y hy
      have h3 : 0 ≤ u1 y := le_trans hpos₁.le (hu1ge y (le_trans hy₂ hy))
      have h4 : 0 ≤ c * u y := le_trans (by positivity) h2
      have h5 : (c * u y) ^ 2 ≤ u1 y ^ 2 := by
        have : |K₀| ≤ (c * u y) ^ 2 := by nlinarith [abs_nonneg K₀]
        nlinarith [neg_abs_le K₀]
      exact (pow_le_pow_iff_left₀ h4 h3 (by norm_num : (2 : ℕ) ≠ 0)).1 h5

    have hE : MonotoneOn (fun y => u y * Real.exp (-(c * y))) (Ici y₂) := by
      refine monotoneOn_Ici_of_hasDerivAt
        (u' := fun y => u1 y * Real.exp (-(c * y)) + u y * (Real.exp (-(c * y)) * -(c * 1)))
        (fun y hy => ?_) (fun y hy => ?_)
      · exact (hu y (le_trans hy₁ (le_trans hy₂ hy))).mul
          (((hasDerivAt_id y).const_mul c).neg.exp)
      · have := hu1cu y hy
        have he := Real.exp_pos (-(c * y))
        nlinarith
    have hu₂pos : 0 < u y₂ := by
      have : 0 < c * u y₂ := lt_of_lt_of_le (by positivity) hcu₂
      exact pos_of_mul_pos_right this hc.le
    refine exp_growth_false (A := u y₂ * Real.exp (-(c * y₂))) (b := c) (K := C ^ 2)
      (M := 2 * N) (Y := max y₂ (max Y₀ 0)) (mul_pos hu₂pos (Real.exp_pos _)) hc fun y hy => ?_
    have hy2 : y₂ ≤ y := le_trans (le_max_left _ _) hy
    have h1 := hE (mem_Ici.2 le_rfl) (mem_Ici.2 hy2) hy2
    simp only at h1
    have h2 := hug y (le_trans (le_max_right _ _) hy)
    have e : u y * Real.exp (-(c * y)) * Real.exp (c * y) = u y := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    calc u y₂ * Real.exp (-(c * y₂)) * Real.exp (c * y)
        ≤ u y * Real.exp (-(c * y)) * Real.exp (c * y) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = u y := e
      _ ≤ C ^ 2 * y ^ (2 * N) := h2
  · push Not at hpos
    have hanti : AntitoneOn u (Ici Y₀) := antitoneOn_Ici_of_hasDerivAt hu hpos

    have hu_lim : Tendsto u atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      by_cases hex : ∃ y₀ ≥ Y₀, u y₀ < ε
      · obtain ⟨y₀, hy₀, hlt⟩ := hex
        refine ⟨y₀, fun y hy => ?_⟩
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (hu0 y)]
        exact lt_of_le_of_lt (hanti (mem_Ici.2 hy₀) (mem_Ici.2 (le_trans hy₀ hy)) hy) hlt
      · exfalso
        push Not at hex
        have hm : MonotoneOn (fun y => u1 y - 2 * c ^ 2 * ε * y) (Ici Y₀) :=
          monotoneOn_Ici_of_hasDerivAt (u' := fun y => w y - 2 * c ^ 2 * ε * 1)
            (fun y hy => (hu1 y hy).sub ((hasDerivAt_id y).const_mul _))
            (fun y hy => by
              have h1 := hw y hy
              have h2 := hex y hy
              have : 2 * c ^ 2 * ε ≤ 2 * c ^ 2 * u y :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
              linarith)
        set y₃ := Y₀ + (|u1 Y₀| + 1) / (2 * c ^ 2 * ε) with hy₃
        have hy₃ge : Y₀ ≤ y₃ := by
          rw [hy₃]; have : 0 ≤ (|u1 Y₀| + 1) / (2 * c ^ 2 * ε) := by positivity
          linarith
        have h1 := hm (mem_Ici.2 le_rfl) (mem_Ici.2 hy₃ge) hy₃ge
        simp only at h1
        have h2 := hpos y₃ hy₃ge
        have e : 2 * c ^ 2 * ε * (y₃ - Y₀) = |u1 Y₀| + 1 := by
          rw [hy₃]; field_simp; ring
        nlinarith [le_abs_self (u1 Y₀), neg_abs_le (u1 Y₀)]
    have : Tendsto (fun y => ‖f y‖) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hu_lim
      simp only [Function.comp_def, Real.sqrt_zero] at h
      refine h.congr fun y => ?_
      simp [hudef, Real.sqrt_sq (norm_nonneg _)]
    exact tendsto_zero_iff_norm_tendsto_zero.2 this
end GroundTheory.Automorphic.ArchWhittaker
