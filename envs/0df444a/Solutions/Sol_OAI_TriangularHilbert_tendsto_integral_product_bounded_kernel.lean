-- Prove2me | solution 1 for OAI.TriangularHilbert.tendsto_integral_product_bounded_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:57:25.962026+00:00
-- url     : https://prove2.me/submissions/f670c221-e31b-4e54-bde3-a8f993372b29

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/CubicProduct.lean:L49-L70
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.tendsto_integral_product_bounded_kernel. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert

-- ---- from OAI.Analysis.TriangularHilbert.CubicProduct ----
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma sq_le_cube_add_one {x : ℝ} (hx : 0 ≤ x) : x^2 ≤ x^3+1 := by
  by_cases h : x ≤ 1
  · have hs := pow_le_pow_left₀ hx h 2
    nlinarith [pow_nonneg hx 3]
  · have hm := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr (le_of_not_ge h))
    nlinarith

lemma mul_le_cube_add_cube_add_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x*y ≤ x^3+y^3+2 := by
  nlinarith [sq_nonneg (x-y),sq_le_cube_add_one hx,sq_le_cube_add_one hy,
    pow_nonneg hx 3,pow_nonneg hy 3]

lemma norm_product_kernel_le (f g : ℝ → ℂ) (K : ℝ → ℝ) {D E : ℝ → ℝ} {L : ℝ}
    (_hL : 0 ≤ L) {c : ℝ} (hf : ‖f c‖^3 ≤ D c) (hg : ‖g c‖^3 ≤ E c)
    (hk : |K c| ≤ L) : ‖f c*g c*(K c:ℂ)‖ ≤ (D c+E c+2)*L := by
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have hp := mul_le_cube_add_cube_add_two (norm_nonneg (f c)) (norm_nonneg (g c))
  have hD : 0 ≤ D c := (pow_nonneg (norm_nonneg _) 3).trans hf
  have hE : 0 ≤ E c := (pow_nonneg (norm_nonneg _) 3).trans hg
  exact mul_le_mul (by linarith : ‖f c‖*‖g c‖ ≤ D c+E c+2) hk (abs_nonneg _) (by positivity)

lemma tendsto_integral_product_bounded_kernel (f g : ℝ → ℂ) (F G : ℕ → ℝ → ℂ) (K : ℝ → ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) volume) (hG : ∀ n, AEStronglyMeasurable (G n) volume)
    (hK : Measurable K) {D E : ℝ → ℝ} (hD : Integrable D) (hE : Integrable E)
    (hbound : ∀ᵐ c : ℝ, ∀ n, ‖F n c‖^3 ≤ D c ∧ ‖G n c‖^3 ≤ E c)
    (ht : ∀ᵐ c : ℝ, Tendsto (fun n => F n c) atTop (𝓝 (f c)) ∧ Tendsto (fun n => G n c) atTop (𝓝 (g c)))
    {s : Set ℝ} (hs : MeasurableSet s) (hμ : volume s ≠ ⊤) {L : ℝ} (hL : 0 ≤ L)
    (hk : ∀ c, |K c| ≤ L) (hzero : ∀ c ∉ s, K c = 0) :
    Tendsto (fun n => ∫ c : ℝ, F n c*G n c*(K c:ℂ)) atTop
      (𝓝 (∫ c : ℝ, f c*g c*(K c:ℂ))) := by
  apply tendsto_integral_of_dominated_convergence (s.indicator (fun c => (D c+E c+2)*L))
  · intro n
    exact ((hF n).mul (hG n)).mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hK.aestronglyMeasurable)
  · exact IntegrableOn.integrable_indicator
      (((hD.integrableOn.add hE.integrableOn).add (integrableOn_const (C := (2:ℝ)) hμ)).mul_const L) hs
  · intro n
    filter_upwards [hbound] with c hc
    by_cases hc' : c ∈ s
    · rw [Set.indicator_of_mem hc']
      exact norm_product_kernel_le (F n) (G n) K hL (hc n).1 (hc n).2 (hk c)
    · simp only [hzero c hc',Complex.ofReal_zero,mul_zero,norm_zero,Set.indicator_of_notMem hc',le_refl]
  · filter_upwards [ht] with c hc
    exact (hc.1.mul hc.2).mul tendsto_const_nhds
end
end TriangularHilbert
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert
open MeasureTheory Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.TriangularHilbert.tendsto_integral_product_bounded_kernel := @_root_.OAI.TriangularHilbert.tendsto_integral_product_bounded_kernel
