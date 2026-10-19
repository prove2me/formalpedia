-- Prove2me | solution 1 for OAI.EntropyRateDimension.ErgodicAux.ae_tendsto_triangle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T18:33:22.749075+00:00
-- url     : https://prove2.me/submissions/25db259b-44ba-41ac-a51b-93f2e626e83f

import Mathlib
import Definitions.Def_OAIQWERD000
import Theorems.Thm_OAI_EntropyRateDimension_ErgodicAux_ae_tendsto_average

section
-- module Solutions.OAIQW_EntropyRateDimension.TriangularAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace EntropyRateDimension.ErgodicAux

variable {α : Type uα}

theorem error_bound {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x) (n : ℕ) (x : α) :
    |f n x - g x| ≤ 2 * F x := by
  exact (abs_sub _ _).trans (by linarith [hf n x,hg x])

theorem tailError_bound {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x) (N : ℕ) (x : α) :
    tailError f g N x ≤ 2*F x :=
  ciSup_le fun k => error_bound hf hg (N+k) x

theorem error_le_tailError {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x) {N k : ℕ}
    (hk : N ≤ k) (x : α) : |f k x - g x| ≤ tailError f g N x := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
  exact le_ciSup (f := fun k : ℕ => |f (N+k) x - g x|)
    ⟨2*F x,fun _ ⟨k,hk⟩ => hk ▸ error_bound hf hg (N+k) x⟩ j

theorem tailError_nonneg {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x) (N : ℕ) (x : α) :
    0 ≤ tailError f g N x :=
  (abs_nonneg _).trans (error_le_tailError hf hg le_rfl x)

theorem tailError_tendsto {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x) {x : α}
    (hx : Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => tailError f g n x) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (tailError_nonneg hf hg n x)
  · intro b hb
    obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hx (b/2) (by linarith)
    filter_upwards [eventually_ge_atTop N] with n hn
    apply lt_of_le_of_lt (ciSup_le fun k => (hN (n+k) (by omega)).le) (by linarith)

variable [MeasurableSpace α] {μ : Measure α}

theorem tailError_measurable {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g) (N : ℕ) :
    Measurable (tailError f g N) :=
  Measurable.iSup fun k => ((hf (N+k)).sub hg).abs

theorem tailError_integrable {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x)
    (hF : Integrable F μ) (N : ℕ) : Integrable (tailError f g N) μ := by
  apply (hF.const_mul 2).mono' (tailError_measurable hfm hgm N).aestronglyMeasurable
  exact ae_of_all μ fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (tailError_nonneg hf hg N x)]
    exact tailError_bound hf hg N x

theorem tailError_integral_tendsto {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x)
    (hF : Integrable F μ) (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ x, tailError f g n x ∂μ) atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence (fun x => 2*F x)
    (fun n => (tailError_measurable hfm hgm n).aestronglyMeasurable) (hF.const_mul 2)
    (fun n => ae_of_all μ fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (tailError_nonneg hf hg n x)]
      exact tailError_bound hf hg n x)
    (hlim.mono fun x hx => tailError_tendsto hf hg hx)
  simpa using ht

omit [MeasurableSpace α] in
 theorem triangle_error_bound {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x)
    (T : α → α) (n N : ℕ) (x : α) :
    |(∑ j ∈ Finset.range (n+N), f (n+N-j) (T^[j] x)) - birkhoffSum T g (n+N) x| ≤
      birkhoffSum T (tailError f g N) (n+N) x +
        2 * (birkhoffSum T F (n+N) x - birkhoffSum T F n x) := by
  rw [birkhoffSum,← Finset.sum_sub_distrib]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  have hfirst : (∑ j ∈ Finset.range n, |f (n+N-j) (T^[j] x) - g (T^[j] x)|) ≤
      ∑ j ∈ Finset.range n, tailError f g N (T^[j] x) := by
    apply Finset.sum_le_sum
    intro j hj
    exact error_le_tailError hf hg (by have := Finset.mem_range.mp hj; omega) _
  have hlast : (∑ j ∈ Finset.range N, |f (n+N-(n+j)) (T^[n+j] x) - g (T^[n+j] x)|) ≤
      2 * ∑ j ∈ Finset.range N, F (T^[n+j] x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => error_bound hf hg _ _
  have hn : 0 ≤ ∑ j ∈ Finset.range N, tailError f g N (T^[n+j] x) :=
    Finset.sum_nonneg fun _ _ => tailError_nonneg hf hg _ _
  simp only [birkhoffSum,Finset.sum_range_add]
  linarith

 theorem tendsto_shift_denominator {a : ℕ → ℝ} {L : ℝ}
    (ha : Tendsto (fun n => a n / (n : ℝ)) atTop (𝓝 L)) (N : ℕ) :
    Tendsto (fun n => a n / (n+N : ℕ)) atTop (𝓝 L) := by
  have hh := ha.mul (tendsto_natCast_div_add_atTop (N : ℝ))
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

 theorem ae_tendsto_triangle_oai [IsProbabilityMeasure μ] {T : α → α}
    (hT : Ergodic T μ) {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g) (hFm : Measurable F)
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x) (hF : Integrable F μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ∀ᵐ x ∂μ, Tendsto (fun n => (∑ j ∈ Finset.range n, f (n-j) (T^[j] x)) / (n : ℝ))
      atTop (𝓝 (∫ x, g x ∂μ)) := by
  have hgi : Integrable g μ := hF.mono' hgm.aestronglyMeasurable
    (ae_of_all μ fun x => by simpa only [Real.norm_eq_abs] using hg x)
  have hb := tailError_integral_tendsto hfm hgm hf hg hF hlim
  filter_upwards [ae_tendsto_average hT hgm hgi,ae_tendsto_average hT hFm hF,
    ae_all_iff.mpr (fun N => ae_tendsto_average hT (tailError_measurable hfm hgm N)
      (tailError_integrable hfm hgm hf hg hF N))] with x hx hxF hxE
  have he : Tendsto (fun n => ((∑ j ∈ Finset.range n, f (n-j) (T^[j] x)) -
      birkhoffSum T g n x) / (n : ℝ)) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := ((tendsto_order.mp hb).2 (ε/2) (by linarith)).exists
    have hplus : Tendsto (fun n => birkhoffSum T F (n+N) x / (n+N : ℕ))
        atTop (𝓝 (∫ x, F x ∂μ)) := (tendsto_add_atTop_iff_nat N).mpr hxF
    have hdiff := hplus.sub (tendsto_shift_denominator hxF N)
    simp only [sub_self] at hdiff
    have hupper := ((tendsto_add_atTop_iff_nat N).mpr (hxE N)).add (hdiff.const_mul 2)
    simp only [mul_zero,add_zero] at hupper
    obtain ⟨k,hk⟩ := eventually_atTop.mp ((tendsto_order.mp hupper).2 ε (by linarith))
    refine ⟨max k 1 + N,?_⟩
    intro m hm
    obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le (show N ≤ m by omega)
    have hn : k ≤ n := by omega
    have hnp : 0 < N+n := by omega
    have hpos : (0 : ℝ) < (N+n : ℕ) := by exact_mod_cast hnp
    rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hpos]
    have hc := triangle_error_bound hf hg T n N x
    have hle := div_le_div_of_nonneg_right hc (show (0 : ℝ) ≤ (n+N : ℕ) by positivity)
    have hu := hk n hn
    rw [add_comm N n]
    apply lt_of_le_of_lt hle
    simpa only [add_div,mul_div_assoc,sub_div] using hu
  have hz := he.add hx
  simp only [zero_add] at hz
  convert hz using 1
  funext n
  ring

end EntropyRateDimension.ErgodicAux

end

end OAI
end

theorem solution.{uα} : type_of% @OAI.EntropyRateDimension.ErgodicAux.ae_tendsto_triangle_oai.{uα} := @OAI.EntropyRateDimension.ErgodicAux.ae_tendsto_triangle_oai.{uα}
