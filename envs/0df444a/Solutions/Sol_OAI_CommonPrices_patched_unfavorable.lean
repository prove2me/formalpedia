-- Prove2me | solution 1 for OAI.CommonPrices.patched_unfavorable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T21:40:34.082008+00:00
-- url     : https://prove2.me/submissions/3692bdee-3aab-495a-906e-063ea69cf6b0

import Mathlib
import Definitions.Def_OAIQWCDE000

section
-- module Solutions.OAIQW_DiskMaximal.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace

noncomputable section

namespace DiskGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem mem_tangent_ball_iff {z y θ : E} (hθ : ‖θ‖ = 1) {L : ℝ} (hL : 0 < L) :
    y ∈ Metric.ball (z + L • θ) L ↔ ‖y - z‖ ^ 2 < 2 * L * ⟪y - z, θ⟫ := by
  rw [Metric.mem_ball, dist_eq_norm]
  have hv : y - (z + L • θ) = (y - z) - L • θ := by abel
  rw [hv, ← sq_lt_sq₀ (norm_nonneg _) hL.le, norm_sub_sq_real,
    norm_smul, Real.norm_eq_abs, abs_of_pos hL, hθ, mul_one, real_inner_smul_right]
  constructor <;> intro h <;> nlinarith

theorem tangent_ball_mono {z θ : E} (hθ : ‖θ‖ = 1) {L L' : ℝ}
    (hL : 0 < L) (hLL' : L ≤ L') :
    Metric.ball (z + L • θ) L ⊆ Metric.ball (z + L' • θ) L' := by
  intro y hy
  rw [mem_tangent_ball_iff hθ hL] at hy
  rw [mem_tangent_ball_iff hθ (hL.trans_le hLL')]
  have hinner : 0 < ⟪y - z, θ⟫ := by
    by_contra hh
    have hh' : ⟪y - z, θ⟫ ≤ 0 := le_of_not_gt hh
    have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2 * L by positivity) hh'
    nlinarith [sq_nonneg ‖y - z‖]
  exact hy.trans_le (mul_le_mul_of_nonneg_right (by linarith) hinner.le)

theorem mem_tangent_ball_iff_entry {z y θ : E} (hθ : ‖θ‖ = 1)
    {L : ℝ} (hL : 0 < L) (ha : 0 < ⟪y - z, θ⟫) :
    y ∈ Metric.ball (z + L • θ) L ↔ entryParameter z y θ < L := by
  rw [mem_tangent_ball_iff hθ hL, entryParameter, div_lt_iff₀ (by positivity)]
  ring_nf

/-- Uniform estimate on the affine difference of squared distances in a thin shell. -/
theorem shell_square_error {l δ d : ℝ} (hl : 0 ≤ l) (hl3 : l ≤ 3)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4) (hd : 0 ≤ d) (hclose : |d - l| ≤ 2 * δ) :
    |d ^ 2 - l ^ 2| ≤ 13 * δ := by
  have hd_upper : d ≤ l + 2 * δ := (abs_le.mp hclose).2 |> fun h => by linarith
  have hsum : 0 ≤ d + l := add_nonneg hd hl
  calc
    |d ^ 2 - l ^ 2| = |d - l| * (d + l) := by
      rw [show d ^ 2 - l ^ 2 = (d - l) * (d + l) by ring, abs_mul, abs_of_nonneg hsum]
    _ ≤ (2 * δ) * (d + l) := mul_le_mul_of_nonneg_right hclose hsum
    _ ≤ 13 * δ := by nlinarith

/-- A shell point separated from the tangency point has positive radial projection. -/
theorem shell_projection_lower {ρ δ l a w2 : ℝ}
    (hρ : 0 < ρ) (hl : 0 < l) (hl3 : l ≤ 3)
    (hδ : δ ≤ ρ ^ 2 / 1600) (hw : ρ ^ 2 ≤ w2)
    (herr : |w2 - 2 * l * a| ≤ 13 * δ) :
    ρ ^ 2 / 12 ≤ a := by
  have hr2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have he := (abs_le.mp herr).2
  have hla : 0 < a := by nlinarith
  nlinarith

theorem entry_window {ρ δ l a w2 : ℝ}
    (hρ : 0 < ρ) (hδ : 0 ≤ δ) (ha : ρ ^ 2 / 12 ≤ a)
    (herr : |w2 - 2 * l * a| ≤ 13 * δ) :
    |w2 / (2 * a) - l| ≤ 78 * δ / ρ ^ 2 := by
  have hr2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have h2a : 0 < 2 * a := by positivity
  rw [show w2 / (2 * a) - l = (w2 - 2 * l * a) / (2 * a) by field_simp,
    abs_div, abs_of_pos h2a]
  calc
    |w2 - 2 * l * a| / (2 * a) ≤ 13 * δ / (2 * a) :=
      div_le_div_of_nonneg_right herr h2a.le
    _ ≤ 78 * δ / ρ ^ 2 := by
      apply (div_le_div_iff₀ h2a hr2).2
      nlinarith [mul_le_mul_of_nonneg_right ha hδ]

/-- Bound for the entry parameter for an actual shell near a tangent disk. -/
theorem shell_entry_window {z y θ : E} (hθ : ‖θ‖ = 1) {l ρ δ : ℝ}
    (hl : 1 / 2 ≤ l) (hl3 : l ≤ 3) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ ^ 2 / 1600)
    (hsep : ρ ≤ ‖y - z‖)
    (hclose : |dist y (z + l • θ) - l| ≤ 2 * δ) :
    ρ ^ 2 / 12 ≤ ⟪y - z, θ⟫ ∧
    |entryParameter z y θ - l| ≤ 78 * δ / ρ ^ 2 := by
  have hl0 : 0 < l := by linarith
  have hδ1 : δ ≤ 1 / 4 := by nlinarith
  have hsq : ρ ^ 2 ≤ ‖y - z‖ ^ 2 :=
    (sq_le_sq₀ hρ.le (norm_nonneg _)).2 hsep
  have hd := shell_square_error hl0.le hl3 hδ.le hδ1 (dist_nonneg (x := y)) hclose
  have hv : y - (z + l • θ) = (y - z) - l • θ := by abel
  have herr : |‖y - z‖ ^ 2 - 2 * l * ⟪y - z, θ⟫| ≤ 13 * δ := by
    rw [dist_eq_norm, hv, norm_sub_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hl0, hθ, mul_one] at hd
    convert hd using 1
    congr 1
    ring
  have ha := shell_projection_lower hρ hl0 hl3 hδρ hsq herr
  exact ⟨ha, entry_window hρ hδ.le ha herr⟩

theorem earlier_tangent_disk_subset {z θ : E} (hθ : ‖θ‖ = 1) {l ρ δ : ℝ}
    (hl : 1 / 2 ≤ l) (hl3 : l ≤ 3) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ ^ 2 / 1600) :
    {y : E | ρ ≤ ‖y - z‖} ∩
      Metric.ball (z + (l - 200 * δ / ρ ^ 2) • θ) (l - 200 * δ / ρ ^ 2) ⊆
      Metric.ball (z + l • θ) (l - 2 * δ) := by
  let v : ℝ := 200 * δ / ρ ^ 2
  have hr2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hvpos : 0 < v := by dsimp [v]; positivity
  have hvsmall : v ≤ 1 / 8 := by
    dsimp [v]
    apply (div_le_iff₀ hr2).2
    linarith
  have hv_eq : v * ρ ^ 2 = 200 * δ := by
    dsimp [v]; exact div_mul_cancel₀ _ hr2.ne'
  have hl0 : 0 < l := by linarith
  have hlv : 0 < l - v := by linarith
  have hδquarter : δ ≤ 1 / 4 := by nlinarith
  have hrad : 0 < l - 2 * δ := by nlinarith
  rintro y ⟨hsep, hy⟩
  change y ∈ Metric.ball (z + (l - v) • θ) (l - v) at hy
  rw [mem_tangent_ball_iff hθ hlv] at hy
  have hnorm : ρ ^ 2 ≤ ‖y - z‖ ^ 2 :=
    (sq_le_sq₀ hρ.le (norm_nonneg _)).2 hsep
  have hapos : 0 < ⟪y - z, θ⟫ := by
    by_contra ha
    have hmul := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ 2 * (l - v) by positivity) (le_of_not_gt ha)
    nlinarith
  have halower : ρ ^ 2 / 6 < ⟪y - z, θ⟫ := by nlinarith
  have hva := mul_lt_mul_of_pos_left halower hvpos
  have hsqdist : dist y (z + l • θ) ^ 2 < (l - 2 * δ) ^ 2 := by
    rw [dist_eq_norm, show y - (z + l • θ) = (y - z) - l • θ by abel,
      norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hl0, hθ, mul_one]
    nlinarith [mul_le_mul_of_nonneg_right hl3 hδ.le]
  exact (sq_lt_sq₀ dist_nonneg hrad.le).1 hsqdist

end DiskGeometry

namespace DiskGeometry

/-- Cancellation of translated monotone integrals on a finite interval. -/
theorem monotone_increment_interval {G : ℝ → ℝ} (hG : Monotone G)
    {C v : ℝ} (h0 : ∀ x, 0 ≤ G x) (hC : ∀ x, G x ≤ C) (hv : 0 ≤ v)
    (a b : ℝ) :
    (∫ l in a..b, (G (l + v) - G (l - v))) ≤ 2 * v * C := by
  have hp : Monotone (fun l => G (l + v)) := hG.comp (by intro x y h; dsimp; linarith)
  have hm : Monotone (fun l => G (l - v)) := hG.comp (fun _ _ h => sub_le_sub_right h v)
  rw [intervalIntegral.integral_sub hp.intervalIntegrable hm.intervalIntegrable,
    intervalIntegral.integral_comp_add_right, intervalIntegral.integral_comp_sub_right,
    intervalIntegral.integral_interval_sub_interval_comm' hG.intervalIntegrable
      hG.intervalIntegrable hG.intervalIntegrable]
  have hn : 0 ≤ ∫ l in a - v..a + v, G l :=
    intervalIntegral.integral_nonneg_of_forall (by linarith) h0
  have hb : (∫ l in b - v..b + v, G l) ≤ 2 * v * C := by
    calc
      (∫ l in b - v..b + v, G l) ≤ ∫ l in b - v..b + v, C :=
        intervalIntegral.integral_mono (by linarith) hG.intervalIntegrable
          intervalIntegrable_const hC
      _ = 2 * v * C := by
        rw [intervalIntegral.integral_const]
        change ((b + v) - (b - v)) * C = _
        ring
  linarith

theorem monotone_increment_integrable {G : ℝ → ℝ} (hG : Monotone G)
    {C v : ℝ} (h0 : ∀ x, 0 ≤ G x) (hC : ∀ x, G x ≤ C) (hv : 0 ≤ v) :
    Integrable (fun l => G (l + v) - G (l - v)) ∧
      (∫ l, (G (l + v) - G (l - v))) ≤ 2 * v * C := by
  have hp : Monotone (fun l => G (l + v)) := hG.comp (by intro x y h; dsimp; linarith)
  have hm : Monotone (fun l => G (l - v)) := hG.comp (fun _ _ h => sub_le_sub_right h v)
  have hn (l : ℝ) : 0 ≤ G (l + v) - G (l - v) := sub_nonneg.mpr (hG (by linarith))
  have hi (a b : ℝ) : IntervalIntegrable (fun l => G (l + v) - G (l - v)) volume a b :=
    hp.intervalIntegrable.sub hm.intervalIntegrable
  have htop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hbot : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot := tendsto_neg_atTop_atBot.comp htop
  have hint : Integrable (fun l => G (l + v) - G (l - v)) := by
    apply integrable_of_intervalIntegral_norm_bounded (2 * v * C)
      (fun n : ℕ => (hi (-(n : ℝ)) n).1) hbot htop
    exact Eventually.of_forall (fun n => by
      simp_rw [Real.norm_of_nonneg (hn _)]
      exact monotone_increment_interval hG h0 hC hv _ _)
  refine ⟨hint, ?_⟩
  exact le_of_tendsto (intervalIntegral_tendsto_integral hint hbot htop)
    (Eventually.of_forall (fun n => monotone_increment_interval hG h0 hC hv (-(n : ℝ)) n))

/-- The permitted jump times have uniformly bounded length, independent of the
size of the original positive measure. Only its truncated distribution is used. -/
theorem monotone_jump_window_measure {H : ℝ → ℝ} (hH : Monotone H)
    (hH0 : ∀ l, 0 ≤ H l) {T U v : ℝ} (hT : 0 ≤ T) (hU : 0 < U) (hv : 0 ≤ v) :
    volume {l | H (l - v) ≤ T ∧ U ≤ H (l + v) - H (l - v)} ≤
      ENNReal.ofReal (2 * v * (1 + T / U)) := by
  let G : ℝ → ℝ := fun l => min (H l) (T + U)
  have hG : Monotone G := hH.min monotone_const
  have hG0 : ∀ l, 0 ≤ G l := fun l => le_min (hH0 l) (by positivity)
  have hGC : ∀ l, G l ≤ T + U := fun l => min_le_right _ _
  obtain ⟨hi, hb⟩ := monotone_increment_integrable hG hG0 hGC hv
  have hn (l : ℝ) : 0 ≤ G (l + v) - G (l - v) := sub_nonneg.mpr (hG (by linarith))
  have hmi : Integrable (fun l => (G (l + v) - G (l - v)) / U) := hi.div_const U
  have hm := hmi.measure_le_integral
    (Eventually.of_forall (fun l => div_nonneg (hn l) hU.le))
    (s := {l | H (l - v) ≤ T ∧ U ≤ H (l + v) - H (l - v)}) (by
      intro l hl
      rw [le_div_iff₀ hU, one_mul]
      have hd : G (l - v) = H (l - v) := min_eq_left (by linarith [hl.1])
      rw [hd]
      change U ≤ min (H (l + v)) (T + U) - H (l - v)
      rw [le_sub_iff_add_le, le_min_iff]
      exact ⟨by linarith [hl.2], by linarith [hl.1]⟩)
  calc
    volume {l | H (l - v) ≤ T ∧ U ≤ H (l + v) - H (l - v)} ≤
        ENNReal.ofReal (∫ l, (G (l + v) - G (l - v)) / U) := hm
    _ ≤ ENNReal.ofReal (2 * v * (1 + T / U)) := by
      apply ENNReal.ofReal_le_ofReal
      rw [integral_div]
      calc
        (∫ l, G (l + v) - G (l - v)) / U ≤ (2 * v * (T + U)) / U :=
          div_le_div_of_nonneg_right hb hU.le
        _ = 2 * v * (1 + T / U) := by field_simp; ring

end DiskGeometry

namespace DiskGeometry

/-- A polar-coordinate area bound from uniform lengths of radial sections. -/
theorem volume_le_radial_sections {s : Set ℂ} (hs : MeasurableSet s)
    (z : ℂ) {R : ℝ} (hR : 0 ≤ R) {B : ℝ≥0∞}
    (hbound : ∀ x ∈ s, ‖x - z‖ ≤ R)
    (hsections : ∀ θ : ℝ, volume {r : ℝ | 0 < r ∧
      z + (r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) ∈ s} ≤ B) :
    volume s ≤ ENNReal.ofReal (2 * Real.pi * R) * B := by
  classical
  let f : ℂ → ℝ≥0∞ := s.indicator 1
  have hf : Measurable f := measurable_const.indicator hs
  have hfc : Measurable (fun p : ℝ × ℝ => f (z + Complex.polarCoord.symm p)) := by
    apply hf.comp
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hpolar : volume s = ∫⁻ p in polarCoord.target,
      ENNReal.ofReal p.1 * f (z + Complex.polarCoord.symm p) := by
    rw [← lintegral_indicator_one hs]
    change (∫⁻ x, f x) = _
    rw [← lintegral_add_left_eq_self f z,
      ← Complex.lintegral_comp_polarCoord_symm (fun x => f (z + x))]
    rfl
  have hinner (θ : ℝ) : (∫⁻ r in Ioi (0 : ℝ), f (z + Complex.polarCoord.symm (r, θ))) ≤ B := by
    let A : Set ℝ := {r | 0 < r ∧
      z + (r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) ∈ s}
    have hA : MeasurableSet A := measurableSet_Ioi.inter (hs.preimage (by fun_prop))
    calc
      _ = ∫⁻ r, A.indicator 1 r := by
        rw [← lintegral_indicator measurableSet_Ioi]
        apply lintegral_congr
        intro r
        by_cases hr : 0 < r <;>
        by_cases hx : z + (r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) ∈ s <;>
        simp only [f, A, Complex.polarCoord_symm_apply, Set.indicator_apply,
          mem_Ioi, mem_ofPred_eq, Pi.one_apply, hr, hx,
          and_true, and_false, ite_true, ite_false]
      _ = volume A := lintegral_indicator_one hA
      _ ≤ B := hsections θ
  calc
    volume s = ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 * f (z + Complex.polarCoord.symm p) := hpolar
    _ ≤ ∫⁻ p in polarCoord.target,
        ENNReal.ofReal R * f (z + Complex.polarCoord.symm p) := by
      apply setLIntegral_mono' polarCoord.open_target.measurableSet
      intro p hp
      by_cases hx : z + Complex.polarCoord.symm p ∈ s
      · gcongr
        have hn := hbound _ hx
        rw [add_sub_cancel_left, Complex.norm_polarCoord_symm, abs_of_pos hp.1] at hn
        exact hn
      · simp only [f, indicator_of_notMem hx, mul_zero, le_refl]
    _ = ENNReal.ofReal R * ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ∫⁻ r in Ioi (0 : ℝ), f (z + Complex.polarCoord.symm (r, θ)) := by
      rw [lintegral_const_mul _ hfc]
      congr 1
      exact setLIntegral_prod_symm _ hfc.aemeasurable
    _ ≤ ENNReal.ofReal R * ∫⁻ θ in Ioo (-Real.pi) Real.pi, B := by
      gcongr with θ
      exact hinner θ
    _ = ENNReal.ofReal (2 * Real.pi * R) * B := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
      rw [show Real.pi - -Real.pi = 2 * Real.pi by ring]
      rw [mul_comm (2 * Real.pi) R, ENNReal.ofReal_mul hR]
      ac_rfl

end DiskGeometry

namespace DiskGeometry

theorem tangentMass_nonneg (S : Measure ℂ) (ρ : ℝ) (z θ : ℂ) (L : ℝ) :
    0 ≤ tangentMass S ρ z θ L := ENNReal.toReal_nonneg

theorem tangentMass_mono (S : Measure ℂ) [IsFiniteMeasure S] (ρ : ℝ)
    (z θ : ℂ) (hθ : ‖θ‖ = 1) : Monotone (tangentMass S ρ z θ) := by
  intro L L' hLL'
  by_cases hL : 0 < L
  · apply ENNReal.toReal_mono (measure_ne_top S _)
    exact measure_mono (inter_subset_inter_right _ (tangent_ball_mono hθ hL hLL'))
  · have hball : Metric.ball (z + L • θ) L = ∅ := Metric.ball_eq_empty.mpr (le_of_not_gt hL)
    simp only [tangentMass, hball, inter_empty, measure_empty, ENNReal.toReal_zero]
    exact ENNReal.toReal_nonneg

theorem measurable_tangentMass (S : Measure ℂ) [IsFiniteMeasure S] (ρ : ℝ)
    {α : Type*} [MeasurableSpace α] {z θ : α → ℂ} {L : α → ℝ}
    (hz : Measurable z) (hθ : Measurable θ) (hL : Measurable L) :
    Measurable (fun a => tangentMass S ρ (z a) (θ a) (L a)) := by
  have hm : MeasurableSet {p : α × ℂ | ρ ≤ ‖p.2 - z p.1‖ ∧
      dist p.2 (z p.1 + L p.1 • θ p.1) < L p.1} := by
    exact (measurableSet_le measurable_const ((measurable_snd.sub (hz.comp measurable_fst)).norm)).inter
      (measurableSet_lt (measurable_snd.dist ((hz.comp measurable_fst).add
        ((hL.comp measurable_fst).smul (hθ.comp measurable_fst)))) (hL.comp measurable_fst))
  exact (measurable_measure_prodMk_left (ν := S) hm).ennreal_toReal

theorem measurableSet_rayCondition (S : Measure ℂ) [IsFiniteMeasure S]
    (ρ T U v : ℝ) : MeasurableSet {p : ℂ × ℂ | rayCondition S ρ T U v p.1 p.2} := by
  have hn : Measurable (fun p : ℂ × ℂ => ‖p.1 - p.2‖) := by fun_prop
  have hdir : Measurable (fun p : ℂ × ℂ => ‖p.1 - p.2‖⁻¹ • (p.1 - p.2)) := by fun_prop
  have hm := measurable_tangentMass S ρ measurable_snd hdir (hn.sub_const v)
  have hp := measurable_tangentMass S ρ measurable_snd hdir (hn.add_const v)
  exact (measurableSet_le measurable_const hn).inter
    ((measurableSet_le hn measurable_const).inter
      ((measurableSet_le hm measurable_const).inter (measurableSet_le measurable_const (hp.sub hm))))

/-- Full two-dimensional ray-condition estimate, independent of the chosen radius. -/
theorem volume_rayCondition (S : Measure ℂ) [IsFiniteMeasure S] (ρ : ℝ)
    {T U v : ℝ} (hT : 0 ≤ T) (hU : 0 < U) (hv : 0 ≤ v) (z : ℂ) :
    volume {x : ℂ | rayCondition S ρ T U v x z} ≤
      ENNReal.ofReal (6 * Real.pi) * ENNReal.ofReal (2 * v * (1 + T / U)) := by
  have hs : MeasurableSet {x : ℂ | rayCondition S ρ T U v x z} :=
    (measurableSet_rayCondition S ρ T U v).preimage
      (show Measurable (fun x : ℂ => (x, z)) by fun_prop)
  have hbound : ∀ x ∈ {x : ℂ | rayCondition S ρ T U v x z}, ‖x - z‖ ≤ 3 :=
    fun _ h => h.2.1
  have hsections (a : ℝ) : volume {r : ℝ | 0 < r ∧
      z + (r : ℂ) * ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I) ∈
        {x : ℂ | rayCondition S ρ T U v x z}} ≤
      ENNReal.ofReal (2 * v * (1 + T / U)) := by
    let θ : ℂ := (Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I
    have hθ : ‖θ‖ = 1 := by
      simpa only [θ, Complex.ofReal_cos, Complex.ofReal_sin] using Complex.norm_cos_add_sin_mul_I a
    apply le_trans (measure_mono (t := {l : ℝ | tangentMass S ρ z θ (l - v) ≤ T ∧
      U ≤ tangentMass S ρ z θ (l + v) - tangentMass S ρ z θ (l - v)}) ?_)
      (monotone_jump_window_measure (tangentMass_mono S ρ z θ hθ)
        (tangentMass_nonneg S ρ z θ) hT hU hv)
    rintro r ⟨hr, hx⟩
    have hnorm : ‖z + (r : ℂ) * θ - z‖ = r := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hθ, mul_one]
    have hdir : ‖z + (r : ℂ) * θ - z‖⁻¹ • (z + (r : ℂ) * θ - z) = θ := by
      rw [hnorm, add_sub_cancel_left, ← Complex.real_smul, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    change rayCondition S ρ T U v (z + (r : ℂ) * θ) z at hx
    rw [rayCondition] at hx
    rw [hdir, hnorm] at hx
    exact hx.2.2
  simpa only [show (2 : ℝ) * Real.pi * 3 = 6 * Real.pi by ring] using
    volume_le_radial_sections hs z (by norm_num : (0 : ℝ) ≤ 3) hbound hsections

end DiskGeometry

namespace DiskGeometry

theorem measurableSet_thinShell (x : ℂ) (r δ : ℝ) : MeasurableSet (thinShell x r δ) := by
  exact measurableSet_le (by fun_prop) measurable_const

theorem shell_center_bounds {x z : ℂ} {r δ : ℝ} (hr : r ∈ Icc (1 : ℝ) 2)
    (hδ : δ ≤ 1 / 4) (hz : z ∈ thinShell x r δ) :
    1 / 2 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 3 := by
  change |‖z - x‖ - r| ≤ δ at hz
  have hh := abs_le.mp hz
  rw [norm_sub_rev z x] at hh
  constructor <;> linarith [hr.1, hr.2]

theorem shell_pair_close {x y z : ℂ} {r δ : ℝ}
    (hy : y ∈ thinShell x r δ) (hz : z ∈ thinShell x r δ) :
    |‖y - x‖ - ‖x - z‖| ≤ 2 * δ := by
  change |‖y - x‖ - r| ≤ δ at hy
  change |‖z - x‖ - r| ≤ δ at hz
  have hy' := abs_le.mp hy
  have hz' := abs_le.mp hz
  rw [norm_sub_rev z x] at hz'
  exact abs_le.mpr ⟨by linarith [hy'.1, hz'.2], by linarith [hy'.2, hz'.1]⟩

/-- Every distant point of the thin shell crosses the tangent disks in the short window. -/
theorem shell_subset_tangent_difference {z θ : ℂ} (hθ : ‖θ‖ = 1) {l ρ δ : ℝ}
    (hl : 1 / 2 ≤ l) (hl3 : l ≤ 3) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ ^ 2 / 1600) :
    {y : ℂ | ρ ≤ ‖y - z‖ ∧ |‖y - (z + l • θ)‖ - l| ≤ 2 * δ} ⊆
      ({y : ℂ | ρ ≤ ‖y - z‖} ∩
        Metric.ball (z + (l + 200 * δ / ρ ^ 2) • θ) (l + 200 * δ / ρ ^ 2)) \
      ({y : ℂ | ρ ≤ ‖y - z‖} ∩
        Metric.ball (z + (l - 200 * δ / ρ ^ 2) • θ) (l - 200 * δ / ρ ^ 2)) := by
  let v : ℝ := 200 * δ / ρ ^ 2
  have hr2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hvp : 0 < v := by dsimp [v]; positivity
  have hvs : v ≤ 1 / 8 := by
    dsimp [v]
    apply (div_le_iff₀ hr2).2
    linarith
  have hlm : 0 < l - v := by linarith
  have hlp : 0 < l + v := by linarith
  have h78 : 78 * δ / ρ ^ 2 < v := by
    dsimp [v]
    exact (div_lt_div_iff_of_pos_right hr2).2 (by linarith)
  rintro y ⟨hsep, hclose⟩
  obtain ⟨ha, hw⟩ := shell_entry_window hθ hl hl3 hρ hρ1 hδ hδρ hsep (by
    simpa only [dist_eq_norm] using hclose)
  have ha0 : 0 < ⟪y - z, θ⟫ := lt_of_lt_of_le (by positivity) ha
  have hentrylo : l - v < entryParameter z y θ := by linarith [(abs_le.mp hw).1]
  have hentryhi : entryParameter z y θ < l + v := by linarith [(abs_le.mp hw).2]
  refine ⟨⟨hsep, (mem_tangent_ball_iff_entry hθ hlp ha0).2 hentryhi⟩, ?_⟩
  rintro ⟨_, hm⟩
  have hm' := (mem_tangent_ball_iff_entry hθ hlm ha0).1 hm
  linarith

/-- The shell mass away from a cap is bounded by the one-dimensional tangent-mass jump. -/
theorem shell_mass_le_jump (S : Measure ℂ) [IsFiniteMeasure S]
    {x z : ℂ} {r ρ δ : ℝ} (hr : r ∈ Icc (1 : ℝ) 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ ^ 2 / 1600) (hz : z ∈ thinShell x r δ) :
    (S (thinShell x r δ \ Metric.ball z ρ)).toReal ≤
      tangentMass S ρ z (‖x - z‖⁻¹ • (x - z)) (‖x - z‖ + 200 * δ / ρ ^ 2) -
      tangentMass S ρ z (‖x - z‖⁻¹ • (x - z)) (‖x - z‖ - 200 * δ / ρ ^ 2) := by
  let l : ℝ := ‖x - z‖
  let θ : ℂ := l⁻¹ • (x - z)
  have hδquarter : δ ≤ 1 / 4 := by nlinarith
  obtain ⟨hl, hl3⟩ := shell_center_bounds hr hδquarter hz
  have hl0 : 0 < l := by dsimp [l]; linarith
  have hθ : ‖θ‖ = 1 := by
    dsimp only [θ]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hl0.le)]
    exact inv_mul_cancel₀ hl0.ne'
  have hx : z + l • θ = x := by
    dsimp only [θ]
    rw [smul_smul, mul_inv_cancel₀ hl0.ne', one_smul]
    abel
  let A := {y : ℂ | ρ ≤ ‖y - z‖} ∩
      Metric.ball (z + (l - 200 * δ / ρ ^ 2) • θ) (l - 200 * δ / ρ ^ 2)
  let B := {y : ℂ | ρ ≤ ‖y - z‖} ∩
      Metric.ball (z + (l + 200 * δ / ρ ^ 2) • θ) (l + 200 * δ / ρ ^ 2)
  have hAm : MeasurableSet A := (measurableSet_le measurable_const (by fun_prop)).inter
    Metric.isOpen_ball.measurableSet
  have hsub : thinShell x r δ \ Metric.ball z ρ ⊆ B \ A := by
    apply subset_trans _ (shell_subset_tangent_difference hθ hl hl3 hρ hρ1 hδ hδρ)
    rintro y ⟨hy, hyz⟩
    exact ⟨le_of_not_gt (by simpa only [Metric.mem_ball, dist_eq_norm] using hyz),
      by rw [hx]; exact shell_pair_close hy hz⟩
  have hAB : A ⊆ B := by
    apply inter_subset_inter_right
    apply tangent_ball_mono hθ
    · have : 200 * δ / ρ ^ 2 ≤ 1 / 8 := by
        apply (div_le_iff₀ (sq_pos_of_pos hρ)).2
        linarith
      change 0 < l - 200 * δ / ρ ^ 2
      linarith
    · have : 0 ≤ 200 * δ / ρ ^ 2 := by positivity
      linarith
  have hmass := ENNReal.toReal_mono (measure_ne_top S (B \ A)) (measure_mono hsub)
  rw [measure_sdiff hAB hAm.nullMeasurableSet (measure_ne_top S A),
    ENNReal.toReal_sub_of_le (measure_mono hAB) (measure_ne_top S B)] at hmass
  exact hmass

/-- The earlier tangent-disk mass is controlled by the concentric interior mass. -/
theorem earlier_mass_le_interior (S : Measure ℂ) [IsFiniteMeasure S]
    {x z : ℂ} {r ρ δ : ℝ} (hr : r ∈ Icc (1 : ℝ) 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ ^ 2 / 1600) (hz : z ∈ thinShell x r δ) :
    tangentMass S ρ z (‖x - z‖⁻¹ • (x - z)) (‖x - z‖ - 200 * δ / ρ ^ 2) ≤
      (S (Metric.ball x (r - δ))).toReal := by
  let l : ℝ := ‖x - z‖
  let θ : ℂ := l⁻¹ • (x - z)
  have hδquarter : δ ≤ 1 / 4 := by nlinarith
  obtain ⟨hl, hl3⟩ := shell_center_bounds hr hδquarter hz
  have hl0 : 0 < l := by dsimp [l]; linarith
  have hθ : ‖θ‖ = 1 := by
    dsimp only [θ]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hl0.le)]
    exact inv_mul_cancel₀ hl0.ne'
  have hx : z + l • θ = x := by
    dsimp only [θ]
    rw [smul_smul, mul_inv_cancel₀ hl0.ne', one_smul]
    abel
  apply ENNReal.toReal_mono (measure_ne_top S _)
  apply measure_mono
  apply (earlier_tangent_disk_subset hθ hl hl3 hρ hρ1 hδ hδρ).trans
  rw [hx]
  apply Metric.ball_subset_ball
  change |‖z - x‖ - r| ≤ δ at hz
  have hh := (abs_le.mp hz).2
  rw [norm_sub_rev z x] at hh
  change l - 2 * δ ≤ r - δ
  dsimp [l]
  linarith

end DiskGeometry

namespace DiskGeometry

/-- Area of a strip with continuously moving interval fibers. -/
theorem volume_interval_fibers (c : ℝ → ℝ) (hc : Continuous c)
    (lo hi w : ℝ) :
    volume {p : ℝ × ℝ | p.2 ∈ Icc lo hi ∧
      p.1 ∈ Icc (c p.2 - w) (c p.2 + w)} =
      ENNReal.ofReal (hi - lo) * ENNReal.ofReal (2 * w) := by
  have hs : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Icc lo hi ∧
      p.1 ∈ Icc (c p.2 - w) (c p.2 + w)} := by
    exact (measurableSet_Icc.preimage continuous_snd.measurable).inter
      ((isClosed_le (hc.comp continuous_snd |>.sub continuous_const) continuous_fst).measurableSet.inter
        (isClosed_le continuous_fst (hc.comp continuous_snd |>.add continuous_const)).measurableSet)
  change (volume.prod volume) _ = _
  rw [Measure.prod_apply_symm hs]
  have hf (y : ℝ) :
      volume ((fun x : ℝ => (x, y)) ⁻¹' {p : ℝ × ℝ | p.2 ∈ Icc lo hi ∧
        p.1 ∈ Icc (c p.2 - w) (c p.2 + w)}) =
      (Icc lo hi).indicator (fun _ => ENNReal.ofReal (2 * w)) y := by
    by_cases hy : y ∈ Icc lo hi
    · simp only [preimage_ofPred_eq, hy, true_and, indicator_of_mem hy]
      change volume (Icc (c y - w) (c y + w)) = _
      rw [Real.volume_Icc]
      congr 1
      ring
    · simp only [preimage_ofPred_eq, hy, false_and, ofPred_false, measure_empty, indicator_of_notMem hy]
  simp_rw [hf]
  rw [lintegral_indicator measurableSet_Icc, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Icc, mul_comm]

/-- A nonvertical affine strip cut off in the second coordinate. -/
theorem volume_affine_strip {a : ℝ} (ha : a ≠ 0) (b c d R w : ℝ) :
    volume {p : ℝ × ℝ | |p.2 - d| ≤ R ∧ |a * p.1 + b * p.2 + c| ≤ w} =
      ENNReal.ofReal (2 * R) * ENNReal.ofReal (2 * (w / |a|)) := by
  have hs : {p : ℝ × ℝ | |p.2 - d| ≤ R ∧ |a * p.1 + b * p.2 + c| ≤ w} =
      {p : ℝ × ℝ | p.2 ∈ Icc (d - R) (d + R) ∧
        p.1 ∈ Icc (-(b * p.2 + c) / a - w / |a|)
          (-(b * p.2 + c) / a + w / |a|)} := by
    ext p
    simp only [mem_ofPred_eq, mem_Icc]
    have heq : a * p.1 + b * p.2 + c = a * (p.1 - -(b * p.2 + c) / a) := by
      field_simp
      ring
    rw [heq, abs_mul, ← le_div_iff₀' (abs_pos.mpr ha)]
    simp only [abs_le]
    constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> constructor <;> constructor <;> linarith
  rw [hs]
  rw [volume_interval_fibers (fun y => -(b * y + c) / a) (by fun_prop)]
  congr 2
  ring

/-- At least one coordinate sees half the Euclidean separation. -/
theorem complex_coordinate_separation {z : ℂ} {ρ : ℝ} (hz : ρ ≤ ‖z‖) :
    ρ / 2 ≤ |z.re| ∨ ρ / 2 ≤ |z.im| := by
  by_contra h
  push Not at h
  have hnorm : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  linarith

/-- The centers of two separated points lying on an almost common circle form
an affine strip of small area. No selected radius occurs here. -/
theorem volume_two_point_strip {y z : ℂ} {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 ≤ δ)
    (hyz : ρ ≤ ‖y - z‖) :
    volume {x : ℂ | ‖x - z‖ ≤ 3 ∧ |‖x - y‖ ^ 2 - ‖x - z‖ ^ 2| ≤ 13 * δ} ≤
      ENNReal.ofReal (156 * δ / ρ) := by
  let a : ℝ := 2 * (z.re - y.re)
  let b : ℝ := 2 * (z.im - y.im)
  let c : ℝ := ‖y‖ ^ 2 - ‖z‖ ^ 2
  have halg (x : ℂ) : ‖x - y‖ ^ 2 - ‖x - z‖ ^ 2 = a * x.re + b * x.im + c := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, a, b, c]
    ring
  have hsplit := complex_coordinate_separation hyz
  have hmain (a b c d : ℝ) (ha : ρ ≤ |a|) :
      volume {p : ℝ × ℝ | |p.2 - d| ≤ 3 ∧ |a * p.1 + b * p.2 + c| ≤ 13 * δ} ≤
        ENNReal.ofReal (156 * δ / ρ) := by
    have hap : 0 < |a| := hρ.trans_le ha
    rw [volume_affine_strip (abs_pos.mp hap)]
    rw [← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    calc
      (2 * 3) * (2 * (13 * δ / |a|)) = 156 * δ / |a| := by ring
      _ ≤ 156 * δ / ρ := div_le_div_of_nonneg_left (by positivity) hρ ha
  rcases hsplit with hre | him
  · have ha : ρ ≤ |a| := by
      dsimp [a]
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_sub_comm]
      simpa only [Complex.sub_re] using (show ρ ≤ 2 * |(y - z).re| by linarith)
    let s : Set (ℝ × ℝ) := {p | |p.2 - z.im| ≤ 3 ∧ |a * p.1 + b * p.2 + c| ≤ 13 * δ}
    have hsub : {x : ℂ | ‖x - z‖ ≤ 3 ∧ |‖x - y‖ ^ 2 - ‖x - z‖ ^ 2| ≤ 13 * δ} ⊆
        Complex.measurableEquivRealProd ⁻¹' s := by
      intro x hx
      exact ⟨(Complex.abs_im_le_norm (x - z)).trans hx.1, by simpa [halg x] using hx.2⟩
    have hs : MeasurableSet s := by
      exact (isClosed_le (show Continuous (fun p : ℝ × ℝ => |p.2 - z.im|) from by fun_prop)
        continuous_const).measurableSet.inter
        (isClosed_le (show Continuous (fun p : ℝ × ℝ => |a * p.1 + b * p.2 + c|) from by fun_prop)
        continuous_const).measurableSet
    calc
      _ ≤ volume (Complex.measurableEquivRealProd ⁻¹' s) := measure_mono hsub
      _ = volume s := Complex.volume_preserving_equiv_real_prod.measure_preimage hs.nullMeasurableSet
      _ ≤ _ := hmain a b c z.im ha
  · have hb : ρ ≤ |b| := by
      dsimp [b]
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_sub_comm]
      simpa only [Complex.sub_im] using (show ρ ≤ 2 * |(y - z).im| by linarith)
    let s : Set (ℝ × ℝ) := {p | |p.2 - z.re| ≤ 3 ∧ |b * p.1 + a * p.2 + c| ≤ 13 * δ}
    have hmp : MeasurePreserving (fun x : ℂ => (x.im, x.re)) :=
      Measure.measurePreserving_swap.comp Complex.volume_preserving_equiv_real_prod
    have hsub : {x : ℂ | ‖x - z‖ ≤ 3 ∧ |‖x - y‖ ^ 2 - ‖x - z‖ ^ 2| ≤ 13 * δ} ⊆
        (fun x : ℂ => (x.im, x.re)) ⁻¹' s := by
      intro x hx
      refine ⟨(Complex.abs_re_le_norm (x - z)).trans hx.1, ?_⟩
      simpa only [halg x, add_comm (a * x.re) (b * x.im)] using hx.2
    have hs : MeasurableSet s := by
      exact (isClosed_le (show Continuous (fun p : ℝ × ℝ => |p.2 - z.re|) from by fun_prop)
        continuous_const).measurableSet.inter
        (isClosed_le (show Continuous (fun p : ℝ × ℝ => |b * p.1 + a * p.2 + c|) from by fun_prop)
        continuous_const).measurableSet
    calc
      _ ≤ volume ((fun x : ℂ => (x.im, x.re)) ⁻¹' s) := measure_mono hsub
      _ = volume s := hmp.measure_preimage hs.nullMeasurableSet
      _ ≤ _ := hmain b a c z.re hb

end DiskGeometry

namespace DiskGeometry

theorem measurableSet_pairCondition (ρ δ : ℝ) :
    MeasurableSet {p : (ℂ × ℂ) × ℂ | pairCondition ρ δ p.1.1 p.1.2 p.2} := by
  have hn : Measurable (fun p : (ℂ × ℂ) × ℂ => ‖p.1.1 - p.1.2‖) := by fun_prop
  have hc : Measurable (fun p : (ℂ × ℂ) × ℂ => |‖p.2 - p.1.1‖ - ‖p.1.1 - p.1.2‖|) := by fun_prop
  have hs : Measurable (fun p : (ℂ × ℂ) × ℂ => ‖p.2 - p.1.2‖) := by fun_prop
  exact (measurableSet_le measurable_const hn).inter
    ((measurableSet_le hn measurable_const).inter
      ((measurableSet_le hc measurable_const).inter (measurableSet_le measurable_const hs)))

theorem volume_pairCondition {ρ δ : ℝ} (hρ : 0 < ρ)
    (hδ : 0 ≤ δ) (hδquarter : δ ≤ 1 / 4) (z y : ℂ) :
    volume {x : ℂ | pairCondition ρ δ x z y} ≤ ENNReal.ofReal (156 * δ / ρ) := by
  by_cases hsep : ρ ≤ ‖y - z‖
  · apply le_trans (measure_mono (t := {x : ℂ | ‖x - z‖ ≤ 3 ∧
      |‖x - y‖ ^ 2 - ‖x - z‖ ^ 2| ≤ 13 * δ}) ?_)
      (volume_two_point_strip hρ hδ hsep)
    intro x hx
    obtain ⟨hl, hl3, hc, _⟩ := hx
    refine ⟨hl3, ?_⟩
    rw [norm_sub_rev x y]
    exact shell_square_error (norm_nonneg _) hl3 hδ hδquarter (norm_nonneg _) hc
  · have he : {x : ℂ | pairCondition ρ δ x z y} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => hsep h.2.2.2
    rw [he, measure_empty]
    exact bot_le

theorem measurable_pairMass (ν : Measure ℂ) [IsFiniteMeasure ν] (ρ δ : ℝ) :
    Measurable (fun p : ℂ × ℂ => pairMass ν ρ δ p.1 p.2) :=
  measurable_measure_prodMk_left (measurableSet_pairCondition ρ δ)

theorem measurable_rayIndicator (S : Measure ℂ) [IsFiniteMeasure S] (ρ T U v : ℝ) :
    Measurable (fun p : ℂ × ℂ => rayIndicator S ρ T U v p.1 p.2) :=
  measurable_const.indicator (measurableSet_rayCondition S ρ T U v)

/-- The first contribution to the Borel majorant is controlled by the two-point strip. -/
theorem lintegral_pairMass (ν : Measure ℂ) [IsFiniteMeasure ν] {ρ δ : ℝ}
    (hρ : 0 < ρ) (hδ : 0 ≤ δ) (hδquarter : δ ≤ 1 / 4) :
    (∫⁻ x : ℂ, ∫⁻ z : ℂ, pairMass ν ρ δ x z ∂ν) ≤
      ENNReal.ofReal (156 * δ / ρ) * ν univ * ν univ := by
  rw [lintegral_lintegral_swap (measurable_pairMass ν ρ δ).aemeasurable]
  apply le_trans (lintegral_mono (fun z => ?_))
    (by rw [lintegral_const])
  let A : Set (ℂ × ℂ) := {p | pairCondition ρ δ p.1 z p.2}
  have hA : MeasurableSet A := (measurableSet_pairCondition ρ δ).preimage
    (show Measurable (fun p : ℂ × ℂ => ((p.1, z), p.2)) by fun_prop)
  have he (x : ℂ) : pairMass ν ρ δ x z = ∫⁻ y : ℂ, A.indicator 1 (x, y) ∂ν := by
    rw [show (fun y : ℂ => A.indicator 1 (x, y)) =
      {y : ℂ | pairCondition ρ δ x z y}.indicator 1 by
        ext y; exact (indicator_comp_right (fun y : ℂ => (x, y))).symm]
    exact (lintegral_indicator_one ((measurableSet_pairCondition ρ δ).preimage
      (show Measurable (fun y : ℂ => ((x, z), y)) by fun_prop))).symm
  simp_rw [he]
  rw [lintegral_lintegral_swap (f := fun x y : ℂ => A.indicator 1 (x, y))
    (measurable_const.indicator hA).aemeasurable]
  calc
    _ ≤ ∫⁻ y : ℂ, ENNReal.ofReal (156 * δ / ρ) ∂ν := by
      apply lintegral_mono
      intro y
      have hei : (fun x : ℂ => A.indicator (1 : ℂ × ℂ → ℝ≥0∞) (x, y)) =
          {x : ℂ | pairCondition ρ δ x z y}.indicator 1 := by
        ext x
        exact (indicator_comp_right (fun x : ℂ => (x, y))).symm
      dsimp only
      rw [hei]
      have hsm : MeasurableSet {x : ℂ | pairCondition ρ δ x z y} :=
        (measurableSet_pairCondition ρ δ).preimage
          (show Measurable (fun x : ℂ => ((x, z), y)) by fun_prop)
      exact (lintegral_indicator_one hsm).le.trans (volume_pairCondition hρ hδ hδquarter z y)
    _ = _ := lintegral_const _

/-- The second contribution is controlled by monotone ray jumps and polar coordinates. -/
theorem lintegral_rayIndicator (ν S : Measure ℂ) [IsFiniteMeasure ν] [IsFiniteMeasure S]
    (ρ : ℝ) {T U v : ℝ} (hT : 0 ≤ T) (hU : 0 < U) (hv : 0 ≤ v) :
    (∫⁻ x : ℂ, ∫⁻ z : ℂ, rayIndicator S ρ T U v x z ∂ν) ≤
      (ENNReal.ofReal (6 * Real.pi) * ENNReal.ofReal (2 * v * (1 + T / U))) * ν univ := by
  rw [lintegral_lintegral_swap (measurable_rayIndicator S ρ T U v).aemeasurable]
  calc
    _ ≤ ∫⁻ _z : ℂ,
        ENNReal.ofReal (6 * Real.pi) * ENNReal.ofReal (2 * v * (1 + T / U)) ∂ν := by
      apply lintegral_mono
      intro z
      have he : (fun x : ℂ => rayIndicator S ρ T U v x z) =
          {x : ℂ | rayCondition S ρ T U v x z}.indicator 1 := by
        ext x
        exact (indicator_comp_right (fun x : ℂ => (x, z))).symm
      dsimp only
      rw [he]
      have hsm : MeasurableSet {x : ℂ | rayCondition S ρ T U v x z} :=
        (measurableSet_rayCondition S ρ T U v).preimage
          (show Measurable (fun x : ℂ => (x, z)) by fun_prop)
      exact (lintegral_indicator_one hsm).le.trans (volume_rayCondition S ρ hT hU hv z)
    _ = _ := lintegral_const _

end DiskGeometry

namespace DiskGeometry

/-- Failure of every cap forces the majorant bracket to be at least one. -/
theorem bad_cap_bracket (S ν : Measure ℂ) [IsFiniteMeasure S] [IsFiniteMeasure ν]
    {x z : ℂ} {r ρ δ T U : ℝ} (hr : r ∈ Icc (1 : ℝ) 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 < δ) (hδρ : δ ≤ ρ ^ 2 / 1600)
    (hT : 0 ≤ T) (hU : 0 < U) (hz : z ∈ thinShell x r δ)
    (hi : S (Metric.ball x (r - δ)) ≤ ENNReal.ofReal T)
    (hb : ENNReal.ofReal (2 * U) < (S + ν) (thinShell x r δ \ Metric.ball z ρ)) :
    1 ≤ (ENNReal.ofReal U)⁻¹ * pairMass ν ρ δ x z +
      rayIndicator S ρ T U (200 * δ / ρ ^ 2) x z := by
  have hδquarter : δ ≤ 1 / 4 := by nlinarith
  obtain ⟨hl, hl3⟩ := shell_center_bounds hr hδquarter hz
  have hcases : ENNReal.ofReal U ≤ ν (thinShell x r δ \ Metric.ball z ρ) ∨
      ENNReal.ofReal U ≤ S (thinShell x r δ \ Metric.ball z ρ) := by
    by_contra h
    push Not at h
    have he2 : ENNReal.ofReal (2 * U) = ENNReal.ofReal U + ENNReal.ofReal U := by
      rw [two_mul, ENNReal.ofReal_add hU.le hU.le]
    have hm : (S + ν) (thinShell x r δ \ Metric.ball z ρ) ≤ ENNReal.ofReal (2 * U) := by
      rw [Measure.add_apply, he2]
      exact add_le_add h.2.le h.1.le
    exact (not_le_of_gt hb) hm
  rcases hcases with hν | hS
  · have hp : ENNReal.ofReal U ≤ pairMass ν ρ δ x z := by
      apply hν.trans (measure_mono ?_)
      rintro y ⟨hy, hsep⟩
      exact ⟨hl, hl3, shell_pair_close hy hz,
        le_of_not_gt (by simpa only [Metric.mem_ball, dist_eq_norm] using hsep)⟩
    calc
      1 = (ENNReal.ofReal U)⁻¹ * ENNReal.ofReal U :=
        (ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hU).ne' ENNReal.ofReal_ne_top).symm
      _ ≤ (ENNReal.ofReal U)⁻¹ * pairMass ν ρ δ x z := mul_le_mul_right hp _
      _ ≤ _ := le_self_add
  · have hi' : (S (Metric.ball x (r - δ))).toReal ≤ T := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hi
      simpa only [ENNReal.toReal_ofReal hT] using this
    have hS' : U ≤ (S (thinShell x r δ \ Metric.ball z ρ)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top S _)).1 hS
    have hc : rayCondition S ρ T U (200 * δ / ρ ^ 2) x z :=
      ⟨hl, hl3, (earlier_mass_le_interior S hr hρ hρ1 hδ hδρ hz).trans hi',
        hS'.trans (shell_mass_le_jump S hr hρ hρ1 hδ hδρ hz)⟩
    have hone : rayIndicator S ρ T U (200 * δ / ρ ^ 2) x z = 1 :=
      indicator_of_mem hc 1
    rw [hone]
    exact le_add_self

theorem measurable_shellMajorant (ν S : Measure ℂ) [IsFiniteMeasure ν] [IsFiniteMeasure S]
    (ρ δ T U : ℝ) : Measurable (shellMajorant ν S ρ δ T U) := by
  exact ((measurable_pairMass ν ρ δ).lintegral_prod_right.const_mul _).add
    ((measurable_rayIndicator S ρ T U (200 * δ / ρ ^ 2)).lintegral_prod_right.const_mul _)

theorem shellMajorant_eq_bracket (ν S : Measure ℂ) [IsFiniteMeasure ν] [IsFiniteMeasure S]
    (ρ δ T U : ℝ) (x : ℂ) :
    shellMajorant ν S ρ δ T U x = (ENNReal.ofReal U)⁻¹ * ∫⁻ z,
      ((ENNReal.ofReal U)⁻¹ * pairMass ν ρ δ x z +
        rayIndicator S ρ T U (200 * δ / ρ ^ 2) x z) ∂ν := by
  have hp : Measurable (fun z : ℂ => pairMass ν ρ δ x z) :=
    (measurable_pairMass ν ρ δ).comp (measurable_const.prodMk measurable_id)
  rw [lintegral_add_left (hp.const_mul _), lintegral_const_mul _ hp]
  unfold shellMajorant
  ring

/-- The majorant is integrable uniformly over all radii. -/
theorem lintegral_shellMajorant (ν S : Measure ℂ) [IsFiniteMeasure ν] [IsFiniteMeasure S]
    {ρ δ T U : ℝ} (hρ : 0 < ρ) (hδ : 0 ≤ δ) (hδquarter : δ ≤ 1 / 4)
    (hT : 0 ≤ T) (hU : 0 < U) :
    (∫⁻ x, shellMajorant ν S ρ δ T U x) ≤
      (ENNReal.ofReal U)⁻¹ ^ 2 * (ENNReal.ofReal (156 * δ / ρ) * ν univ * ν univ) +
      (ENNReal.ofReal U)⁻¹ * ((ENNReal.ofReal (6 * Real.pi) *
        ENNReal.ofReal (2 * (200 * δ / ρ ^ 2) * (1 + T / U))) * ν univ) := by
  have hp : Measurable (fun x : ℂ => ∫⁻ z, pairMass ν ρ δ x z ∂ν) :=
    (measurable_pairMass ν ρ δ).lintegral_prod_right
  have hr : Measurable (fun x : ℂ => ∫⁻ z, rayIndicator S ρ T U (200 * δ / ρ ^ 2) x z ∂ν) :=
    (measurable_rayIndicator S ρ T U (200 * δ / ρ ^ 2)).lintegral_prod_right
  simp only [shellMajorant]
  rw [lintegral_add_left (hp.const_mul _), lintegral_const_mul _ hp, lintegral_const_mul _ hr]
  exact add_le_add
    (mul_le_mul_right (lintegral_pairMass ν hρ hδ hδquarter) _)
    (mul_le_mul_right (lintegral_rayIndicator ν S ρ hT hU (by positivity)) _)

/-- The majorant detects simultaneous failure of concentration at every cap. -/
theorem one_le_majorant_of_no_cap (ν S : Measure ℂ) [IsFiniteMeasure ν] [IsFiniteMeasure S]
    {ρ δ T U : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 < δ)
    (hδρ : δ ≤ ρ ^ 2 / 1600) (hT : 0 ≤ T) (hU : 0 < U)
    {x : ℂ} {r : ℝ} (hr : r ∈ Icc (1 : ℝ) 2)
    (hν : ENNReal.ofReal U ≤ ν (thinShell x r δ))
    (hS : S (Metric.ball x (r - δ)) ≤ ENNReal.ofReal T)
    (hbad : ∀ z ∈ thinShell x r δ,
      ENNReal.ofReal (2 * U) < (S + ν) (thinShell x r δ \ Metric.ball z ρ)) :
    1 ≤ shellMajorant ν S ρ δ T U x := by
  have hu0 : ENNReal.ofReal U ≠ 0 := (ENNReal.ofReal_pos.mpr hU).ne'
  rw [shellMajorant_eq_bracket]
  calc
    1 = (ENNReal.ofReal U)⁻¹ * ENNReal.ofReal U :=
      (ENNReal.inv_mul_cancel hu0 ENNReal.ofReal_ne_top).symm
    _ ≤ (ENNReal.ofReal U)⁻¹ * ν (thinShell x r δ) := mul_le_mul_right hν _
    _ = (ENNReal.ofReal U)⁻¹ * (∫⁻ z, (thinShell x r δ).indicator 1 z ∂ν) := by
      rw [lintegral_indicator_one (measurableSet_thinShell x r δ)]
    _ ≤ _ := by
      apply mul_le_mul_right
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ thinShell x r δ
      · rw [indicator_of_mem hz]
        exact bad_cap_bracket S ν hr hρ hρ1 hδ hδρ hT hU hz hS (hbad z hz)
      · rw [indicator_of_notMem hz]
        exact bot_le

/-- Full radius-independent shell concentration, with explicit absolute constants. -/
theorem shell_concentration (ν S : Measure ℂ) [IsFiniteMeasure ν] [IsFiniteMeasure S]
    {ρ δ T U : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 < δ)
    (hδρ : δ ≤ ρ ^ 2 / 1600) (hT : 0 ≤ T) (hU : 0 < U) :
    ∃ E : Set ℂ, MeasurableSet E ∧
      volume E ≤
        (ENNReal.ofReal U)⁻¹ ^ 2 * (ENNReal.ofReal (156 * δ / ρ) * ν univ * ν univ) +
        (ENNReal.ofReal U)⁻¹ * ((ENNReal.ofReal (6 * Real.pi) *
          ENNReal.ofReal (2 * (200 * δ / ρ ^ 2) * (1 + T / U))) * ν univ) ∧
      ∀ x ∉ E, ∀ r ∈ Icc (1 : ℝ) 2,
        ENNReal.ofReal U ≤ ν (thinShell x r δ) →
        S (Metric.ball x (r - δ)) ≤ ENNReal.ofReal T →
        ∃ z ∈ thinShell x r δ,
          (S + ν) (thinShell x r δ \ Metric.ball z ρ) ≤ ENNReal.ofReal (2 * U) := by
  let E : Set ℂ := {x | 1 ≤ shellMajorant ν S ρ δ T U x}
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (measurable_shellMajorant ν S ρ δ T U)
  refine ⟨E, hE, ?_, ?_⟩
  · have hm := meas_ge_le_lintegral_div (μ := (volume : Measure ℂ))
      (measurable_shellMajorant ν S ρ δ T U).aemeasurable one_ne_zero ENNReal.one_ne_top
    simp only [div_one] at hm
    refine hm.trans (lintegral_shellMajorant ν S hρ hδ.le ?_ hT hU)
    have hρsq : ρ ^ 2 ≤ 1 := by nlinarith
    linarith
  · intro x hx r hr hν hS
    by_contra h
    push Not at h
    exact hx (one_le_majorant_of_no_cap ν S hρ hρ1 hδ hδρ hT hU hr hν hS h)

end DiskGeometry

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff

noncomputable section

namespace DiskMoments

attribute [local instance] OAI.DiskMoments.instFactEqNatFinrankRealComplexOfNat_solutions
lemma rotation_apply (t : ℝ) (z : ℂ) :
    rotation t z = ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I) * z := by
  simp only [rotation, Complex.rotation, Real.Angle.coe_toCircle, Real.Angle.cos_coe, Real.Angle.sin_coe]

lemma rotation_zero (z : ℂ) : rotation 0 z = z := by simp [rotation_apply]

lemma rotation_norm (t : ℝ) (z : ℂ) : ‖rotation t z‖ = ‖z‖ :=
  (rotation t).norm_map z

lemma integral_rotation (g : ℂ → ℝ) (x : ℂ) (r t : ℝ) :
    (∫ z in Metric.ball 0 r, g (x + rotation t z)) =
      ∫ z in Metric.ball 0 r, g (x + z) := by
  have hpre : (rotation t) ⁻¹' Metric.ball (0 : ℂ) r = Metric.ball 0 r := by
    ext z
    simp [Metric.mem_ball, dist_zero_right]
  have h := (rotation t).measurePreserving.setIntegral_preimage_emb
    (rotation t).toHomeomorph.measurableEmbedding (fun z => g (x + z)) (Metric.ball 0 r)
  rw [hpre] at h
  exact h

lemma hasDerivAt_rotation (t : ℝ) (z : ℂ) :
    HasDerivAt (fun a : ℝ => rotation a z) (Complex.I * rotation t z) t := by
  simp only [rotation_apply]
  convert! (((Real.hasDerivAt_cos t).ofReal_comp.add
    ((Real.hasDerivAt_sin t).ofReal_comp.mul_const Complex.I )).mul_const z) using 1; try rfl
  simp only [Complex.ofReal_neg]
  ring_nf
  simp [sub_eq_add_neg]

/-- The circulation moment of a smooth gradient on a disk vanishes. -/
theorem rotational_moment_zero {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (x : ℂ) (r : ℝ) :
    (∫ z in Metric.ball 0 r, (fderiv ℝ g (x + z)) (Complex.I * z)) = 0 := by
  let F : ℝ → ℂ → ℝ := fun t z => g (x + rotation t z)
  let F' : ℝ → ℂ → ℝ := fun t z =>
    (fderiv ℝ g (x + rotation t z)) (Complex.I * rotation t z)
  have hdc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn hdc.continuousOn
  have hFm (t : ℝ) : Continuous (F t) := hg.continuous.comp (by fun_prop)
  have hF'm (t : ℝ) : Continuous (F' t) := by
    unfold F'
    exact (hdc.comp (by fun_prop)).clm_apply (by fun_prop)
  have hFi : IntegrableOn (F 0) (Metric.ball 0 r) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 r) (hFm 0).continuousOn).mono_set
      Metric.ball_subset_closedBall
  have hdiff (z : ℂ) (t : ℝ) : HasDerivAt (fun t => F t z) (F' t z) t := by
    exact ((hg.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_rotation t z).const_add x))
  have hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) r), ∀ t ∈ (univ : Set ℝ),
      ‖F' t z‖ ≤ max C 0 * r := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz t _
    have hz' : ‖z‖ ≤ r := by simpa [Metric.mem_ball, dist_zero_right] using (show ‖z‖ < r by simpa [Metric.mem_ball, dist_zero_right] using hz).le
    have hpos : x + rotation t z ∈ Metric.closedBall x r := by
      simpa [Metric.mem_closedBall, dist_eq_norm, rotation_norm] using hz'
    exact ((fderiv ℝ g (x + rotation t z)).le_opNorm _).trans
      (mul_le_mul ((hC _ hpos).trans (le_max_left _ _))
        (by simpa [norm_mul, rotation_norm] using hz') (norm_nonneg _) (le_max_right _ _))
  have hb : IntegrableOn (fun _ : ℂ => max C 0 * r) (Metric.ball 0 r) := by
    exact integrableOn_const (by finiteness)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Metric.ball (0 : ℂ) r))
    (x₀ := (0 : ℝ)) (s := univ) (F := F) (F' := F') (bound := fun _ => max C 0 * r)
    Filter.univ_mem (Filter.Eventually.of_forall (fun t => (hFm t).aestronglyMeasurable))
    hFi (hF'm 0).aestronglyMeasurable hbound hb
    (Filter.Eventually.of_forall (fun z t _ => hdiff z t))).2
  have hconst : (fun t => ∫ z in Metric.ball 0 r, F t z) =
      fun _ => ∫ z in Metric.ball 0 r, g (x + z) := by
    funext t
    exact integral_rotation g x r t
  rw [hconst] at hd
  have he := hd.unique (hasDerivAt_const 0 (∫ z in Metric.ball 0 r, g (x + z)))
  simpa only [F', rotation_zero] using he

lemma integral_translate_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (x : ℂ) (r : ℝ) :
    (∫ z in Metric.ball 0 r, f (x + z)) = ∫ y in Metric.ball x r, f y := by
  have hpre : (fun z : ℂ => x + z) ⁻¹' Metric.ball x r = Metric.ball 0 r := by
    ext z
    simp [Metric.mem_ball, dist_eq_norm]
  have h := (measurePreserving_add_left volume x).setIntegral_preimage_emb
    (Homeomorph.addLeft x).measurableEmbedding f (Metric.ball x r)
  rwa [hpre] at h

lemma continuous_gradient {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (gradient g) :=
  (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp (hg.continuous_fderiv one_ne_zero)

lemma real_moment_integrand (g : ℂ → ℝ) (x z : ℂ) :
    (star z * gradient g x).re = (fderiv ℝ g x) z := by
  rw [← inner_gradient_left, Complex.inner]
  simp [mul_comm]

lemma imaginary_moment_integrand (g : ℂ → ℝ) (x z : ℂ) :
    (star z * gradient g x).im = (fderiv ℝ g x) (Complex.I * z) := by
  rw [← inner_gradient_left, Complex.inner]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- The imaginary part of the actual complex disk moment is zero. -/
theorem imaginary_moment_zero {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (x : ℂ) (r : ℝ) :
    (∫ y in Metric.ball x r, star (y - x) * gradient g y).im = 0 := by
  have ht := (integral_translate_ball (fun y => star (y-x) * gradient g y) x r).symm
  rw [ht]
  have hi : IntegrableOn (fun z => star ((x+z)-x) * gradient g (x+z)) (Metric.ball 0 r) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 r)
      ((by fun_prop : Continuous (fun z : ℂ => star ((x+z)-x))).mul
        ((continuous_gradient hg).comp (by fun_prop))).continuousOn).mono_set
      Metric.ball_subset_closedBall
  change Complex.imCLM (∫ z in Metric.ball 0 r, star ((x+z)-x) * gradient g (x+z)) = 0
  rw [← Complex.imCLM.integral_comp_comm hi]
  convert rotational_moment_zero hg x r using 1
  congr 1
  funext z
  simpa using imaginary_moment_integrand g (x+z) z

/-- Differentiate a disk average on its fixed unit-disk model. -/
theorem hasDerivAt_integral_unitDisk {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (x : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ z in Metric.ball (0 : ℂ) 1, g (x + s • z))
      (∫ z in Metric.ball (0 : ℂ) 1, (fderiv ℝ g (x + t • z)) z) t := by
  let F : ℝ → ℂ → ℝ := fun s z => g (x + s • z)
  let F' : ℝ → ℂ → ℝ := fun s z => (fderiv ℝ g (x + s • z)) z
  have hdc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := (isCompact_closedBall x (|t|+1)).exists_bound_of_continuousOn hdc.continuousOn
  have hFm (s : ℝ) : Continuous (F s) := hg.continuous.comp (by fun_prop)
  have hF'm (s : ℝ) : Continuous (F' s) := by
    unfold F'
    exact (hdc.comp (by fun_prop)).clm_apply continuous_id
  have hFi : IntegrableOn (F t) (Metric.ball 0 1) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 1) (hFm t).continuousOn).mono_set
      Metric.ball_subset_closedBall
  have hdiff (z : ℂ) (s : ℝ) : HasDerivAt (fun s => F s z) (F' s z) s := by
    convert! ((hg.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp_hasDerivAt s
        (((hasDerivAt_id s).smul_const z).const_add x)) using 1
    simp [F', id_eq]
  have hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1),
      ∀ s ∈ Metric.ball t 1, ‖F' s z‖ ≤ max C 0 := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz s hs
    have hz' : ‖z‖ ≤ 1 := by simpa [Metric.mem_ball, dist_zero_right] using
      (show ‖z‖ < 1 by simpa [Metric.mem_ball, dist_zero_right] using hz).le
    have hs' : |s| ≤ |t| + 1 := by
      have hh : |s-t| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hs
      have hh' := abs_add_le (s-t) t
      rw [sub_add_cancel] at hh'
      linarith
    have hpos : x + s • z ∈ Metric.closedBall x (|t|+1) := by
      simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hz' (abs_nonneg s)).trans (by simpa using hs')
    exact ((fderiv ℝ g (x+s•z)).le_opNorm _).trans
      (by simpa only [mul_one] using (mul_le_mul ((hC _ hpos).trans (le_max_left C 0)) hz'
        (norm_nonneg _) (le_max_right C 0)))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Metric.ball (0 : ℂ) 1))
    (x₀ := t) (s := Metric.ball t 1) (F := F) (F' := F') (bound := fun _ => max C 0)
    (Metric.ball_mem_nhds _ zero_lt_one) (Filter.Eventually.of_forall (fun s => (hFm s).aestronglyMeasurable))
    hFi (hF'm t).aestronglyMeasurable hbound (integrableOn_const (by finiteness))
    (Filter.Eventually.of_forall (fun z s _ => hdiff z s))).2

lemma integral_scale_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) {t : ℝ} (ht : 0 < t) :
    (∫ z in Metric.ball (0 : ℂ) 1, f (t • z)) =
      (t^2)⁻¹ • ∫ z in Metric.ball (0 : ℂ) t, f z := by
  convert Measure.setIntegral_comp_smul_of_pos volume f (Metric.ball 0 1) ht using 1
  rw [Complex.finrank_real_complex, smul_ball ht.ne', smul_zero, Real.norm_eq_abs, abs_of_pos ht, mul_one]

lemma signedAverage_fixedDomain (g : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    signedAverage g x t = (∫ z in Metric.ball (0 : ℂ) 1, g (x + t • z)) / Real.pi := by
  rw [integral_scale_ball (fun z => g (x+z)) ht, integral_translate_ball]
  simp only [signedAverage, smul_eq_mul]
  ring

lemma integral_fderiv_scale (g : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    (∫ z in Metric.ball (0 : ℂ) 1, (fderiv ℝ g (x+t•z)) z) =
      (t^3)⁻¹ * ∫ y in Metric.ball x t, (fderiv ℝ g y) (y-x) := by
  have hi (z : ℂ) : (fderiv ℝ g (x+t•z)) z =
      t⁻¹ * (fderiv ℝ g (x+t•z)) (t•z) := by
    rw [map_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
  simp_rw [hi]
  rw [integral_const_mul, integral_scale_ball (fun z => (fderiv ℝ g (x+z)) z) ht]
  have hh : (∫ z in Metric.ball (0 : ℂ) t, (fderiv ℝ g (x+z)) z) =
      ∫ y in Metric.ball x t, (fderiv ℝ g y) (y-x) := by
    simpa using integral_translate_ball (fun y => (fderiv ℝ g y) (y-x)) x t
  rw [hh]
  simp only [smul_eq_mul]
  ring

lemma integral_fderiv_moment_real {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ) (t : ℝ) :
    (∫ y in Metric.ball x t, (fderiv ℝ g y) (y-x)) =
      (∫ y in Metric.ball x t, star (y-x) * gradient g y).re := by
  have hi : IntegrableOn (fun y => star (y-x) * gradient g y) (Metric.ball x t) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall x t)
      ((by fun_prop : Continuous (fun y : ℂ => star (y-x))).mul
        (continuous_gradient hg)).continuousOn).mono_set Metric.ball_subset_closedBall
  change _ = Complex.reCLM _
  rw [← Complex.reCLM.integral_comp_comm hi]
  congr 1
  funext y
  exact (real_moment_integrand g y (y-x)).symm

/-- The radial disk derivative is the real part of its complex moment. -/
theorem hasDerivAt_signedAverage {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (x : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (signedAverage g x)
      ((∫ y in Metric.ball x t, star (y-x) * gradient g y).re / (Real.pi * t^3)) t := by
  have hd := (hasDerivAt_integral_unitDisk hg x t).div_const Real.pi
  rw [integral_fderiv_scale g x ht, integral_fderiv_moment_real hg x t] at hd
  have he : (fun s => (∫ z in Metric.ball (0 : ℂ) 1, g (x+s•z)) / Real.pi)
      =ᶠ[𝓝 t] signedAverage g x := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact (signedAverage_fixedDomain g x hs).symm
  convert! hd.congr_of_eventuallyEq he.symm using 1; try rfl
  ring

lemma ball_ae_closedBall (x : ℂ) (r : ℝ) :
    Metric.ball x r =ᵐ[volume] Metric.closedBall x r := by
  apply ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall
  · exact (Measure.addHaar_closedBall_eq_addHaar_ball volume x r).le
  · exact measurableSet_ball.nullMeasurableSet
  · exact measure_closedBall_lt_top.ne

lemma continuous_integral_fderiv_unit {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ) :
    Continuous (fun t : ℝ => ∫ z in Metric.ball (0 : ℂ) 1, (fderiv ℝ g (x+t•z)) z) := by
  have he (t : ℝ) : (∫ z in Metric.ball (0 : ℂ) 1, (fderiv ℝ g (x+t•z)) z) =
      ∫ z in Metric.closedBall (0 : ℂ) 1, (fderiv ℝ g (x+t•z)) z :=
    setIntegral_congr_set (ball_ae_closedBall 0 1)
  simp_rw [he]
  apply continuous_parametric_integral_of_continuous _ (isCompact_closedBall 0 1)
  exact ((hg.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply continuous_snd

end DiskMoments

open MeasureTheory Set Filter
open scoped Topology Interval NNReal

noncomputable section
namespace DiskKernels

lemma tail_nonneg {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (u : ℝ) :
    0 ≤ tail k u := integral_nonneg k.nonneg

lemma tail_le_one {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (u : ℝ) :
    tail k u ≤ 1 := by
  rw [← k.integral_one]
  exact setIntegral_le_integral k.integrable (Eventually.of_forall k.nonneg)

lemma tail_one {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) {u : ℝ} (hu : u < a) :
    tail k u = 1 := by
  rw [tail, setIntegral_eq_integral_of_forall_compl_eq_zero, k.integral_one]
  intro t ht
  apply k.support
  simp only [mem_Ioi, not_lt] at ht
  intro h
  linarith [h.1]

lemma tail_zero {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) {u : ℝ} (hu : b ≤ u) :
    tail k u = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  apply k.support
  intro h
  have := ht
  simp only [mem_Ioi] at this
  linarith [h.2]

lemma tail_lipschitz {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) :
    LipschitzWith M (tail k) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [Real.dist_eq, ← Real.norm_eq_abs, tail, tail,
    intervalIntegral.integral_Ioi_sub_Ioi' k.integrable.integrableOn k.integrable.integrableOn]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := u) (b := v) (f := k) (C := (M : ℝ)) (fun t _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (k.nonneg t)]
      exact k.bound t)
  simpa only [Real.dist_eq, abs_sub_comm v u] using h

lemma kernel_lipschitz {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x : ℂ) :
    LipschitzWith M (kernel k x) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  exact ((tail_lipschitz k).dist_le_mul (dist y x) (dist z x)).trans
    (mul_le_mul_of_nonneg_left (dist_dist_dist_le_left y z x) M.coe_nonneg)

lemma kernel_one {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x : ℂ)
    {y : ℂ} (hy : y ∈ Metric.ball x a) : kernel k x y = 1 := tail_one k hy

lemma kernel_zero {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x : ℂ)
    {y : ℂ} (hy : y ∉ Metric.ball x b) : kernel k x y = 0 :=
  tail_zero k (not_lt.mp hy)

/-- Two oppositely signed moments admit an explicit convex zero. -/
lemma convex_zero {A B : ℝ} (hA : 0 ≤ A) (hB : B ≤ 0) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ w*A+(1-w)*B = 0 := by
  by_cases h : A-B=0
  · refine ⟨1, zero_le_one, le_rfl, ?_⟩
    have : A = 0 := by linarith
    simp [this]
  · have hp : 0 < A-B := lt_of_le_of_ne (by linarith) (Ne.symm h)
    refine ⟨-B/(A-B), div_nonneg (neg_nonneg.mpr hB) hp.le, ?_, ?_⟩
    · apply (div_le_one hp).mpr
      linarith
    · field_simp
      ring

/-- Fubini identifies a radial kernel pairing with the average of disk pairings. -/
theorem kernel_pairing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x : ℂ)
    {f : ℂ → E} (hf : Integrable f) :
    (∫ y, kernel k x y • f y) = ∫ t, k t • ∫ y in Metric.ball x t, f y := by
  let A : Set (ℝ × ℂ) := {p | dist p.2 x < p.1}
  have hA : MeasurableSet A := measurableSet_lt (by fun_prop) measurable_fst
  let F : ℝ × ℂ → E := A.indicator (fun p => k p.1 • f p.2)
  have hF : Integrable F (volume.prod volume) := (k.integrable.smul_prod hf).indicator hA
  have hleft (t : ℝ) : (∫ y, F (t,y)) = k t • ∫ y in Metric.ball x t, f y := by
    have he : (fun y => F (t,y)) = fun y => k t • (Metric.ball x t).indicator f y := by
      funext y
      by_cases h : dist y x < t
      · simp [F, A, Metric.mem_ball, h]
      · simp [F, A, Metric.mem_ball, h]
    rw [he, integral_smul, integral_indicator measurableSet_ball]
  have hright (y : ℂ) : (∫ t, F (t,y)) = kernel k x y • f y := by
    have he : (fun t => F (t,y)) = fun t => (Ioi (dist y x)).indicator k t • f y := by
      funext t
      by_cases h : dist y x < t
      · simp [F, A, h]
      · simp [F, A, h]
    rw [he, integral_smul_const, integral_indicator measurableSet_Ioi]
    rfl
  have hh := integral_integral_swap (f := fun t y => F (t,y)) hF
  simp_rw [hleft, hright] at hh
  exact hh.symm

end DiskKernels

namespace DiskMoments
open DiskKernels

lemma continuous_radialDerivative {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ) :
    Continuous (radialDerivative g x) := (continuous_integral_fderiv_unit hg x).div_const Real.pi

lemma moment_coefficient {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ)
    {t : ℝ} (ht : 0 < t) : (moment g x t).re / (Real.pi * t^3) = radialDerivative g x t := by
  rw [radialDerivative, integral_fderiv_scale g x ht, integral_fderiv_moment_real hg]
  simp only [moment]
  ring

lemma hasDerivAt_signedAverage_fixed {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (x : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (signedAverage g x) (radialDerivative g x t) t := by
  rw [← moment_coefficient hg x ht]
  exact hasDerivAt_signedAverage hg x ht

lemma moment_eq {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ)
    {t : ℝ} (ht : 0 < t) :
    moment g x t = ((Real.pi * t^3 * radialDerivative g x t : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    have hh := moment_coefficient hg x ht
    have hp : Real.pi * t^3 ≠ 0 := mul_ne_zero Real.pi_ne_zero (pow_ne_zero 3 ht.ne')
    exact (div_eq_iff hp).mp hh |>.trans (mul_comm _ _)
  · simpa only [moment, Complex.ofReal_im] using imaginary_moment_zero hg x t

lemma integral_radialDerivative {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in Icc a b, radialDerivative g x t) = signedAverage g x b - signedAverage g x a := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ ((continuous_radialDerivative hg x).intervalIntegrable a b)
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact hasDerivAt_signedAverage_fixed hg x (lt_of_lt_of_le ha ht.1)

lemma cubeDensity_moment_integrable {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ)
    {a b : ℝ} (ha : 0 < a) :
    Integrable (fun t => cubeDensity a b t • moment g x t) := by
  have he : (fun t => cubeDensity a b t • moment g x t) =
      (Icc a b).indicator (fun t =>
        (((Real.pi / cubeMass a b) * radialDerivative g x t : ℝ) : ℂ)) := by
    funext t
    by_cases ht : t ∈ Icc a b
    · have ht0 := lt_of_lt_of_le ha ht.1
      rw [cubeDensity, Set.indicator_of_mem ht, Set.indicator_of_mem ht, moment_eq hg x ht0]
      apply Complex.ext <;> simp only [Complex.smul_re, Complex.smul_im, Complex.ofReal_re,
        Complex.ofReal_im, smul_eq_mul, mul_zero]
      simp only [inverseCube]
      field_simp
    · simp [cubeDensity, Set.indicator_of_notMem ht]
  rw [he]
  exact (Complex.continuous_ofReal.comp ((continuous_radialDerivative hg x).const_mul _)).continuousOn.integrableOn_Icc.integrable_indicator measurableSet_Icc

lemma cubeDensity_moment_integral {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t, cubeDensity a b t • moment g x t) =
      (((Real.pi / cubeMass a b) * (signedAverage g x b - signedAverage g x a) : ℝ) : ℂ) := by
  have he : (fun t => cubeDensity a b t • moment g x t) =
      (Icc a b).indicator (fun t =>
        (((Real.pi / cubeMass a b) * radialDerivative g x t : ℝ) : ℂ)) := by
    funext t
    by_cases ht : t ∈ Icc a b
    · have ht0 := lt_of_lt_of_le ha ht.1
      rw [cubeDensity, Set.indicator_of_mem ht, Set.indicator_of_mem ht, moment_eq hg x ht0]
      apply Complex.ext <;> simp only [Complex.smul_re, Complex.smul_im, Complex.ofReal_re,
        Complex.ofReal_im, smul_eq_mul, mul_zero]
      simp only [inverseCube]
      field_simp
    · simp [cubeDensity, Set.indicator_of_notMem ht]
  rw [he, integral_indicator measurableSet_Icc]
  change (∫ t in Icc a b, Complex.ofRealCLM ((Real.pi / cubeMass a b) * radialDerivative g x t)) = _
  rw [Complex.ofRealCLM.integral_comp_comm
    ((continuous_radialDerivative hg x).const_mul _).continuousOn.integrableOn_Icc,
    integral_const_mul, integral_radialDerivative hg x ha hab]
  rfl

end DiskMoments

namespace DiskKernels

/-- Only integrability over the largest supporting disk is required. -/
theorem kernel_pairing_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x : ℂ)
    {f : ℂ → E} (hf : IntegrableOn f (Metric.ball x b)) :
    (∫ y, kernel k x y • f y) = ∫ t, k t • ∫ y in Metric.ball x t, f y := by
  have hh := kernel_pairing k x (hf.integrable_indicator measurableSet_ball)
  have hleft : (fun y => kernel k x y • (Metric.ball x b).indicator f y) =
      fun y => kernel k x y • f y := by
    funext y
    by_cases hy : y ∈ Metric.ball x b
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, kernel_zero k x hy, zero_smul, zero_smul]
  rw [hleft] at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Icc a b
  · congr 1
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    exact Set.indicator_of_mem (show y ∈ Metric.ball x b from lt_of_lt_of_le hy ht.2) f
  · rw [k.support t ht, zero_smul, zero_smul]

end DiskKernels

namespace DiskMoments
open DiskKernels

/-- A faithful balanced disk-mixture kernel, with an explicit absolute bound. -/
theorem balanced_kernel {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ)
    {r δ : ℝ} (hr : r ∈ Icc (1 : ℝ) 2) (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hm : signedAverage g x (r-δ) ≤ signedAverage g x r)
    (hp : signedAverage g x (r+δ) ≤ signedAverage g x r) :
    ∃ k : RadiusDensity (r-δ) (r+δ) ⟨216/δ, by positivity⟩,
      (∫ y, kernel k x y • (star (y-x) * gradient g y)) = 0 := by
  have ha : (1 : ℝ)/2 ≤ r-δ := by linarith [hr.1]
  have hb : r+δ ≤ (3 : ℝ) := by linarith [hr.2]
  have hrh : (1 : ℝ)/2 ≤ r := by linarith [hr.1]
  have hrb : r ≤ (3 : ℝ) := by linarith [hr.2]
  have hmr : r-δ < r := by linarith
  have hpr : r < r+δ := by linarith
  let km : RadiusDensity (r-δ) (r+δ) ⟨216/δ, by positivity⟩ :=
    enlarge (inverseCubeDensity (r-δ) r ha hrb hmr) le_rfl hpr.le (by
      change 216/(r-(r-δ)) ≤ 216/δ
      simp)
  let kp : RadiusDensity (r-δ) (r+δ) ⟨216/δ, by positivity⟩ :=
    enlarge (inverseCubeDensity r (r+δ) hrh hb hpr) hmr.le le_rfl (by
      change 216/(r+δ-r) ≤ 216/δ
      simp)
  let A := Real.pi / cubeMass (r-δ) r * (signedAverage g x r - signedAverage g x (r-δ))
  let B := Real.pi / cubeMass r (r+δ) * (signedAverage g x (r+δ) - signedAverage g x r)
  have hA : 0 ≤ A := mul_nonneg (div_nonneg Real.pi_pos.le (cubeMass_pos ha hrb hmr).le)
    (sub_nonneg.mpr hm)
  have hB : B ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg Real.pi_pos.le (cubeMass_pos hrh hb hpr).le) (sub_nonpos.mpr hp)
  obtain ⟨w, hw0, hw1, hw⟩ := convex_zero hA hB
  let k := mix km kp w hw0 hw1
  refine ⟨k, ?_⟩
  have hfi : IntegrableOn (fun y => star (y-x) * gradient g y) (Metric.ball x (r+δ)) :=
    (((by fun_prop : Continuous (fun y : ℂ => star (y-x))).mul (continuous_gradient hg)).continuousOn.integrableOn_compact (isCompact_closedBall x (r+δ))).mono_set Metric.ball_subset_closedBall
  rw [kernel_pairing_local k x hfi]
  change (∫ t, (w * cubeDensity (r-δ) r t + (1-w) * cubeDensity r (r+δ) t) • moment g x t) = 0
  simp_rw [add_smul, mul_smul]
  have him : Integrable (fun t : ℝ => w • (cubeDensity (r-δ) r t • moment g x t)) := by
    convert! (cubeDensity_moment_integrable hg x (a := r-δ) (b := r) (by linarith [ha])).smul w
  have hip : Integrable (fun t : ℝ => (1-w) • (cubeDensity r (r+δ) t • moment g x t)) := by
    convert! (cubeDensity_moment_integrable hg x (a := r) (b := r+δ) (by linarith [hr.1])).smul (1-w)
  rw [integral_add him hip,
    integral_smul, integral_smul,
    cubeDensity_moment_integral hg x (by linarith [ha]) hmr.le,
    cubeDensity_moment_integral hg x (by linarith [hr.1]) hpr.le]
  change w • (A : ℂ) + (1-w) • (B : ℂ) = 0
  apply Complex.ext <;> simp only [Complex.smul_re, Complex.smul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.zero_re, Complex.zero_im,
    smul_eq_mul, mul_zero, add_zero]
  exact hw

end DiskMoments

end
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Cancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal

noncomputable section

namespace LocalCancellation

lemma integrable_lip_mul {b F : ℂ → ℂ} (hb : Integrable b)
    {L : ℝ≥0} (hF : LipschitzWith L F) (z : ℂ) {s : ℝ}
    (hsupp : ∀ᵐ y, b y ≠ 0 → ‖y-z‖ ≤ s) : Integrable (fun y => F y * b y) := by
  have hbound : ∀ᵐ y, ‖(F y - F z) * b y‖ ≤ ((L : ℝ) * s) * ‖b y‖ := by
    filter_upwards [hsupp] with y hy
    by_cases hby : b y = 0
    · simp [hby]
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        ((hF.norm_sub_le y z).trans (mul_le_mul_of_nonneg_left (hy hby) L.coe_nonneg))
        (norm_nonneg _)
  have hdiff : Integrable (fun y => (F y - F z) * b y) :=
    (hb.norm.smul ((L : ℝ) * s)).mono'
      ((hF.continuous.sub continuous_const).aestronglyMeasurable.mul hb.aestronglyMeasurable) hbound
  have h := hdiff.add (hb.const_mul (F z))
  change Integrable (fun y => (F y-F z)*b y + F z * b y) at h
  simpa only [← add_mul, sub_add_cancel] using h

/-- Cancellation against the actual integrable complex error density. -/
lemma lip_cancellation {b F : ℂ → ℂ} (hb : Integrable b) (hzero : ∫ y, b y = 0)
    {L : ℝ≥0} (hF : LipschitzWith L F) (z : ℂ) {s : ℝ}
    (hsupp : ∀ᵐ y, b y ≠ 0 → ‖y-z‖ ≤ s) :
    ‖∫ y, F y * b y‖ ≤ (L : ℝ) * s * ∫ y, ‖b y‖ := by
  have hprod := integrable_lip_mul hb hF z hsupp
  have he : (∫ y, (F y - F z) * b y) = ∫ y, F y * b y := by
    simp_rw [sub_mul]
    rw [integral_sub hprod (hb.const_mul (F z)), integral_const_mul, hzero, mul_zero, sub_zero]
  rw [← he]
  calc
    ‖∫ y, (F y-F z) * b y‖ ≤ ∫ y, ((L : ℝ) * s) * ‖b y‖ := by
      apply norm_integral_le_of_norm_le (hb.norm.smul ((L : ℝ) * s))
      filter_upwards [hsupp] with y hy
      by_cases hby : b y = 0
      · simp [hby]
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          ((hF.norm_sub_le y z).trans (mul_le_mul_of_nonneg_left (hy hby) L.coe_nonneg))
          (norm_nonneg _)
    _ = (L : ℝ) * s * ∫ y, ‖b y‖ := integral_const_mul _ _

lemma bounded_pairing {b F : ℂ → ℂ} (hb : Integrable b) {M : ℝ}
    (hF : ∀ y, ‖F y‖ ≤ M) : ‖∫ y, F y * b y‖ ≤ M * ∫ y, ‖b y‖ := by
  calc
    ‖∫ y, F y * b y‖ ≤ ∫ y, M * ‖b y‖ := by
      apply norm_integral_le_of_norm_le (hb.norm.const_mul M)
      exact Eventually.of_forall (fun y => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hF y) (norm_nonneg _))
    _ = M * ∫ y, ‖b y‖ := integral_const_mul _ _

lemma min_one_le_rpow {a α : ℝ} (ha : 0 ≤ a) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    min 1 a ≤ a ^ α := by
  by_cases ha1 : a ≤ 1
  · rw [min_eq_right ha1]
    by_cases hz : a = 0
    · rw [hz]
      exact Real.rpow_nonneg (by norm_num) _
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne ha (Ne.symm hz)) ha1 hα1
  · rw [min_eq_left (le_of_not_ge ha1)]
    exact Real.one_le_rpow (le_of_not_ge ha1) hα0

lemma ErrorPiece.mass_nonneg {Cs : ℝ} (b : ErrorPiece Cs) : 0 ≤ b.mass :=
  integral_nonneg (fun _ => norm_nonneg _)

/-- The single-piece interpolation discount, with no smoothness assumed on the density. -/
lemma piece_discount {Cs α δ C : ℝ} (b : ErrorPiece Cs)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : 1 ≤ C) {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hLC : (L : ℝ) * Cs ≤ C / δ) :
    ‖∫ y, F y * b.density y‖ ≤ C * (b.size / δ) ^ α * b.mass := by
  have hr : ‖∫ y, F y * b.density y‖ ≤ b.mass := by
    convert! bounded_pairing b.integrable hFb using 1
    simp only [one_mul, ErrorPiece.mass]
  have hCm : 0 ≤ C * b.mass := mul_nonneg (by linarith) b.mass_nonneg
  have hm : ‖∫ y, F y * b.density y‖ ≤ C * min 1 (b.size/δ) * b.mass := by
    by_cases hs : b.size < 1
    · have hl := lip_cancellation b.integrable (b.zero_mass hs) hF b.center (b.support hs)
      have hl' : ‖∫ y, F y * b.density y‖ ≤ C * (b.size/δ) * b.mass := by
        have hh := mul_le_mul_of_nonneg_right hLC (mul_nonneg b.size_pos.le b.mass_nonneg)
        calc
          _ ≤ (L : ℝ) * (Cs * b.size) * b.mass := hl
          _ ≤ C * (b.size/δ) * b.mass := by convert! hh using 1 <;> ring
      have hr' : ‖∫ y, F y * b.density y‖ ≤ C * 1 * b.mass := by nlinarith [b.mass_nonneg]
      by_cases hh : 1 ≤ b.size/δ
      · simpa only [min_eq_left hh] using hr'
      · simpa only [min_eq_right (le_of_not_ge hh)] using hl'
    · have hs1 : b.size = 1 := le_antisymm b.size_le_one (le_of_not_gt hs)
      have hh : 1 ≤ b.size / δ := by rw [hs1]; exact (one_le_div hδ).mpr hδ1
      rw [min_eq_left hh]
      nlinarith [b.mass_nonneg]
  calc
    _ ≤ C * min 1 (b.size/δ) * b.mass := hm
    _ ≤ C * (b.size/δ)^α * b.mass := by
      nlinarith [mul_le_mul_of_nonneg_left
        (min_one_le_rpow (div_nonneg b.size_pos.le hδ.le) hα0 hα1) hCm]

end LocalCancellation

namespace LocalCancellation

/-- Multiplication by the position keeps a bounded-support Lipschitz test Lipschitz. -/
lemma position_lipschitz {F : ℂ → ℂ} {L M R : ℝ≥0} (hF : LipschitzWith L F)
    (hM : ∀ y, ‖F y‖ ≤ M) (x : ℂ)
    (hR : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ R) :
    LipschitzWith (R*L+M) (fun y => star (y-x) * F y) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [dist_eq_norm, dist_eq_norm]
  change ‖star (y-x)*F y - star (z-x)*F z‖ ≤ ((R : ℝ)*(L : ℝ)+(M : ℝ))*‖y-z‖
  by_cases hz : F z = 0
  · rw [hz, mul_zero, sub_zero]
    by_cases hy : F y = 0
    · simp only [hy, mul_zero, norm_zero]
      positivity
    · have hFy : ‖F y‖ ≤ (L : ℝ)*‖y-z‖ := by simpa only [hz, sub_zero] using hF.norm_sub_le y z
      rw [norm_mul, norm_star]
      have hh := mul_le_mul (hR y hy) hFy (norm_nonneg _) R.coe_nonneg
      nlinarith [mul_nonneg M.coe_nonneg (norm_nonneg (y-z))]
  · have he : star (y-x)*F y-star (z-x)*F z =
        star (z-x)*(F y-F z)+star (y-z)*F y := by
      simp only [star_sub]
      ring
    rw [he]
    calc
      _ ≤ ‖star (z-x)*(F y-F z)‖+‖star (y-z)*F y‖ := norm_add_le _ _
      _ = ‖z-x‖*‖F y-F z‖+‖y-z‖*‖F y‖ := by rw [norm_mul, norm_mul, norm_star, norm_star]
      _ ≤ (R : ℝ)*((L : ℝ)*‖y-z‖)+‖y-z‖*(M : ℝ) :=
        add_le_add (mul_le_mul (hR z hz) (hF.norm_sub_le y z) (norm_nonneg _) R.coe_nonneg)
          (mul_le_mul_of_nonneg_left (hM y) (norm_nonneg _))
      _ = _ := by ring

lemma correction_eq {x z y : ℂ} (hz : z ≠ x) :
    correction x z y = star (z-y) / star (z-x) := by
  have hzx : star (z-x) ≠ 0 := star_ne_zero.mpr (sub_ne_zero.mpr hz)
  have he : star (z-x)-star (y-x) = star (z-y) := by simp only [star_sub]; ring
  calc
    correction x z y = (star (z-x)-star (y-x))/star (z-x) := by
      rw [sub_div, div_self hzx]
      rfl
    _ = star (z-y)/star (z-x) := by rw [he]

lemma norm_correction {x z y : ℂ} (hz : z ≠ x) :
    ‖correction x z y‖ = ‖y-z‖ / ‖z-x‖ := by
  rw [correction_eq hz, norm_div, norm_star, norm_star, norm_sub_rev z y]

lemma correction_cap_bound {x z y : ℂ} {ρ : ℝ}
    (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hy : ‖y-z‖ ≤ ρ) :
    ‖correction x z y‖ ≤ 2*ρ := by
  have hzx : 0 < ‖z-x‖ := by linarith
  have hne : z ≠ x := sub_ne_zero.mp (norm_pos_iff.mp hzx)
  rw [norm_correction hne]
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hy
  apply (div_le_iff₀ hzx).mpr
  nlinarith

lemma correction_bounded {x z y : ℂ} (hz : (1 : ℝ)/2 ≤ ‖z-x‖)
    (hy : ‖y-x‖ ≤ 3) : ‖correction x z y‖ ≤ 7 := by
  have hzx : 0 < ‖z-x‖ := by linarith
  calc
    ‖correction x z y‖ ≤ 1+‖y-x‖/‖z-x‖ := by
      simpa only [correction, norm_one, norm_div, norm_star] using norm_sub_le (1 : ℂ) (star (y-x)/star (z-x))
    _ ≤ 7 := by
      have : ‖y-x‖/‖z-x‖ ≤ 6 := (div_le_iff₀ hzx).mpr (by linarith)
      linarith

/-- Global Lipschitz control of the corrected increment test. -/
lemma corrected_lipschitz {F : ℂ → ℂ} {L M R H : ℝ≥0} (hF : LipschitzWith L F)
    (hM : ∀ y, ‖F y‖ ≤ M) (x z : ℂ)
    (hR : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ R) (hH : ‖(star (z-x))⁻¹‖ ≤ H) :
    LipschitzWith (L+H*(R*L+M)) (fun y => correction x z y * F y) := by
  have hp := position_lipschitz hF hM x hR
  apply LipschitzWith.of_dist_le_mul
  intro y w
  have he : correction x z y*F y-correction x z w*F w =
      (F y-F w)-(star (z-x))⁻¹*(star (y-x)*F y-star (w-x)*F w) := by
    simp only [correction, div_eq_mul_inv]
    ring
  rw [dist_eq_norm, he, dist_eq_norm]
  calc
    _ ≤ ‖F y-F w‖+‖(star (z-x))⁻¹*(star (y-x)*F y-star (w-x)*F w)‖ := norm_sub_le _ _
    _ ≤ (L : ℝ)*‖y-w‖+(H : ℝ)*(((R : ℝ)*(L : ℝ)+(M : ℝ))*‖y-w‖) := by
      apply add_le_add (hF.norm_sub_le y w)
      rw [norm_mul]
      exact mul_le_mul hH (hp.norm_sub_le y w) (norm_nonneg _) H.coe_nonneg
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul]; ring

end LocalCancellation

namespace LocalCancellation

variable {ι : Type*} [Fintype ι]

lemma errorPrice_nonneg {Cs : ℝ} (b : ι → ErrorPiece Cs) (α : ℝ) :
    0 ≤ errorPrice b α := Finset.sum_nonneg (fun d _ =>
  mul_nonneg (Real.rpow_nonneg (b d).size_pos.le _) (b d).mass_nonneg)

lemma square_rpow {δ : ℝ} (hδ : 0 ≤ δ) (α : ℝ) :
    (δ^2)^α = δ^(2*α) := by
  rw [Real.rpow_mul hδ, Real.rpow_two]

lemma coarse_mass_mul_le {Cs α δ : ℝ} (b : ι → ErrorPiece Cs) (hα : 0 ≤ α)
    (hδ : 0 ≤ δ) :
    δ^(2*α) * (∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), (b d).mass) ≤
      errorPrice b α := by
  classical
  rw [Finset.mul_sum]
  have hp : δ^(2*α) = (δ^2)^α := (square_rpow hδ α).symm
  calc
    _ ≤ ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), (b d).size^α*(b d).mass := by
      apply Finset.sum_le_sum
      intro d hd
      rw [hp]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (sq_nonneg δ) (Finset.mem_filter.mp hd).2 hα) (b d).mass_nonneg
    _ ≤ errorPrice b α := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun d _ _ => mul_nonneg (Real.rpow_nonneg (b d).size_pos.le _) (b d).mass_nonneg)

lemma fine_size_sum_le {Cs α δ : ℝ} (b : ι → ErrorPiece Cs) (hα : α ≤ 1)
    (hδ : 0 ≤ δ) :
    (∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2), (b d).size*(b d).mass) ≤
      δ^(2*(1-α))*errorPrice b α := by
  classical
  calc
    _ ≤ ∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2),
        δ^(2*(1-α))*((b d).size^α*(b d).mass) := by
      apply Finset.sum_le_sum
      intro d hd
      have hs : (b d).size < δ^2 := (Finset.mem_filter.mp hd).2
      have he : (b d).size = (b d).size^α*(b d).size^(1-α) := by
        rw [← Real.rpow_add (b d).size_pos]
        simp
      have hh := Real.rpow_le_rpow (b d).size_pos.le hs.le (sub_nonneg.mpr hα)
      rw [square_rpow hδ] at hh
      calc
        _ = ((b d).size^α*(b d).size^(1-α))*(b d).mass := congrArg (fun v => v*(b d).mass) he
        _ = (b d).size^(1-α)*((b d).size^α*(b d).mass) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hh
          (mul_nonneg (Real.rpow_nonneg (b d).size_pos.le _) (b d).mass_nonneg)
    _ = δ^(2*(1-α)) * (∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2),
        (b d).size^α*(b d).mass) := (Finset.mul_sum ..).symm
    _ ≤ δ^(2*(1-α))*errorPrice b α := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun d _ _ => mul_nonneg (Real.rpow_nonneg (b d).size_pos.le _) (b d).mass_nonneg))
      (Real.rpow_nonneg hδ _)

lemma total_pairing_discount {Cs α δ C : ℝ} (b : ι → ErrorPiece Cs)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : 1 ≤ C) {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hLC : (L : ℝ)*Cs ≤ C/δ) :
    ‖∑ d, ∫ y, F y*(b d).density y‖ ≤ C/δ^α*errorPrice b α := by
  calc
    _ ≤ ∑ d, ‖∫ y, F y*(b d).density y‖ := norm_sum_le _ _
    _ ≤ ∑ d, C*((b d).size/δ)^α*(b d).mass := Finset.sum_le_sum
      (fun d _ => piece_discount (b d) hα0 hα1 hδ hδ1 hC hF hFb hLC)
    _ = C/δ^α*errorPrice b α := by
      rw [errorPrice, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Real.div_rpow (b d).size_pos.le hδ.le]
      ring

/-- All fine errors together retain the stronger, summable power of the width. -/
lemma fine_pairing_bound {Cs α δ : ℝ} (b : ι → ErrorPiece Cs) (hCs : 0 ≤ Cs)
    (hα : α ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) :
    ‖∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2), ∫ y, F y*(b d).density y‖ ≤
      (L : ℝ)*Cs*δ^(2*(1-α))*errorPrice b α := by
  classical
  calc
    _ ≤ ∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2), ‖∫ y, F y*(b d).density y‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2),
        (L : ℝ)*Cs*((b d).size*(b d).mass) := by
      apply Finset.sum_le_sum
      intro d hd
      have hs : (b d).size < 1 := lt_of_lt_of_le (Finset.mem_filter.mp hd).2 (by nlinarith)
      have hh := lip_cancellation (b d).integrable ((b d).zero_mass hs) hF (b d).center ((b d).support hs)
      convert! hh using 1
      dsimp only [ErrorPiece.mass]
      ring
    _ = (L : ℝ)*Cs*(∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2),
        (b d).size*(b d).mass) := (Finset.mul_sum ..).symm
    _ ≤ (L : ℝ)*Cs*(δ^(2*(1-α))*errorPrice b α) :=
      mul_le_mul_of_nonneg_left (fine_size_sum_le b hα hδ) (mul_nonneg L.coe_nonneg hCs)
    _ = _ := by ring

end LocalCancellation

open MeasureTheory Set Filter
open scoped Topology NNReal Real

noncomputable section
namespace LocalCancellation

lemma densityMeasure_apply {b : ℂ → ℂ} (hb : Integrable b) {D : Set ℂ}
    (hD : MeasurableSet D) : densityMeasure b D = ENNReal.ofReal (∫ y in D, ‖b y‖) := by
  rw [densityMeasure, withDensity_apply _ hD]
  exact (ofReal_integral_eq_lintegral_ofReal hb.integrableOn.norm
    (Eventually.of_forall (fun _ => norm_nonneg _))).symm

lemma densityMeasure_univ {b : ℂ → ℂ} (hb : Integrable b) :
    densityMeasure b univ = ENNReal.ofReal (∫ y, ‖b y‖) := by
  rw [densityMeasure_apply hb MeasurableSet.univ, Measure.restrict_univ]

lemma densityMeasure_finite {b : ℂ → ℂ} (hb : Integrable b) : IsFiniteMeasure (densityMeasure b) := by
  constructor
  rw [densityMeasure_univ hb]
  exact ENNReal.ofReal_lt_top

/-- A cap decomposition bound, with all integrals over genuine densities. -/
lemma pairing_majorant {b F : ℂ → ℂ} (hb : Integrable b) {A : Set ℂ}
    (hA : MeasurableSet A) (c d : ℝ)
    (hF : ∀ y, ‖F y‖ ≤ c + d*A.indicator (fun _ => (1 : ℝ)) y) :
    ‖∫ y, F y*b y‖ ≤ c*(∫ y, ‖b y‖)+d*(∫ y in A, ‖b y‖) := by
  have hi : Integrable (fun y => c*‖b y‖+d*A.indicator (fun y => ‖b y‖) y) :=
    (hb.norm.const_mul c).add ((hb.norm.indicator hA).const_mul d)
  calc
    _ ≤ ∫ y, c*‖b y‖+d*A.indicator (fun y => ‖b y‖) y := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards with y
      rw [norm_mul]
      have hh := mul_le_mul_of_nonneg_right (hF y) (norm_nonneg (b y))
      convert! hh using 1
      by_cases hy : y ∈ A
      · simp only [Set.indicator_of_mem hy, mul_one]
        ring
      · simp only [Set.indicator_of_notMem hy, mul_zero, add_zero]
    _ = _ := by
      rw [integral_add (hb.norm.const_mul c) ((hb.norm.indicator hA).const_mul d),
        integral_const_mul, integral_const_mul, integral_indicator hA]

end LocalCancellation

namespace LocalCancellation

lemma corrected_pairing_cap {b F : ℂ → ℂ} (hb : Integrable b) {D : Set ℂ}
    (hD : MeasurableSet D) (hFb : ∀ y, ‖F y‖ ≤ 1)
    (hFD : ∀ y, F y ≠ 0 → y ∈ D) (x z : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3) :
    ‖∫ y, correction x z y*F y*b y‖ ≤
      2*ρ*(∫ y, ‖b y‖)+7*(∫ y in D \ Metric.ball z ρ, ‖b y‖) := by
  apply pairing_majorant hb (hD.diff measurableSet_ball) (2*ρ) 7
  intro y
  by_cases hFy : F y = 0
  · simp only [hFy, mul_zero, norm_zero]
    exact add_nonneg (mul_nonneg (by norm_num) hρ)
      (mul_nonneg (by norm_num) (Set.indicator_nonneg (fun _ _ => zero_le_one) y))
  · have hyD := hFD y hFy
    by_cases hyB : y ∈ Metric.ball z ρ
    · have hc := correction_cap_bound hz (show ‖y-z‖ ≤ ρ from by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hyB).le)
      rw [Set.indicator_of_notMem (show y ∉ D \ Metric.ball z ρ from fun h => h.2 hyB), mul_zero, add_zero]
      rw [norm_mul]
      simpa only [mul_one] using mul_le_mul hc (hFb y) (norm_nonneg _) (mul_nonneg (by norm_num) hρ)
    · rw [Set.indicator_of_mem (show y ∈ D \ Metric.ball z ρ from ⟨hyD,hyB⟩), mul_one]
      have hc := correction_bounded hz (hD3 y hyD)
      rw [norm_mul]
      have hh := mul_le_mul hc (hFb y) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 7)
      nlinarith

lemma supported_pairing {b F : ℂ → ℂ} (hb : Integrable b) {D : Set ℂ}
    (hD : MeasurableSet D) (hFb : ∀ y, ‖F y‖ ≤ 1)
    (hFD : ∀ y, F y ≠ 0 → y ∈ D) :
    ‖∫ y, F y*b y‖ ≤ ∫ y in D, ‖b y‖ := by
  have hh := pairing_majorant hb hD 0 1 (show ∀ y, ‖F y‖ ≤ 0+1*D.indicator (fun _ => (1 : ℝ)) y from by
    intro y
    by_cases hy : y ∈ D
    · simpa only [Set.indicator_of_mem hy, mul_one, zero_add] using hFb y
    · have hf : F y = 0 := by by_contra h; exact hy (hFD y h)
      simp only [hf, norm_zero, Set.indicator_of_notMem hy, mul_zero, zero_add, le_refl])
  simpa only [zero_mul, one_mul, zero_add] using hh

variable {ι : Type*} [Fintype ι]

lemma coarseMass_nonneg {Cs : ℝ} (b : ι → ErrorPiece Cs) (δ : ℝ) (D : Set ℂ) :
    0 ≤ coarseMass b δ D := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))

lemma coarseMeasure_apply {Cs : ℝ} (b : ι → ErrorPiece Cs) (δ : ℝ) {D : Set ℂ}
    (hD : MeasurableSet D) : coarseMeasure b δ D = ENNReal.ofReal (coarseMass b δ D) := by
  classical
  simp only [coarseMeasure, Measure.finsetSum_apply, densityMeasure_apply (b _).integrable hD,
    coarseMass]
  rw [ENNReal.ofReal_sum_of_nonneg (fun d _ => integral_nonneg (fun _ => norm_nonneg _))]

instance coarseMeasure_finite {Cs : ℝ} (b : ι → ErrorPiece Cs) (δ : ℝ) :
    IsFiniteMeasure (coarseMeasure b δ) := by
  constructor
  rw [coarseMeasure_apply b δ MeasurableSet.univ]
  exact ENNReal.ofReal_lt_top

lemma coarseMass_univ {Cs : ℝ} (b : ι → ErrorPiece Cs) (δ : ℝ) :
    coarseMass b δ univ = ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), (b d).mass := by
  simp only [coarseMass, ErrorPiece.mass, Measure.restrict_univ]

lemma coarseMass_bound {Cs α δ : ℝ} (b : ι → ErrorPiece Cs) (hα : 0 ≤ α)
    (hδ : 0 < δ) : coarseMass b δ univ ≤ errorPrice b α / δ^(2*α) := by
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hδ _), mul_comm, coarseMass_univ]
  exact coarse_mass_mul_le b hα hδ.le

/-- The uncorrected increment costs only shell mass plus the fine-error discount. -/
lemma increment_bound {Cs α δ : ℝ} (b : ι → ErrorPiece Cs) (hCs : 0 ≤ Cs)
    (hα : α ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hFD : ∀ y, F y ≠ 0 → y ∈ D) :
    ‖∑ d, ∫ y, F y*(b d).density y‖ ≤
      coarseMass b δ D+(L : ℝ)*Cs*δ^(2*(1-α))*errorPrice b α := by
  classical
  have he : (∑ d, ∫ y, F y*(b d).density y) =
      (∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), ∫ y, F y*(b d).density y)+
      (∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2), ∫ y, F y*(b d).density y) := by
    simpa only [not_le] using (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun d => δ^2 ≤ (b d).size) (fun d => ∫ y, F y*(b d).density y)).symm
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum (fun d _ => supported_pairing (b d).integrable hD hFb hFD)
  · exact fine_pairing_bound b hCs hα hδ hδ1 hF

end LocalCancellation

namespace LocalCancellation

lemma integrable_bounded_pairing {b F : ℂ → ℂ} (hb : Integrable b)
    (hF : AEStronglyMeasurable F) {M : ℝ} (hM : ∀ y, ‖F y‖ ≤ M) :
    Integrable (fun y => F y*b y) := by
  apply (hb.norm.const_mul M).mono' (hF.mul hb.aestronglyMeasurable)
  filter_upwards with y
  change ‖F y * b y‖ ≤ M * ‖b y‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)

lemma position_bound {F : ℂ → ℂ} (hF : ∀ y, ‖F y‖ ≤ 1) (x : ℂ)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ R) :
    ∀ y, ‖star (y-x)*F y‖ ≤ R := by
  intro y
  by_cases hy : F y = 0
  · simpa only [hy, mul_zero, norm_zero] using hR0
  · rw [norm_mul, norm_star]
    simpa only [mul_one] using mul_le_mul (hR y hy) (hF y) (norm_nonneg _) hR0

end LocalCancellation

namespace DiskKernels

lemma kernel_nonneg {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x y : ℂ) :
    0 ≤ kernel k x y := tail_nonneg k _

lemma kernel_le_one {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x y : ℂ) :
    kernel k x y ≤ 1 := tail_le_one k _

lemma complex_kernel_lipschitz {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x : ℂ) :
    LipschitzWith M (fun y => (kernel k x y : ℂ)) := by
  simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitz.comp (kernel_lipschitz k x)

lemma complex_kernel_bound {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x y : ℂ) :
    ‖(kernel k x y : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg k x y)] using kernel_le_one k x y

lemma difference_bound {a b c d : ℝ} {M N : ℝ≥0}
    (k : RadiusDensity a b M) (l : RadiusDensity c d N) (x y : ℂ) :
    ‖((kernel l x y : ℂ) - kernel k x y)‖ ≤ 1 := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [kernel_nonneg k x y, kernel_nonneg l x y, kernel_le_one k x y, kernel_le_one l x y]

lemma difference_support {r δ ε : ℝ} {M N : ℝ≥0}
    (k : RadiusDensity (r-δ) (r+δ) M) (l : RadiusDensity (r-ε) (r+ε) N)
    (hεδ : ε ≤ δ) (x y : ℂ) (h : (kernel l x y : ℂ) - kernel k x y ≠ 0) :
    |‖y-x‖-r| ≤ δ := by
  by_cases hlo : ‖y-x‖ < r-δ
  · have hk : kernel k x y = 1 := kernel_one k x (by simpa only [Metric.mem_ball, dist_eq_norm] using hlo)
    have hl : kernel l x y = 1 := kernel_one l x (by
      simp only [Metric.mem_ball, dist_eq_norm]
      linarith)
    exact False.elim (h (by simp only [hk, hl, sub_self]))
  · by_cases hup : r+δ ≤ ‖y-x‖
    · have hk : kernel k x y = 0 := kernel_zero k x (by
        simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hup)
      have hl : kernel l x y = 0 := kernel_zero l x (by
        simp only [Metric.mem_ball, dist_eq_norm, not_lt]
        linarith)
      exact False.elim (h (by simp only [hk, hl, sub_self]))
    · rw [abs_le]
      constructor <;> linarith

end DiskKernels

namespace DiskKernels

/-- At every point away from the boundary circle, all such mixtures tend to
    the actual sharp disk. No convergence of the chosen radius densities is assumed. -/
lemma tendsto_kernel {r : ℝ} {δ : ℕ → ℝ} {M : ℕ → ℝ≥0}
    (k : ∀ n, RadiusDensity (r-δ n) (r+δ n) (M n))
    (hδ : Tendsto δ atTop (𝓝 0)) (x y : ℂ) (hy : ‖y-x‖ ≠ r) :
    Tendsto (fun n => kernel (k n) x y) atTop
      (𝓝 ((Metric.ball x r).indicator (fun _ => (1 : ℝ)) y)) := by
  by_cases h : ‖y-x‖ < r
  · have he : ∀ᶠ n in atTop, kernel (k n) x y = 1 := by
      filter_upwards [hδ.eventually_lt_const (sub_pos.mpr h)] with n hn
      exact kernel_one (k n) x (by
        simp only [Metric.mem_ball, dist_eq_norm]
        linarith)
    have hmem : y ∈ Metric.ball x r := by simpa only [Metric.mem_ball, dist_eq_norm] using h
    rw [indicator_of_mem hmem]
    exact tendsto_const_nhds.congr' (he.mono fun _ hn => hn.symm)
  · have hh : r < ‖y-x‖ := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hy)
    have he : ∀ᶠ n in atTop, kernel (k n) x y = 0 := by
      filter_upwards [hδ.eventually_lt_const (sub_pos.mpr hh)] with n hn
      exact kernel_zero (k n) x (by
        simp only [Metric.mem_ball, dist_eq_norm, not_lt]
        linarith)
    have hmem : y ∉ Metric.ball x r := by simpa only [Metric.mem_ball, dist_eq_norm] using h
    rw [indicator_of_notMem hmem]
    exact tendsto_const_nhds.congr' (he.mono fun _ hn => hn.symm)

/-- Dominated convergence of an arbitrary sequence of mixtures against each
    actual absolutely continuous finite vector measure. -/
lemma tendsto_kernel_pairing {r : ℝ} {δ : ℕ → ℝ} {M : ℕ → ℝ≥0}
    (k : ∀ n, RadiusDensity (r-δ n) (r+δ n) (M n))
    (hδ : Tendsto δ atTop (𝓝 0)) (x : ℂ) {b : ℂ → ℂ} (hb : Integrable b) :
    Tendsto (fun n => ∫ y, (kernel (k n) x y : ℂ)*b y) atTop
      (𝓝 (∫ y in Metric.ball x r, b y)) := by
  rw [← integral_indicator measurableSet_ball]
  apply tendsto_integral_of_dominated_convergence (fun y => ‖b y‖)
  · intro n
    exact (complex_kernel_lipschitz (k n) x).continuous.aestronglyMeasurable.mul hb.aestronglyMeasurable
  · exact hb.norm
  · intro n
    filter_upwards with y
    change ‖(kernel (k n) x y : ℂ)*b y‖ ≤ ‖b y‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (complex_kernel_bound (k n) x y)
  · have hcircle : ∀ᵐ y : ℂ, ‖y-x‖ ≠ r := by
      simpa only [Metric.mem_sphere, dist_eq_norm] using (measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume x r))
    filter_upwards [hcircle] with y hy
    have h := (Complex.continuous_ofReal.tendsto _).comp (tendsto_kernel k hδ x y hy)
    have hm := h.mul_const (b y)
    convert! hm using 1
    by_cases hmem : y ∈ Metric.ball x r
    · simp only [indicator_of_mem hmem, Complex.ofReal_one, one_mul]
    · simp only [indicator_of_notMem hmem, Complex.ofReal_zero, zero_mul]

end DiskKernels

end
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Scales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real

noncomputable section

namespace DiskScales

lemma width_le {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) : width δ n ≤ δ := by
  unfold width
  exact mul_le_of_le_one_right hδ (pow_le_one₀ (by norm_num) (by norm_num))

lemma width_succ (δ : ℝ) (n : ℕ) : width δ (n+1) = width δ n / 2 := by
  simp only [width, pow_succ]
  ring

lemma width_antitone {δ : ℝ} (hδ : 0 ≤ δ) : Antitone (width δ) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [width_succ]
  have : 0 ≤ width δ n := mul_nonneg hδ (pow_nonneg (by norm_num) _)
  linarith

lemma tendsto_width (δ : ℝ) : Tendsto (width δ) atTop (𝓝 0) := by
  change Tendsto (fun n => δ*(1/2 : ℝ)^n) atTop (𝓝 0)
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)).const_mul δ

lemma width_rpow {δ : ℝ} (hδ : 0 ≤ δ) (p : ℝ) (n : ℕ) :
    (width δ n)^p = δ^p*((1/2 : ℝ)^p)^n := by
  rw [width, Real.mul_rpow hδ (pow_nonneg (by norm_num) n)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    mul_comm (n : ℝ) p, Real.rpow_mul (by norm_num), Real.rpow_natCast]

lemma ratio_norm_lt {p : ℝ} (hp : 0 < p) : ‖(1/2 : ℝ)^p‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
  exact Real.rpow_lt_one (by norm_num) (by norm_num) hp

lemma summable_width_rpow {δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 < p) :
    Summable (fun n => (width δ n)^p) := by
  simp_rw [width_rpow hδ]
  exact (summable_geometric_of_norm_lt_one (ratio_norm_lt hp)).mul_left _

lemma tsum_width_rpow {δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 < p) :
    (∑' n, (width δ n)^p) = δ^p / (1-(1/2 : ℝ)^p) := by
  simp_rw [width_rpow hδ]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (ratio_norm_lt hp)]
  rfl

lemma scaled_increment {Cs A t δ M L : ℝ} (hCs : 0 ≤ Cs) (hA : 0 ≤ A)
    (hAt : A ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : M ≤ A*δ^(-(1/50 : ℝ))) (hL : L ≤ 648/δ) :
    2*δ^(1/5 : ℝ)*M+14*(t*δ^(1/10 : ℝ))+
      (L+2*(3*L+1))*Cs*δ^(2*(1-(1/100 : ℝ)))*A ≤
      (16+4538*Cs)*t*δ^(1/10 : ℝ) := by
  have ht : 0 ≤ t := hA.trans hAt
  have hc : L+2*(3*L+1) ≤ 4538/δ := by
    have hh : L*δ ≤ 648 := (le_div_iff₀ hδ).mp hL
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have he1 : δ^(1/5 : ℝ)*δ^(-(1/50 : ℝ)) = δ^(9/50 : ℝ) := by
    rw [← Real.rpow_add hδ]
    norm_num
  have he2 : δ⁻¹*δ^(2*(1-(1/100 : ℝ))) = δ^(49/50 : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hδ]
    norm_num
  have hb1 : δ^(9/50 : ℝ) ≤ δ^(1/10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  have hb2 : δ^(49/50 : ℝ) ≤ δ^(1/10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  have hm : 2*δ^(1/5 : ℝ)*M ≤ 2*t*δ^(1/10 : ℝ) := by
    calc
      _ ≤ 2*δ^(1/5 : ℝ)*(A*δ^(-(1/50 : ℝ))) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = 2*A*δ^(9/50 : ℝ) := by rw [← he1]; ring
      _ ≤ 2*t*δ^(1/10 : ℝ) := mul_le_mul (by linarith) hb1
        (Real.rpow_nonneg hδ.le _) (by positivity)
  have hf : (L+2*(3*L+1))*Cs*δ^(2*(1-(1/100 : ℝ)))*A ≤
      4538*Cs*t*δ^(1/10 : ℝ) := by
    calc
      _ ≤ (4538/δ)*Cs*δ^(2*(1-(1/100 : ℝ)))*A := by gcongr
      _ = 4538*Cs*A*δ^(49/50 : ℝ) := by rw [← he2]; ring
      _ ≤ 4538*Cs*t*δ^(1/10 : ℝ) := mul_le_mul (by gcongr) hb2
        (Real.rpow_nonneg hδ.le _) (by positivity)
  nlinarith

/-- A single small width works for both shell geometry and every smaller width. -/
lemma exists_admissible_width : ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1/4 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → δ ≤ (δ^(1/5 : ℝ))^2/1600 := by
  have ht : Tendsto (fun δ : ℝ => δ^(3/5 : ℝ)) (𝓝 0) (𝓝 0) := by
    simpa using (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3/5)).tendsto 0
  have hev := ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1/1600)
  obtain ⟨l,u,hu,hs⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
  let d := min (u/2) (1/4)
  have hd : 0 < d := lt_min (by linarith [hu.2]) (by norm_num)
  refine ⟨d, hd, min_le_right _ _, fun δ hδ hδd => ?_⟩
  have hdltu : d < u := lt_of_le_of_lt (min_le_left _ _) (by linarith [hu.2])
  have hp : δ^(3/5 : ℝ) < 1/1600 := hs ⟨lt_trans hu.1 hδ, lt_of_le_of_lt hδd hdltu⟩
  have he : δ = δ^(3/5 : ℝ)*(δ^(1/5 : ℝ))^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
    norm_num
  calc
    δ = δ^(3/5 : ℝ)*(δ^(1/5 : ℝ))^2 := he
    _ ≤ (δ^(1/5 : ℝ))^2/1600 :=
      (mul_le_mul_of_nonneg_right hp.le (sq_nonneg _)).trans_eq (by ring)

end DiskScales

namespace LocalCancellation
open DiskKernels DiskMoments DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

lemma moment_pairing_integrable {Cs r δ : ℝ} (b : ErrorPiece Cs)
    {M : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M) (x : ℂ) (hr : r+δ ≤ 3) :
    Integrable (fun y => star (y-x)*(kernel k x y : ℂ)*b.density y) := by
  apply integrable_bounded_pairing b.integrable
    ((by fun_prop : Continuous (fun y : ℂ => star (y-x))).mul
      (complex_kernel_lipschitz k x).continuous).aestronglyMeasurable
  apply position_bound (complex_kernel_bound k x) x (by norm_num : (0 : ℝ) ≤ 3)
  intro y hy
  have hyb : y ∈ Metric.ball x (r+δ) := by
    by_contra hh
    exact hy (by rw [kernel_zero k x hh, Complex.ofReal_zero])
  exact (show ‖y-x‖ < r+δ by simpa only [Metric.mem_ball, dist_eq_norm] using hyb).le.trans hr

end LocalCancellation

namespace DiskScales

lemma first_power_identity {δ : ℝ} (hδ : 0 < δ) :
    (δ^(1/10 : ℝ))⁻¹^2 * (δ / δ^(1/5 : ℝ) * δ^(-(1/50 : ℝ)) * δ^(-(1/50 : ℝ))) =
      δ^(14/25 : ℝ) := by
  rw [← Real.rpow_neg hδ.le, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
  have he (a : ℝ) : δ / δ^a = δ^(1-a) := by
    rw [Real.rpow_sub hδ, Real.rpow_one]
  rw [he]
  rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
  norm_num

lemma second_power_identity {δ : ℝ} (hδ : 0 < δ) :
    (δ^(1/10 : ℝ))⁻¹ * (δ / (δ^(1/5 : ℝ))^2 * δ^(-(1/50 : ℝ))) =
      δ^(12/25 : ℝ) := by
  rw [← Real.rpow_neg hδ.le, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
  have he (a : ℝ) : δ / δ^a = δ^(1-a) := by
    rw [Real.rpow_sub hδ, Real.rpow_one]
  rw [he]
  rw [← mul_assoc, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
  norm_num

end DiskScales

namespace DiskScales

lemma norm_geometric_rpow_lt {p : ℝ} (hp : 0 < p) : (1/2 : ℝ)^p < 1 :=
  Real.rpow_lt_one (by norm_num) (by norm_num) hp

lemma geometric_tail_sum {A t d : ℝ} (hA : 0 ≤ A) (ht : 0 < t) (hd : 0 ≤ d) :
    (∑' n : ℕ, ENNReal.ofReal
      (156*(A/t)^2*(width d n)^(14/25 : ℝ)+2424*Real.pi*(A/t)*(width d n)^(9/25 : ℝ))) =
    ENNReal.ofReal (156*(A/t)^2*d^(14/25 : ℝ)/(1-(1/2 : ℝ)^(14/25 : ℝ))+
      2424*Real.pi*(A/t)*d^(9/25 : ℝ)/(1-(1/2 : ℝ)^(9/25 : ℝ))) := by
  have h1 := (summable_width_rpow hd (by norm_num : (0 : ℝ) < 14/25)).mul_left (156*(A/t)^2)
  have h2 := (summable_width_rpow hd (by norm_num : (0 : ℝ) < 9/25)).mul_left (2424*Real.pi*(A/t))
  have hn (n : ℕ) : 0 ≤ width d n := mul_nonneg hd (pow_nonneg (by norm_num) n)
  have hc1 : 0 ≤ 156*(A/t)^2 := by positivity
  have hc2 : 0 ≤ 2424*Real.pi*(A/t) := by positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => add_nonneg
    (mul_nonneg hc1 (Real.rpow_nonneg (hn n) _))
    (mul_nonneg hc2 (Real.rpow_nonneg (hn n) _))) (h1.add h2),
    Summable.tsum_add h1 h2, tsum_mul_left, tsum_mul_left,
    tsum_width_rpow hd (by norm_num : (0 : ℝ) < 14/25),
    tsum_width_rpow hd (by norm_num : (0 : ℝ) < 9/25)]
  congr 1
  ring

/-- After the initial-width choice d=A/t, the failure exponents are strictly
larger than one, rather than the nonintegrable weak-(1,1) exponent. -/
lemma starting_width_tail {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    156*(A/t)^2*(A/t)^(14/25 : ℝ)/(1-(1/2 : ℝ)^(14/25 : ℝ))+
      2424*Real.pi*(A/t)*(A/t)^(9/25 : ℝ)/(1-(1/2 : ℝ)^(9/25 : ℝ)) =
    (156/(1-(1/2 : ℝ)^(14/25 : ℝ)))*(A/t)^(64/25 : ℝ)+
      (2424*Real.pi/(1-(1/2 : ℝ)^(9/25 : ℝ)))*(A/t)^(34/25 : ℝ) := by
  have hq : 0 < A/t := div_pos hA ht
  have he1 : (A/t)^2*(A/t)^(14/25 : ℝ) = (A/t)^(64/25 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hq]
    norm_num
  have he2 : (A/t)*(A/t)^(9/25 : ℝ) = (A/t)^(34/25 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one (A/t)]
    rw [← Real.rpow_add hq]
    norm_num
  calc
    _ = (156/(1-(1/2 : ℝ)^(14/25 : ℝ)))*((A/t)^2*(A/t)^(14/25 : ℝ))+
      (2424*Real.pi/(1-(1/2 : ℝ)^(9/25 : ℝ)))*((A/t)*(A/t)^(9/25 : ℝ)) := by ring
    _ = _ := by rw [he1,he2]

end DiskScales

namespace DiskScales

lemma sizeTailConstant_pos : 0 < sizeTailConstant := by
  have h1 : 0 < 1-(1/2 : ℝ)^(14/25 : ℝ) := sub_pos.mpr (norm_geometric_rpow_lt (by norm_num))
  have h2 : 0 < 1-(1/2 : ℝ)^(9/25 : ℝ) := sub_pos.mpr (norm_geometric_rpow_lt (by norm_num))
  unfold sizeTailConstant
  positivity

lemma collapse_size_tail {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    (156/(1-(1/2 : ℝ)^(14/25 : ℝ)))*q^(64/25 : ℝ)+
      (2424*Real.pi/(1-(1/2 : ℝ)^(9/25 : ℝ)))*q^(34/25 : ℝ) ≤
      sizeTailConstant*q^(34/25 : ℝ) := by
  have hc : 0 ≤ 156/(1-(1/2 : ℝ)^(14/25 : ℝ)) :=
    div_nonneg (by norm_num) (sub_nonneg.mpr ((norm_geometric_rpow_lt (by norm_num)).le))
  have he := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hq hq1 (by norm_num : (34/25 : ℝ) ≤ 64/25)) hc
  unfold sizeTailConstant
  nlinarith

end DiskScales

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.LocalPrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real

noncomputable section

namespace DyadicMajorant
variable {X : Type*} [MeasurableSpace X]

lemma measurable_price (t : ℝ) {E : ℕ → Set X} (hE : ∀ n, MeasurableSet (E n)) :
    Measurable (price t E) := by
  unfold price
  have hs : Measurable (fun x => ∑' n : ℕ, (E n).indicator (fun _ => ENNReal.ofReal (t*2^(n+1))) x) := Measurable.tsum (fun n =>
    (measurable_const : Measurable (fun _ : X => ENNReal.ofReal (t*2^(n+1)))).indicator (hE n))
  exact measurable_const.add hs

omit [MeasurableSpace X] in
lemma majorizes {t v : ℝ} (ht : 0 < t) {E : ℕ → Set X} {x : X}
    (hv : ∀ n : ℕ, x ∉ E n → v ≤ t*2^n) :
    ENNReal.ofReal v ≤ price t E x := by
  by_cases hvt : v ≤ t
  · exact (ENNReal.ofReal_le_ofReal hvt).trans le_self_add
  · have he : ∃ n : ℕ, v ≤ t*2^n := by
      obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (v/t) (by norm_num : (1 : ℝ) < 2)
      exact ⟨n, le_of_lt ((div_lt_iff₀ ht).mp hn |> fun h => by simpa only [mul_comm] using h)⟩
    let n := Nat.find he
    have hn : v ≤ t*2^n := Nat.find_spec he
    have hn0 : n ≠ 0 := by
      intro hz
      have : v ≤ t := by simpa only [hz, pow_zero, mul_one] using hn
      exact hvt this
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hjn : j < n := by omega
    have hmem : x ∈ E j := by
      by_contra h
      exact Nat.find_min he hjn (hv j h)
    have hp : ENNReal.ofReal (t*2^(j+1)) ≤ price t E x := by
      have hs := ENNReal.le_tsum j (f := fun n : ℕ => (E n).indicator (fun _ => ENNReal.ofReal (t*2^(n+1))) x)
      rw [indicator_of_mem hmem] at hs
      exact hs.trans le_add_self
    apply le_trans (ENNReal.ofReal_le_ofReal hn)
    simpa only [hj, Nat.succ_eq_add_one] using hp

lemma lintegral_price (μ : Measure X) {Q : Set X}
    (t : ℝ) {E : ℕ → Set X} (hE : ∀ n, MeasurableSet (E n)) :
    (∫⁻ x in Q, price t E x ∂μ) ≤
      ENNReal.ofReal t*μ Q + ∑' n : ℕ, ENNReal.ofReal (t*2^(n+1))*μ (E n) := by
  simp only [price]
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ,
    lintegral_tsum (fun n => (measurable_const.indicator (hE n)).aemeasurable)]
  apply add_le_add le_rfl
  apply ENNReal.tsum_le_tsum
  intro n
  rw [lintegral_indicator (hE n), lintegral_const, Measure.restrict_apply_univ,
    Measure.restrict_apply (hE n)]
  exact mul_le_mul_right (measure_mono inter_subset_left) _

end DyadicMajorant

namespace DyadicMajorant

lemma weighted_geometric_sum {t K c : ℝ} (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hc : 0 ≤ c) (hc1 : 2*c < 1) :
    (∑' n : ℕ, ENNReal.ofReal (t*2^(n+1))*ENNReal.ofReal (K*c^n)) =
      ENNReal.ofReal (2*t*K/(1-2*c)) := by
  have he (n : ℕ) : ENNReal.ofReal (t*2^(n+1))*ENNReal.ofReal (K*c^n) =
      ENNReal.ofReal (2*t*K*(2*c)^n) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_pow, pow_succ]
    ring
  simp_rw [he]
  have hc' : ‖2*c‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hc1
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    ((summable_geometric_of_norm_lt_one hc').mul_left (2*t*K)),
    tsum_mul_left, tsum_geometric_of_norm_lt_one hc']
  rfl

variable {X : Type*} [MeasurableSpace X]

lemma lintegral_price_geometric (μ : Measure X) {Q : Set X} {q t K c : ℝ}
    (hq : 0 ≤ q) (hQ : μ Q ≤ ENNReal.ofReal q) (ht : 0 ≤ t)
    (hK : 0 ≤ K) (hc : 0 ≤ c) (hc1 : 2*c < 1)
    {E : ℕ → Set X} (hE : ∀ n, MeasurableSet (E n))
    (hEv : ∀ n : ℕ, μ (E n) ≤ ENNReal.ofReal (K*c^n)) :
    (∫⁻ x in Q, price t E x ∂μ) ≤
      ENNReal.ofReal (t*(q+2*K/(1-2*c))) := by
  apply (lintegral_price μ t hE).trans
  calc
    _ ≤ ENNReal.ofReal t*ENNReal.ofReal q+
        ∑' n : ℕ, ENNReal.ofReal (t*2^(n+1))*ENNReal.ofReal (K*c^n) :=
      add_le_add (mul_le_mul_right hQ _) (ENNReal.tsum_le_tsum fun n => mul_le_mul_right (hEv n) _)
    _ = ENNReal.ofReal (t*q)+ENNReal.ofReal (2*t*K/(1-2*c)) := by
      rw [← ENNReal.ofReal_mul ht, weighted_geometric_sum ht hK hc hc1]
    _ = _ := by
      rw [← ENNReal.ofReal_add (mul_nonneg ht hq) (by positivity [sub_pos.mpr hc1])]
      congr 1
      ring

end DyadicMajorant

namespace LocalCancellation
open DiskScales DiskMoments

lemma errorPrice_zero {ι : Type*} [Fintype ι] {Cs α : ℝ} (b : ι → ErrorPiece Cs)
    (hA : errorPrice b α = 0) : ∀ j, (b j).density =ᵐ[volume] 0 := by
  intro j
  have hterm : (b j).size^α*(b j).mass ≤ errorPrice b α :=
    Finset.single_le_sum (fun k _ => mul_nonneg (Real.rpow_nonneg (b k).size_pos.le _) (b k).mass_nonneg) (Finset.mem_univ j)
  have hm : (b j).mass = 0 := by
    have hp := Real.rpow_pos_of_pos (b j).size_pos α
    rw [hA] at hterm
    nlinarith [(b j).mass_nonneg]
  have hz := (integral_eq_zero_iff_of_nonneg (fun y => norm_nonneg ((b j).density y)) (b j).integrable.norm).mp hm
  filter_upwards [hz] with y hy
  exact norm_eq_zero.mp hy

lemma dyadic_ratio {A L : ℝ} (hA : 0 < A) (hL : 1 ≤ L) (n : ℕ) :
    A/(L*A*2^n) ≤ (1/2 : ℝ)^n := by
  have hLA : 0 < L*A := mul_pos (by linarith) hA
  have hn : 0 < (2 : ℝ)^n := by positivity
  calc
    _ ≤ (L*A)/(L*A*2^n) := div_le_div_of_nonneg_right (le_mul_of_one_le_left hA.le hL) (mul_nonneg hLA.le hn.le)
    _ = (1/2 : ℝ)^n := by rw [div_pow]; field_simp; simp

end LocalCancellation

namespace LocalCancellation
open DiskKernels DiskGeometry

lemma inner_unit_bound {e p : ℂ} (he : ‖e‖ = 1) : |inner ℝ e p| ≤ ‖p‖ := by
  simpa only [he,one_mul] using abs_real_inner_le_norm e p

lemma negative_projection_change (e p q : ℂ) (he : ‖e‖ = 1) :
    max 0 (-inner ℝ e q) ≤ max 0 (-inner ℝ e p)+‖q-p‖ := by
  have h := inner_unit_bound (p := q-p) he
  rw [inner_sub_right] at h
  apply max_le
  · positivity
  · have hh := neg_le_abs (inner ℝ e q-inner ℝ e p)
    have hm := le_max_right (0 : ℝ) (-inner ℝ e p)
    linarith

lemma cone_pairing {e : ℂ} {κ : ℝ} (a : ConeDensity e κ)
    {K : ℂ → ℝ} (hK : AEStronglyMeasurable K) (hK0 : ∀ y, 0 ≤ K y)
    (hK1 : ∀ y, K y ≤ 1) :
    κ*(∫ y, K y*‖a.density y‖) ≤ inner ℝ e (∫ y, (K y : ℂ)*a.density y) := by
  have hKn (y : ℂ) : ‖K y‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (hK0 y)]; exact hK1 y
  have hi : Integrable (fun y => K y*‖a.density y‖) := a.integrable.norm.bdd_mul hK (ae_of_all _ hKn)
  have hia : Integrable (fun y => (K y : ℂ)*a.density y) :=
    a.integrable.bdd_mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hK)
      (ae_of_all _ (fun y => by simpa only [Complex.norm_real] using hKn y))
  rw [← integral_const_mul, ← integral_inner hia e]
  apply integral_mono_ae (hi.const_mul κ) ((innerSL ℝ e).integrable_comp hia)
  filter_upwards [a.cone] with y hy
  change κ*(K y*‖a.density y‖) ≤ inner ℝ e ((K y : ℂ)*a.density y)
  rw [← Complex.real_smul, inner_smul_right]
  nlinarith [mul_le_mul_of_nonneg_left hy (hK0 y)]

/-- Nonpositive total projection bounds the weighted good mass by the error. -/
lemma cone_mass_of_nonpositive {e : ℂ} {κ : ℝ} (a : ConeDensity e κ)
    (he : ‖e‖ = 1) (hκ : 0 < κ) {K : ℂ → ℝ} (hK : AEStronglyMeasurable K)
    (hK0 : ∀ y, 0 ≤ K y) (hK1 : ∀ y, K y ≤ 1) {p : ℂ}
    (hp : inner ℝ e ((∫ y, (K y : ℂ)*a.density y)+p) ≤ 0) :
    (∫ y, K y*‖a.density y‖) ≤ ‖p‖/κ := by
  apply (le_div_iff₀ hκ).mpr
  have hh := cone_pairing a hK hK0 hK1
  have hb := inner_unit_bound (p := p) he
  rw [inner_add_right] at hp
  have hn := neg_le_abs (inner ℝ e p)
  nlinarith

/-- Crossing the zero projection selects a genuine convex kernel, not an
arbitrary discontinuous truncation. -/
lemma crossing_interpolation (e p q : ℂ) (hq : inner ℝ e q < 0) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      inner ℝ e (θ • p+(1-θ) • q) ≤ 0 ∧
      max 0 (-inner ℝ e (θ • p+(1-θ) • q)) = max 0 (-inner ℝ e p) := by
  by_cases hp : inner ℝ e p ≤ 0
  · refine ⟨1,zero_le_one,le_rfl,?_,?_⟩
    · simpa using hp
    · simp
  · obtain ⟨θ,hθ0,hθ1,hzero⟩ := convex_zero (le_of_not_ge hp) hq.le
    refine ⟨θ,hθ0,hθ1,?_,?_⟩
    · simp only [inner_add_right, inner_smul_right, hzero, le_refl]
    · rw [inner_add_right, inner_smul_right, inner_smul_right, hzero,
        neg_zero, max_self, max_eq_left (by linarith : -inner ℝ e p ≤ 0)]

/-- The cap cost of the good density is weighted interior mass, not its
possibly enormous total mass. -/
lemma cone_corrected_cap {a : ℂ → ℂ} (ha : Integrable a)
    {K L : ℂ → ℝ} (hK : AEStronglyMeasurable K) (hL : AEStronglyMeasurable L)
    (hK0 : ∀ y, 0 ≤ K y) (hK1 : ∀ y, K y ≤ 1)
    (hL0 : ∀ y, 0 ≤ L y) (hL1 : ∀ y, L y ≤ 1)
    {D : Set ℂ} (hD : MeasurableSet D) (hsupp : ∀ y, L y-K y ≠ 0 → y ∈ D)
    (x z : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hz : (1 : ℝ)/2 ≤ ‖z-x‖)
    (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3) :
    ‖∫ y, correction x z y*((L y : ℂ)-K y)*a y‖ ≤
      2*ρ*(∫ y, (L y+K y)*‖a y‖)+7*(∫ y in D \ Metric.ball z ρ, ‖a y‖) := by
  have hi : Integrable (fun y => (L y+K y)*‖a y‖) :=
    ha.norm.bdd_mul (c := 2) (hL.add hK) (ae_of_all _ (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (hL0 y) (hK0 y))]
      linarith [hK1 y,hL1 y]))
  let B := D \ Metric.ball z ρ
  have hB : MeasurableSet B := hD.diff measurableSet_ball
  have hbi : Integrable (B.indicator (fun y => ‖a y‖)) := ha.norm.indicator hB
  have hmaj : ‖∫ y, correction x z y*((L y : ℂ)-K y)*a y‖ ≤
      ∫ y, 2*ρ*((L y+K y)*‖a y‖)+7*B.indicator (fun y => ‖a y‖) y := by
    apply norm_integral_le_of_norm_le ((hi.const_mul _).add (hbi.const_mul _))
    filter_upwards with y
    change ‖correction x z y*((L y : ℂ)-K y)*a y‖ ≤ 2*ρ*((L y+K y)*‖a y‖)+7*B.indicator (fun y => ‖a y‖) y
    have hk := hK0 y
    have hl := hL0 y
    have hb : 0 ≤ B.indicator (fun y => ‖a y‖) y := Set.indicator_nonneg (fun _ _ => norm_nonneg _) y
    have hf : ‖((L y : ℂ)-K y)‖ = |L y-K y| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hsum : |L y-K y| ≤ L y+K y := abs_le.mpr ⟨by linarith [hL0 y], by linarith [hK0 y]⟩
    have hone : |L y-K y| ≤ 1 := abs_le.mpr ⟨by linarith [hL0 y,hK1 y],by linarith [hL1 y,hK0 y]⟩
    by_cases hzero : L y-K y = 0
    · have hc : (L y : ℂ)-K y = 0 := by exact_mod_cast hzero
      rw [hc, mul_zero, zero_mul, norm_zero]
      positivity
    · have hyD := hsupp y hzero
      by_cases hyB : y ∈ Metric.ball z ρ
      · have hc := correction_cap_bound hz (show ‖y-z‖ ≤ ρ from by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hyB).le)
        rw [indicator_of_notMem (show y ∉ B from fun h => h.2 hyB), mul_zero, add_zero,
          norm_mul, norm_mul, hf]
        have hh := mul_le_mul hc hsum (abs_nonneg _) (by positivity : 0 ≤ 2*ρ)
        nlinarith [mul_le_mul_of_nonneg_right hh (norm_nonneg (a y))]
      · rw [indicator_of_mem (show y ∈ B from ⟨hyD,hyB⟩),norm_mul,norm_mul,hf]
        have hc := mul_le_mul (correction_bounded hz (hD3 y hyD)) hone (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 7)
        have hh := mul_le_mul_of_nonneg_right hc (norm_nonneg (a y))
        have hn : 0 ≤ 2*ρ*((L y+K y)*‖a y‖) := by positivity
        nlinarith
  rw [integral_add (hi.const_mul _) (hbi.const_mul _), integral_const_mul,
    integral_const_mul, integral_indicator hB] at hmaj
  exact hmaj

end LocalCancellation

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

/-- The error contribution to the corrected first active step; no moment
cancellation for the errors alone is presumed. -/
lemma corrected_error_bound {Cs α δ ρ : ℝ} (b : ι → ErrorPiece Cs) (hCs : 0 ≤ Cs)
    (hα : α ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hρ : 0 ≤ ρ)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hFD : ∀ y, F y ≠ 0 → y ∈ D) (x z : ℂ)
    (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3) :
    ‖∑ d, ∫ y, correction x z y*F y*(b d).density y‖ ≤
      2*ρ*coarseMass b δ univ+7*coarseMass b δ (D \ Metric.ball z ρ)+
      ((L : ℝ)+2*(3*(L : ℝ)+1))*Cs*δ^(2*(1-α))*errorPrice b α := by
  classical
  have hnorm : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ (3 : ℝ) := fun y hy => hD3 y (hFD y hy)
  have hH : ‖(star (z-x))⁻¹‖ ≤ (2 : ℝ) := by
    rw [norm_inv, norm_star]
    have hn : 0 < ‖z-x‖ := by linarith
    rw [inv_eq_one_div, div_le_iff₀ hn]
    linarith
  have hcorr : LipschitzWith (L+2*(3*L+1)) (fun y => correction x z y*F y) :=
    corrected_lipschitz (M := 1) (R := 3) (H := 2) hF hFb x z hnorm hH
  have hsplit : (∑ d, ∫ y, correction x z y*F y*(b d).density y) =
      (∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), ∫ y, correction x z y*F y*(b d).density y)+
      (∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2), ∫ y, correction x z y*F y*(b d).density y) := by
    simpa only [not_le] using (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun d => δ^2 ≤ (b d).size) (fun d => ∫ y, correction x z y*F y*(b d).density y)).symm
  rw [hsplit]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      _ ≤ ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size),
          ‖∫ y, correction x z y*F y*(b d).density y‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size),
          (2*ρ*(∫ y, ‖(b d).density y‖)+7*(∫ y in D \ Metric.ball z ρ, ‖(b d).density y‖)) :=
        Finset.sum_le_sum (fun d _ => corrected_pairing_cap (b d).integrable hD hFb hFD x z hρ hz hD3)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        simp only [coarseMass, Measure.restrict_univ]
  · exact fine_pairing_bound b hCs hα hδ hδ1 hcorr

end LocalCancellation

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

lemma increment_bound_general {Cs α δ M : ℝ} (b : ι → ErrorPiece Cs) (hCs : 0 ≤ Cs)
    (hα : α ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ M) (hFD : ∀ y, F y ≠ 0 → y ∈ D) :
    ‖∑ d, ∫ y, F y*(b d).density y‖ ≤
      M*coarseMass b δ D+(L : ℝ)*Cs*δ^(2*(1-α))*errorPrice b α := by
  classical
  have he : (∑ d, ∫ y, F y*(b d).density y) =
      (∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), ∫ y, F y*(b d).density y)+
      (∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2), ∫ y, F y*(b d).density y) := by
    simpa only [not_le] using (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun d => δ^2 ≤ (b d).size) (fun d => ∫ y, F y*(b d).density y)).symm
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      _ ≤ ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), ‖∫ y, F y*(b d).density y‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), M*(∫ y in D, ‖(b d).density y‖) := by
        apply Finset.sum_le_sum
        intro d _
        have hh := pairing_majorant (b d).integrable hD 0 M (fun y => by
          by_cases hy : y ∈ D
          · simpa only [indicator_of_mem hy, mul_one, zero_add] using hFb y
          · have hf : F y = 0 := by by_contra h; exact hy (hFD y h)
            simp only [hf,norm_zero,indicator_of_notMem hy,mul_zero,add_zero,le_refl])
        simpa only [zero_mul,zero_add] using hh
      _ = _ := by rw [← Finset.mul_sum]; rfl
  · exact fine_pairing_bound b hCs hα hδ hδ1 hF

lemma correction_kernel_bound {F : ℂ → ℂ} (hFb : ∀ y, ‖F y‖ ≤ 1)
    (x z : ℂ) (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hD3 : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ 3) :
    ∀ y, ‖correction x z y*F y‖ ≤ 7 := by
  intro y
  by_cases hy : F y = 0
  · simp only [hy,mul_zero,norm_zero]; norm_num
  · rw [norm_mul]
    simpa only [mul_one] using mul_le_mul (correction_bounded hz (hD3 y hy)) (hFb y) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 7)

lemma corrected_inactive_bound {Cs α δ : ℝ} (b : ι → ErrorPiece Cs) (hCs : 0 ≤ Cs)
    (hα : α ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hFD : ∀ y, F y ≠ 0 → y ∈ D) (x z : ℂ)
    (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3) :
    ‖∑ d, ∫ y, correction x z y*F y*(b d).density y‖ ≤
      7*coarseMass b δ D+((L : ℝ)+2*(3*(L : ℝ)+1))*Cs*δ^(2*(1-α))*errorPrice b α := by
  have hnorm : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ (3 : ℝ) := fun y hy => hD3 y (hFD y hy)
  have hH : ‖(star (z-x))⁻¹‖ ≤ (2 : ℝ) := by
    rw [norm_inv, norm_star]
    have hn : 0 < ‖z-x‖ := by linarith
    rw [inv_eq_one_div, div_le_iff₀ hn]
    linarith
  have hcorr : LipschitzWith (L+2*(3*L+1)) (fun y => correction x z y*F y) :=
    corrected_lipschitz (M := 1) (R := 3) (H := 2) hF hFb x z hnorm hH
  exact increment_bound_general b hCs hα hδ hδ1 hcorr hD (correction_kernel_bound hFb x z hz hnorm)
    (fun y hy => hFD y (fun h => hy (by rw [h,mul_zero])))

end LocalCancellation

/-- A finite last-active-index induction. Its hypotheses are local gaps, not
an assumed global estimate, and no infinite list of active indices is chosen. -/
lemma last_active_bound (active : ℕ → Prop) (N a : ℕ → ℝ) (B : ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hfirst : ∀ n, (∀ i < n, ¬active i) → N n ≤ B+∑ i ∈ Finset.range n, a i)
    (hgap : ∀ j n, j < n → active j → (∀ i, j < i → i < n → ¬active i) →
      N n ≤ N j+a j) : ∀ n, N n ≤ B+∑ i ∈ Finset.range n, a i := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let S := (Finset.range n).filter active
    by_cases hS : S.Nonempty
    · let j := S.max' hS
      have hjmem : j ∈ S := Finset.max'_mem S hS
      have hjn : j < n := Finset.mem_range.mp (Finset.mem_filter.mp hjmem).1
      have hjact : active j := (Finset.mem_filter.mp hjmem).2
      have hng : ∀ i, j < i → i < n → ¬active i := by
        intro i hji hin hi
        have his : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hin,hi⟩
        exact (not_lt_of_ge (Finset.le_max' S i his)) hji
      have hh := hgap j n hjn hjact hng
      have hb := ih j hjn
      have hs : (∑ i ∈ Finset.range (j+1), a i) ≤ ∑ i ∈ Finset.range n, a i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_of_lt hjn)) (fun i _ _ => ha i)
      rw [Finset.sum_range_succ] at hs
      linarith
    · apply hfirst n
      intro i hi hai
      exact hS ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hai⟩⟩

lemma last_active_limit (active : ℕ → Prop) (N a : ℕ → ℝ) (B Z : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsm : Summable a) (hN : Tendsto N atTop (𝓝 Z))
    (hfirst : ∀ n, (∀ i < n, ¬active i) → N n ≤ B+∑ i ∈ Finset.range n, a i)
    (hgap : ∀ j n, j < n → active j → (∀ i, j < i → i < n → ¬active i) →
      N n ≤ N j+a j) : Z ≤ B+∑' i, a i := by
  apply le_of_tendsto hN
  filter_upwards with n
  exact (last_active_bound active N a B ha hfirst hgap n).trans
    (add_le_add le_rfl (hsm.sum_le_tsum (Finset.range n) (fun i _ => ha i)))

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales

lemma real_weight_integrable {a : ℂ → ℂ} (ha : Integrable a) {K : ℂ → ℝ}
    (hK : AEStronglyMeasurable K) (hK0 : ∀ y, 0 ≤ K y) (hK1 : ∀ y, K y ≤ 1) :
    Integrable (fun y => (K y : ℂ)*a y) :=
  integrable_bounded_pairing ha (Complex.continuous_ofReal.comp_aestronglyMeasurable hK)
    (fun y => by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hK0 y)]; exact hK1 y)

lemma real_weight_norm_integrable {a : ℂ → ℂ} (ha : Integrable a) {K : ℂ → ℝ}
    (hK : AEStronglyMeasurable K) (hK0 : ∀ y, 0 ≤ K y) (hK1 : ∀ y, K y ≤ 1) :
    Integrable (fun y => K y*‖a y‖) :=
  ha.norm.bdd_mul hK (ae_of_all _ fun y => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hK0 y)]; exact hK1 y)

lemma convex_pairing {a : ℂ → ℂ} {K L : ℂ → ℝ}
    (hiK : Integrable (fun y => (K y : ℂ)*a y))
    (hiL : Integrable (fun y => (L y : ℂ)*a y)) (θ : ℝ) :
    (∫ y, ((θ*K y+(1-θ)*L y : ℝ) : ℂ)*a y) =
      θ • (∫ y, (K y : ℂ)*a y)+(1-θ) • (∫ y, (L y : ℂ)*a y) := by
  have he : (fun y => ((θ*K y+(1-θ)*L y : ℝ) : ℂ)*a y) =
      (fun y => θ • ((K y : ℂ)*a y)+(1-θ) • ((L y : ℂ)*a y)) := by
    ext y
    simp only [Complex.ofReal_add,Complex.ofReal_mul,Complex.real_smul]
    ring
  rw [he]
  calc
    _ = (∫ y, θ • ((K y : ℂ)*a y))+(∫ y, (1-θ) • ((L y : ℂ)*a y)) :=
      integral_add (hiK.smul θ) (hiL.smul (1-θ))
    _ = _ := by rw [integral_smul,integral_smul]

/-- Analytic comparison of two balanced mixtures at a negative later
projection. The only error term is their fixed-correction difference. -/
lemma negative_gap_cap {e : ℂ} {κ B ρ H : ℝ} (a : ConeDensity e κ)
    (he : ‖e‖ = 1) (hκ : 0 < κ) (hρ : 0 ≤ ρ)
    {K L : ℂ → ℝ} (hK : AEStronglyMeasurable K) (hL : AEStronglyMeasurable L)
    (hK0 : ∀ y, 0 ≤ K y) (hK1 : ∀ y, K y ≤ 1)
    (hL0 : ∀ y, 0 ≤ L y) (hL1 : ∀ y, L y ≤ 1)
    {D : Set ℂ} (hD : MeasurableSet D) (hsupp : ∀ y, L y-K y ≠ 0 → y ∈ D)
    (x z : ℂ) (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3)
    (hcap : (∫ y in D \ Metric.ball z ρ, ‖a.density y‖) ≤ H)
    {p q R : ℂ} (hp : ‖p‖ ≤ B) (hq : ‖q‖ ≤ B)
    (hneg : inner ℝ e ((∫ y, (L y : ℂ)*a.density y)+q) < 0)
    (hcor : ((∫ y, (L y : ℂ)*a.density y)+q)-((∫ y, (K y : ℂ)*a.density y)+p) =
      (∫ y, correction x z y*((L y : ℂ)-K y)*a.density y)+R) :
    max 0 (-inner ℝ e ((∫ y, (L y : ℂ)*a.density y)+q)) ≤
      max 0 (-inner ℝ e ((∫ y, (K y : ℂ)*a.density y)+p))+
        4*ρ*(B/κ)+7*H+‖R‖ := by
  let P := (∫ y, (K y : ℂ)*a.density y)+p
  let Q := (∫ y, (L y : ℂ)*a.density y)+q
  obtain ⟨θ,hθ0,hθ1,hθneg,hθeq⟩ := crossing_interpolation e P Q hneg
  let J (y : ℂ) := θ*K y+(1-θ)*L y
  have hJ0 (y : ℂ) : 0 ≤ J y := add_nonneg (mul_nonneg hθ0 (hK0 y)) (mul_nonneg (sub_nonneg.mpr hθ1) (hL0 y))
  have hJ1 (y : ℂ) : J y ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left (hK1 y) hθ0
    have h2 := mul_le_mul_of_nonneg_left (hL1 y) (sub_nonneg.mpr hθ1)
    dsimp [J]
    nlinarith
  have hJ : AEStronglyMeasurable J := (hK.const_mul θ).add (hL.const_mul (1-θ))
  have hiK := real_weight_integrable a.integrable hK hK0 hK1
  have hiL := real_weight_integrable a.integrable hL hL0 hL1
  let pstar := θ • p+(1-θ) • q
  have hpstar : ‖pstar‖ ≤ B := by
    calc
      ‖pstar‖ ≤ ‖θ • p‖+‖(1-θ) • q‖ := norm_add_le _ _
      _ = θ*‖p‖+(1-θ)*‖q‖ := by
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
          abs_of_nonneg hθ0,abs_of_nonneg (sub_nonneg.mpr hθ1)]
      _ ≤ θ*B+(1-θ)*B := add_le_add (mul_le_mul_of_nonneg_left hp hθ0)
        (mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hθ1))
      _ = B := by ring
  have hstar : (∫ y, (J y : ℂ)*a.density y)+pstar = θ • P+(1-θ) • Q := by
    rw [show (∫ y, (J y : ℂ)*a.density y) = _ from convex_pairing hiK hiL θ]
    dsimp [P,Q,pstar]
    ring
  have hsmass := cone_mass_of_nonpositive a he hκ hJ hJ0 hJ1
    (show inner ℝ e ((∫ y, (J y : ℂ)*a.density y)+pstar) ≤ 0 by rw [hstar]; exact hθneg)
  have hlmass := cone_mass_of_nonpositive a he hκ hL hL0 hL1 hneg.le
  have hweighted : (∫ y, (L y+J y)*‖a.density y‖) ≤ 2*(B/κ) := by
    have hiLn := real_weight_norm_integrable a.integrable hL hL0 hL1
    have hiJn := real_weight_norm_integrable a.integrable hJ hJ0 hJ1
    simp_rw [add_mul]
    rw [integral_add hiLn hiJn]
    have hs := hsmass.trans (div_le_div_of_nonneg_right hpstar hκ.le)
    have hl := hlmass.trans (div_le_div_of_nonneg_right hq hκ.le)
    linarith
  have hJdiff (y : ℂ) : L y-J y = θ*(L y-K y) := by dsimp [J]; ring
  have hJDs : ∀ y, L y-J y ≠ 0 → y ∈ D := by
    intro y hy
    apply hsupp y
    intro h
    exact hy (by rw [hJdiff,h,mul_zero])
  let G := ∫ y, correction x z y*((L y : ℂ)-J y)*a.density y
  have hG : ‖G‖ ≤ 4*ρ*(B/κ)+7*H := by
    have hh := cone_corrected_cap a.integrable hJ hL hJ0 hJ1 hL0 hL1 hD hJDs x z hρ hz hD3
    change ‖G‖ ≤ _ at hh
    have hg := mul_le_mul_of_nonneg_left hweighted (by positivity : 0 ≤ 2*ρ)
    have hc := mul_le_mul_of_nonneg_left hcap (by norm_num : (0 : ℝ) ≤ 7)
    nlinarith
  have hGid : G = θ • (∫ y, correction x z y*((L y : ℂ)-K y)*a.density y) := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards with y
    change correction x z y*((L y : ℂ)-(θ*K y+(1-θ)*L y : ℝ))*a.density y =
      θ • (correction x z y*((L y : ℂ)-K y)*a.density y)
    simp only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one,Complex.real_smul]
    ring
  have hdiff : Q-(θ • P+(1-θ) • Q) = G+θ • R := by
    have hh : Q-P = (∫ y, correction x z y*((L y : ℂ)-K y)*a.density y)+R := hcor
    rw [hGid, ← smul_add, ← hh]
    simp only [sub_smul,one_smul,smul_sub]
    abel
  have hR : ‖θ • R‖ ≤ ‖R‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hθ0]
    exact mul_le_of_le_one_left (norm_nonneg _) hθ1
  have hn := negative_projection_change e (θ • P+(1-θ) • Q) Q he
  rw [hθeq,hdiff] at hn
  have hh := (norm_add_le G (θ • R)).trans (add_le_add hG hR)
  change max 0 (-inner ℝ e Q) ≤ max 0 (-inner ℝ e P)+4*ρ*(B/κ)+7*H+‖R‖
  linarith

end LocalCancellation

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales

lemma cone_negative_le_error {e : ℂ} {κ : ℝ} (a : ConeDensity e κ)
    (he : ‖e‖ = 1) (hκ : 0 ≤ κ) {K : ℂ → ℝ}
    (hK : AEStronglyMeasurable K) (hK0 : ∀ y, 0 ≤ K y) (hK1 : ∀ y, K y ≤ 1) (p : ℂ) :
    max 0 (-inner ℝ e ((∫ y, (K y : ℂ)*a.density y)+p)) ≤ ‖p‖ := by
  have hh := cone_pairing a hK hK0 hK1
  have hi : 0 ≤ ∫ y, K y*‖a.density y‖ := integral_nonneg (fun y => mul_nonneg (hK0 y) (norm_nonneg _))
  have hproj : 0 ≤ inner ℝ e (∫ y, (K y : ℂ)*a.density y) := (mul_nonneg hκ hi).trans hh
  rw [inner_add_right]
  exact max_le (norm_nonneg _) (by linarith [(abs_le.mp (inner_unit_bound (p := p) he)).1])

lemma general_moment_integrable {a : ℂ → ℂ} (ha : Integrable a)
    {r δ : ℝ} {M : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M) (x : ℂ) (hr : r+δ ≤ 3) :
    Integrable (fun y => star (y-x)*(kernel k x y : ℂ)*a y) := by
  apply integrable_bounded_pairing ha
    ((by fun_prop : Continuous (fun y : ℂ => star (y-x))).mul
      (complex_kernel_lipschitz k x).continuous).aestronglyMeasurable
  apply position_bound (complex_kernel_bound k x) x (by norm_num : (0 : ℝ) ≤ 3)
  intro y hy
  have hyb : y ∈ Metric.ball x (r+δ) := by
    by_contra hh
    exact hy (by rw [kernel_zero k x hh, Complex.ofReal_zero])
  exact (show ‖y-x‖ < r+δ by simpa only [Metric.mem_ball, dist_eq_norm] using hyb).le.trans hr

lemma correcting_pairing {a F : ℂ → ℂ} (ha : Integrable a)
    (hF : AEStronglyMeasurable F) (hFb : ∀ y, ‖F y‖ ≤ 1) (x z : ℂ)
    (hsupp : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ 3) :
    (∫ y, correction x z y*F y*a y) = (∫ y, F y*a y) -
      (star (z-x))⁻¹*(∫ y, star (y-x)*F y*a y) := by
  have hi := integrable_bounded_pairing ha hF hFb
  have him : Integrable (fun y => star (y-x)*F y*a y) :=
    integrable_bounded_pairing ha
      ((by fun_prop : Continuous (fun y : ℂ => star (y-x))).aestronglyMeasurable.mul hF)
      (position_bound hFb x (by norm_num : (0 : ℝ) ≤ 3) hsupp)
  have he : (fun y => correction x z y*F y*a y) =
      fun y => F y*a y-(star (z-x))⁻¹*(star (y-x)*F y*a y) := by
    ext y
    simp only [correction,div_eq_mul_inv]
    ring
  rw [he,integral_sub hi (him.const_mul _),integral_const_mul]

lemma general_kernel_pairing_sub {a : ℂ → ℂ} (ha : Integrable a)
    {u v u' v' : ℝ} {M N : ℝ≥0} (k : RadiusDensity u v M) (l : RadiusDensity u' v' N) (x : ℂ) :
    (∫ y, (kernel l x y : ℂ)*a y)-(∫ y, (kernel k x y : ℂ)*a y) =
      ∫ y, ((kernel l x y : ℂ)-kernel k x y)*a y := by
  rw [← integral_sub
    (integrable_bounded_pairing ha (complex_kernel_lipschitz l x).continuous.aestronglyMeasurable (complex_kernel_bound l x))
    (integrable_bounded_pairing ha (complex_kernel_lipschitz k x).continuous.aestronglyMeasurable (complex_kernel_bound k x))]
  congr 1
  ext y
  ring

lemma corrected_kernel_integrable {a : ℂ → ℂ} (ha : Integrable a)
    {r δ : ℝ} {M : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M) (x z : ℂ)
    (hr : r+δ ≤ 3) (hz : (1 : ℝ)/2 ≤ ‖z-x‖) :
    Integrable (fun y => correction x z y*(kernel k x y : ℂ)*a y) := by
  apply integrable_bounded_pairing ha
    ((by unfold correction; fun_prop : Continuous (correction x z)).mul (complex_kernel_lipschitz k x).continuous).aestronglyMeasurable
  apply correction_kernel_bound (complex_kernel_bound k x) x z hz
  intro y hy
  have hyb : y ∈ Metric.ball x (r+δ) := by
    by_contra hh
    exact hy (by rw [kernel_zero k x hh,Complex.ofReal_zero])
  exact (show ‖y-x‖ < r+δ by simpa only [Metric.mem_ball,dist_eq_norm] using hyb).le.trans hr

lemma corrected_kernel_pairing_sub {a : ℂ → ℂ} (ha : Integrable a)
    {r δ ε : ℝ} {M N : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M)
    (l : RadiusDensity (r-ε) (r+ε) N) (x z : ℂ)
    (hrδ : r+δ ≤ 3) (hrε : r+ε ≤ 3) (hz : (1 : ℝ)/2 ≤ ‖z-x‖) :
    (∫ y, correction x z y*(kernel l x y : ℂ)*a y)-
      (∫ y, correction x z y*(kernel k x y : ℂ)*a y) =
      ∫ y, correction x z y*((kernel l x y : ℂ)-kernel k x y)*a y := by
  rw [← integral_sub (corrected_kernel_integrable ha l x z hrε hz)
    (corrected_kernel_integrable ha k x z hrδ hz)]
  congr 1
  ext y
  ring

lemma interior_mass_le_kernel {a : ℂ → ℂ} (ha : Integrable a)
    {r δ ε : ℝ} {M : ℝ≥0} (k : RadiusDensity (r-ε) (r+ε) M) (x : ℂ) (hεδ : ε ≤ δ) :
    (∫ y in Metric.ball x (r-δ), ‖a y‖) ≤ ∫ y, kernel k x y*‖a y‖ := by
  rw [← integral_indicator measurableSet_ball]
  apply integral_mono_ae (ha.norm.indicator measurableSet_ball)
    (ha.norm.bdd_mul (kernel_lipschitz k x).continuous.aestronglyMeasurable
      (ae_of_all _ (fun y => by rw [Real.norm_eq_abs,abs_of_nonneg (kernel_nonneg k x y)]; exact kernel_le_one k x y)))
  filter_upwards with y
  by_cases hy : y ∈ Metric.ball x (r-δ)
  · have hk : kernel k x y = 1 := kernel_one k x (by
      simp only [Metric.mem_ball] at hy ⊢
      linarith)
    simp only [indicator_of_mem hy,hk,one_mul,le_refl]
  · simp only [indicator_of_notMem hy]
    exact mul_nonneg (kernel_nonneg k x y) (norm_nonneg _)

end LocalCancellation

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Telescoping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real

noncomputable section

namespace DiskScales

lemma width_add (d : ℝ) (j n : ℕ) : width d (j+n) = width (width d j) n := by
  simp only [width,pow_add]
  ring

lemma sum_width_tail {d p : ℝ} (hd : 0 ≤ d) (hp : 0 < p) (j n : ℕ) :
    (∑ i ∈ Finset.Ico j n, (width d i)^p) ≤ (width d j)^p/(1-(1/2 : ℝ)^p) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hs : Summable (fun i => (width (width d j) i)^p) :=
    summable_width_rpow (by dsimp [width]; positivity) hp
  have hh := hs.sum_le_tsum (Finset.range (n-j)) (fun i _ => Real.rpow_nonneg (by dsimp [width]; positivity) p)
  simp_rw [width_add]
  exact hh.trans_eq (tsum_width_rpow (by dsimp [width]; positivity) hp)

lemma dist_width_tail {α : Type*} [PseudoMetricSpace α] {d p C : ℝ} (hd : 0 ≤ d)
    (hp : 0 < p) (hC : 0 ≤ C) {f : ℕ → α} {j n : ℕ} (hjn : j ≤ n)
    (hincr : ∀ i, j ≤ i → i < n → dist (f i) (f (i+1)) ≤ C*(width d i)^p) :
    dist (f j) (f n) ≤ C*(width d j)^p/(1-(1/2 : ℝ)^p) := by
  have hh := dist_le_Ico_sum_of_dist_le hjn (fun {i} hi hin => hincr i hi hin)
  rw [← Finset.mul_sum] at hh
  exact hh.trans (by simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (sum_width_tail hd hp j n) hC)

end DiskScales

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

lemma moment_kernel_pairing_sub {a : ℂ → ℂ} (ha : Integrable a)
    {r δ ε : ℝ} {M N : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M)
    (l : RadiusDensity (r-ε) (r+ε) N) (x : ℂ) (hrδ : r+δ ≤ 3) (hrε : r+ε ≤ 3) :
    (∫ y, star (y-x)*(kernel l x y : ℂ)*a y)-
      (∫ y, star (y-x)*(kernel k x y : ℂ)*a y) =
      ∫ y, star (y-x)*((kernel l x y : ℂ)-kernel k x y)*a y := by
  rw [← integral_sub (general_moment_integrable ha l x hrε) (general_moment_integrable ha k x hrδ)]
  congr 1
  ext y
  ring

lemma total_correction {Cs : ℝ} (b : ι → ErrorPiece Cs) {a F : ℂ → ℂ} (ha : Integrable a)
    (hF : AEStronglyMeasurable F) (hFb : ∀ y, ‖F y‖ ≤ 1) (x z : ℂ)
    (hsupp : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ 3)
    (hzero : (∫ y, star (y-x)*F y*a y)+(∑ j, ∫ y, star (y-x)*F y*(b j).density y) = 0) :
    (∫ y, F y*a y)+(∑ j, ∫ y, F y*(b j).density y) =
      (∫ y, correction x z y*F y*a y)+(∑ j, ∫ y, correction x z y*F y*(b j).density y) := by
  rw [correcting_pairing ha hF hFb x z hsupp]
  simp_rw [correcting_pairing (b _).integrable hF hFb x z hsupp]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  linear_combination (star (z-x))⁻¹*hzero

lemma balanced_kernel_gap_identity {Cs : ℝ} (b : ι → ErrorPiece Cs) {a : ℂ → ℂ}
    (ha : Integrable a) {r δ ε : ℝ} {M N : ℝ≥0}
    (k : RadiusDensity (r-δ) (r+δ) M) (l : RadiusDensity (r-ε) (r+ε) N)
    (x z : ℂ) (hrδ : r+δ ≤ 3) (hrε : r+ε ≤ 3) (hεδ : ε ≤ δ)
    (hMk : (∫ y, star (y-x)*(kernel k x y : ℂ)*a y)+
      (∑ j, ∫ y, star (y-x)*(kernel k x y : ℂ)*(b j).density y) = 0)
    (hMl : (∫ y, star (y-x)*(kernel l x y : ℂ)*a y)+
      (∑ j, ∫ y, star (y-x)*(kernel l x y : ℂ)*(b j).density y) = 0) :
    ((∫ y, (kernel l x y : ℂ)*a y)+(∑ j, ∫ y, (kernel l x y : ℂ)*(b j).density y))-
      ((∫ y, (kernel k x y : ℂ)*a y)+(∑ j, ∫ y, (kernel k x y : ℂ)*(b j).density y)) =
    (∫ y, correction x z y*((kernel l x y : ℂ)-kernel k x y)*a y)+
      (∑ j, ∫ y, correction x z y*((kernel l x y : ℂ)-kernel k x y)*(b j).density y) := by
  let F (y : ℂ) := (kernel l x y : ℂ)-kernel k x y
  have hsupp : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ 3 := by
    intro y hy
    have hh := (abs_le.mp (difference_support k l hεδ x y hy)).2
    linarith
  have hzero : (∫ y, star (y-x)*F y*a y)+
      (∑ j, ∫ y, star (y-x)*F y*(b j).density y) = 0 := by
    simp_rw [F, ← moment_kernel_pairing_sub ha k l x hrδ hrε,
      ← moment_kernel_pairing_sub (b _).integrable k l x hrδ hrε]
    rw [Finset.sum_sub_distrib]
    linear_combination hMl-hMk
  have hcorr := total_correction b ha
    ((complex_kernel_lipschitz l x).continuous.sub (complex_kernel_lipschitz k x).continuous).aestronglyMeasurable
    (difference_bound k l x) x z hsupp hzero
  calc
    _ = ((∫ y, (kernel l x y : ℂ)*a y)-(∫ y, (kernel k x y : ℂ)*a y))+
        ((∑ j, ∫ y, (kernel l x y : ℂ)*(b j).density y)-
          (∑ j, ∫ y, (kernel k x y : ℂ)*(b j).density y)) := by abel
    _ = (∫ y, F y*a y)+(∑ j, ∫ y, F y*(b j).density y) := by
      rw [general_kernel_pairing_sub ha k l x, ← Finset.sum_sub_distrib]
      simp_rw [general_kernel_pairing_sub (b _).integrable k l x]
      rfl
    _ = _ := hcorr

end LocalCancellation

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

lemma kernel_error_bound {Cs δ r : ℝ} (b : ι → ErrorPiece Cs) (hCs : 0 ≤ Cs)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (k : RadiusDensity (r-δ) (r+δ) ⟨216/δ, by positivity⟩) (x : ℂ) :
    ‖∑ j, ∫ y, (kernel k x y : ℂ)*(b j).density y‖ ≤
      (1+216*Cs)/δ^(1/100 : ℝ)*errorPrice b (1/100) := by
  exact total_pairing_discount b (by norm_num : (0 : ℝ) ≤ 1/100)
    (by norm_num : (1/100 : ℝ) ≤ 1) hδ hδ1 (by linarith)
    (complex_kernel_lipschitz k x) (complex_kernel_bound k x)
    (by change (216/δ)*Cs ≤ (1+216*Cs)/δ
        apply (le_div_iff₀ hδ).mpr
        field_simp [hδ.ne']
        linarith)

lemma coarse_bound_scaled {Cs δ : ℝ} (b : ι → ErrorPiece Cs) (hδ : 0 < δ) :
    coarseMass b δ univ ≤ errorPrice b (1/100)*δ^(-(1/50 : ℝ)) := by
  have hh := coarseMass_bound b (by norm_num : (0 : ℝ) ≤ 1/100) hδ
  norm_num at hh
  simpa only [Real.rpow_neg hδ.le,div_eq_mul_inv] using hh

lemma scaled_ordinary_inactive {Cs δ t : ℝ} (b : ι → ErrorPiece Cs)
    (hCs : 0 ≤ Cs) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hAt : errorPrice b (1/100) ≤ t)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hFD : ∀ y, F y ≠ 0 → y ∈ D)
    (hL : (L : ℝ) ≤ 648/δ) (hsmall : coarseMass b δ D ≤ t*δ^(1/10 : ℝ)) :
    ‖∑ j, ∫ y, F y*(b j).density y‖ ≤ (16+4538*Cs)*t*δ^(1/10 : ℝ) := by
  have hi := increment_bound b hCs (by norm_num : (1/100 : ℝ) ≤ 1) hδ.le hδ1 hF hD hFb hFD
  have hs := scaled_increment hCs (errorPrice_nonneg b (1/100)) hAt hδ hδ1 (coarse_bound_scaled b hδ) hL
  have hM : 0 ≤ 2*δ^(1/5 : ℝ)*coarseMass b δ univ := by
    exact mul_nonneg (by positivity) (coarseMass_nonneg b δ univ)
  have hC : 0 ≤ 2*(3*(L : ℝ)+1)*Cs*δ^(2*(1-(1/100 : ℝ)))*errorPrice b (1/100) := by
    exact mul_nonneg (by positivity) (errorPrice_nonneg b (1/100))
  have hU : 0 ≤ t*δ^(1/10 : ℝ) := mul_nonneg ((errorPrice_nonneg b (1/100)).trans hAt) (by positivity)
  nlinarith

lemma scaled_corrected_inactive {Cs δ t : ℝ} (b : ι → ErrorPiece Cs)
    (hCs : 0 ≤ Cs) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hAt : errorPrice b (1/100) ≤ t)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hFD : ∀ y, F y ≠ 0 → y ∈ D)
    (hL : (L : ℝ) ≤ 648/δ) (hsmall : coarseMass b δ D ≤ t*δ^(1/10 : ℝ))
    (x z : ℂ) (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3) :
    ‖∑ j, ∫ y, correction x z y*F y*(b j).density y‖ ≤
      (16+4538*Cs)*t*δ^(1/10 : ℝ) := by
  have hi := corrected_inactive_bound b hCs (by norm_num : (1/100 : ℝ) ≤ 1) hδ.le hδ1 hF hD hFb hFD x z hz hD3
  have hs := scaled_increment hCs (errorPrice_nonneg b (1/100)) hAt hδ hδ1 (coarse_bound_scaled b hδ) hL
  have hM : 0 ≤ 2*δ^(1/5 : ℝ)*coarseMass b δ univ :=
    mul_nonneg (by positivity) (coarseMass_nonneg b δ univ)
  have hU : 0 ≤ t*δ^(1/10 : ℝ) := mul_nonneg ((errorPrice_nonneg b (1/100)).trans hAt) (by positivity)
  nlinarith

lemma scaled_corrected_active {Cs δ t : ℝ} (b : ι → ErrorPiece Cs)
    (hCs : 0 ≤ Cs) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hAt : errorPrice b (1/100) ≤ t)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hFD : ∀ y, F y ≠ 0 → y ∈ D)
    (hL : (L : ℝ) ≤ 648/δ) (x z : ℂ) (hz : (1 : ℝ)/2 ≤ ‖z-x‖)
    (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3)
    (hcap : coarseMass b δ (D \ Metric.ball z (δ^(1/5 : ℝ))) ≤ 2*(t*δ^(1/10 : ℝ))) :
    ‖∑ j, ∫ y, correction x z y*F y*(b j).density y‖ ≤
      (16+4538*Cs)*t*δ^(1/10 : ℝ) := by
  have hi := corrected_error_bound b hCs (by norm_num : (1/100 : ℝ) ≤ 1) hδ.le hδ1
    (Real.rpow_nonneg hδ.le (1/5)) hF hD hFb hFD x z hz hD3
  have hs := scaled_increment hCs (errorPrice_nonneg b (1/100)) hAt hδ hδ1 (coarse_bound_scaled b hδ) hL
  linarith

end LocalCancellation

namespace DiskScales

lemma successor_discount {δ : ℝ} (hδ : 0 < δ) :
    (δ/2)⁻¹^(1/100 : ℝ) ≤ 2*δ⁻¹^(1/100 : ℝ) := by
  rw [inv_div,Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) hδ.le,Real.inv_rpow hδ.le]
  have hh : (2 : ℝ)^(1/100 : ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1/100 : ℝ) ≤ 1)
  exact div_le_div_of_nonneg_right hh (by positivity)

lemma geometric_den_pos {p : ℝ} (hp : 0 < p) : 0 < 1-(1/2 : ℝ)^p := by
  linarith [norm_geometric_rpow_lt hp]

lemma coarse_error_scale {Cs A t δ : ℝ} (hCs : 0 ≤ Cs) (hA : 0 ≤ A)
    (hAt : A ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    2*((1+216*Cs)/δ^(1/100 : ℝ)*A) +
      (16+4538*Cs)*t*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) ≤
    (2*(1+216*Cs)+(16+4538*Cs)/(1-(1/2 : ℝ)^(1/10 : ℝ)))*t*δ^(-(1/50 : ℝ)) := by
  have ht : 0 ≤ t := hA.trans hAt
  have hp1 : δ^(-(1/100 : ℝ)) ≤ δ^(-(1/50 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  have hp2 : δ^(1/10 : ℝ) ≤ δ^(-(1/50 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  have h1 : 2*((1+216*Cs)/δ^(1/100 : ℝ)*A) ≤ 2*(1+216*Cs)*t*δ^(-(1/50 : ℝ)) := by
    rw [Real.rpow_neg hδ.le] at hp1
    calc
      _ = 2*(1+216*Cs)*A*(δ^(1/100 : ℝ))⁻¹ := by ring
      _ ≤ 2*(1+216*Cs)*t*δ^(-(1/50 : ℝ)) := mul_le_mul (by gcongr) hp1 (by positivity) (by positivity)
  have hd := geometric_den_pos (by norm_num : (0 : ℝ) < 1/10)
  have h2 := mul_le_mul_of_nonneg_left hp2
    (by positivity : 0 ≤ (16+4538*Cs)*t/(1-(1/2 : ℝ)^(1/10 : ℝ)))
  have h2' : (16+4538*Cs)*t*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) ≤
      ((16+4538*Cs)/(1-(1/2 : ℝ)^(1/10 : ℝ)))*t*δ^(-(1/50 : ℝ)) := by
    calc
      _ = ((16+4538*Cs)*t/(1-(1/2 : ℝ)^(1/10 : ℝ)))*δ^(1/10 : ℝ) := by ring
      _ ≤ ((16+4538*Cs)*t/(1-(1/2 : ℝ)^(1/10 : ℝ)))*δ^(-(1/50 : ℝ)) := h2
      _ = _ := by ring
  linarith

end DiskScales

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

lemma inactive_kernel_distance {Cs d t r : ℝ} (b : ι → ErrorPiece Cs)
    (hCs : 0 ≤ Cs) (hd : 0 < d) (hd1 : d ≤ 1) (hAt : errorPrice b (1/100) ≤ t)
    (k : ∀ n : ℕ, RadiusDensity (r-width d n) (r+width d n)
      ⟨216/width d n, div_nonneg (by norm_num) (width_pos hd n).le⟩) (x : ℂ) (n : ℕ)
    (hsmall : coarseMass b (width d n) (thinShell x r (width d n)) ≤ t*(width d n)^(1/10 : ℝ)) :
    dist (∑ j, ∫ y, (kernel (k n) x y : ℂ)*(b j).density y)
      (∑ j, ∫ y, (kernel (k (n+1)) x y : ℂ)*(b j).density y) ≤
      (16+4538*Cs)*t*(width d n)^(1/10 : ℝ) := by
  rw [dist_eq_norm,norm_sub_rev,← Finset.sum_sub_distrib]
  simp_rw [general_kernel_pairing_sub (b _).integrable (k n) (k (n+1)) x]
  apply scaled_ordinary_inactive b hCs (width_pos hd n) ((width_le hd.le n).trans hd1) hAt
    ((complex_kernel_lipschitz (k (n+1)) x).sub (complex_kernel_lipschitz (k n) x))
    (measurableSet_thinShell x r (width d n)) (difference_bound (k n) (k (n+1)) x)
    (difference_support (k n) (k (n+1)) (width_antitone hd.le (Nat.le_succ n)) x) ?_ hsmall
  change 216/width d (n+1)+216/width d n ≤ 648/width d n
  rw [width_succ]
  exact le_of_eq (by ring)

lemma kernel_gap_errors {Cs d t r : ℝ} (b : ι → ErrorPiece Cs)
    (hCs : 0 ≤ Cs) (hd : 0 < d) (hd1 : d ≤ 1) (hAt : errorPrice b (1/100) ≤ t)
    (k : ∀ n : ℕ, RadiusDensity (r-width d n) (r+width d n)
      ⟨216/width d n, div_nonneg (by norm_num) (width_pos hd n).le⟩) (x : ℂ) {j n : ℕ} (hjn : j < n)
    (hsmall : ∀ i, j < i → i < n → coarseMass b (width d i) (thinShell x r (width d i)) ≤
      t*(width d i)^(1/10 : ℝ)) :
    let B := (2*(1+216*Cs)+(16+4538*Cs)/(1-(1/2 : ℝ)^(1/10 : ℝ)))*t*(width d j)^(-(1/50 : ℝ))
    ‖∑ v, ∫ y, (kernel (k j) x y : ℂ)*(b v).density y‖ ≤ B ∧
    ‖∑ v, ∫ y, (kernel (k n) x y : ℂ)*(b v).density y‖ ≤ B := by
  have ht : 0 ≤ t := (errorPrice_nonneg b (1/100)).trans hAt
  have hwp (i : ℕ) := width_pos hd i
  have hw1 (i : ℕ) := (width_le hd.le i).trans hd1
  have hjpos : 0 < width d j := hwp j
  let P (i : ℕ) := ∑ v, ∫ y, (kernel (k i) x y : ℂ)*(b v).density y
  have hind (i : ℕ) : ‖P i‖ ≤ (1+216*Cs)/(width d i)^(1/100 : ℝ)*errorPrice b (1/100) :=
    kernel_error_bound b hCs (hwp i) (hw1 i) (k i) x
  have hsuc : ‖P (j+1)‖ ≤ 2*((1+216*Cs)/(width d j)^(1/100 : ℝ)*errorPrice b (1/100)) := by
    have hh := successor_discount (hwp j)
    have hi := hind (j+1)
    rw [width_succ] at hi
    have ha := mul_le_mul_of_nonneg_left hh
      (mul_nonneg (show 0 ≤ 1+216*Cs by linarith) (errorPrice_nonneg b (1/100)))
    simp only [Real.inv_rpow (hwp j).le,Real.inv_rpow (by positivity : 0 ≤ width d j/2)] at ha
    exact hi.trans (by convert ha using 1 <;> ring)
  have htail := dist_width_tail hd.le (by norm_num : (0 : ℝ) < 1/10)
    (by positivity : 0 ≤ (16+4538*Cs)*t) (Nat.succ_le_of_lt hjn)
    (fun i hji hin => inactive_kernel_distance b hCs hd hd1 hAt k x i (hsmall i (by omega) hin))
  have hpow : (width d (j+1))^(1/10 : ℝ) ≤ (width d j)^(1/10 : ℝ) :=
    Real.rpow_le_rpow (hwp (j+1)).le (width_antitone hd.le (Nat.le_succ j)) (by norm_num)
  have hdg := geometric_den_pos (by norm_num : (0 : ℝ) < 1/10)
  have htail' : dist (P (j+1)) (P n) ≤
      (16+4538*Cs)*t*(width d j)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) :=
    htail.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) hdg.le)
  have hn : ‖P n‖ ≤ ‖P (j+1)‖+dist (P (j+1)) (P n) := by
    calc
      ‖P n‖ = ‖P (j+1)+(P n-P (j+1))‖ := by congr 1; abel
      _ ≤ ‖P (j+1)‖+‖P n-P (j+1)‖ := norm_add_le _ _
      _ = _ := by rw [dist_eq_norm,norm_sub_rev]
  have hscale := coarse_error_scale hCs (errorPrice_nonneg b (1/100)) hAt (hwp j) (hw1 j)
  constructor
  · have hnon : 0 ≤ (1+216*Cs)/(width d j)^(1/100 : ℝ)*errorPrice b (1/100) :=
      mul_nonneg (by positivity) (errorPrice_nonneg b (1/100))
    have htailnon : 0 ≤ (16+4538*Cs)*t*(width d j)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) := by positivity
    exact (hind j).trans (by linarith)
  · change ‖P n‖ ≤ _
    linarith

lemma corrected_kernel_gap {Cs d t r : ℝ} (b : ι → ErrorPiece Cs)
    (hCs : 0 ≤ Cs) (hd : 0 < d) (hdq : d ≤ 1/4) (hr : r ∈ Icc (1 : ℝ) 2)
    (hAt : errorPrice b (1/100) ≤ t)
    (k : ∀ n : ℕ, RadiusDensity (r-width d n) (r+width d n)
      ⟨216/width d n, div_nonneg (by norm_num) (width_pos hd n).le⟩) (x z : ℂ) {j n : ℕ} (hjn : j < n)
    (hz : (1 : ℝ)/2 ≤ ‖z-x‖)
    (hcap : coarseMass b (width d j) (thinShell x r (width d j) \ Metric.ball z ((width d j)^(1/5 : ℝ))) ≤
      2*(t*(width d j)^(1/10 : ℝ)))
    (hsmall : ∀ i, j < i → i < n → coarseMass b (width d i) (thinShell x r (width d i)) ≤
      t*(width d i)^(1/10 : ℝ)) :
    ‖∑ v, ∫ y, correction x z y*((kernel (k n) x y : ℂ)-kernel (k j) x y)*(b v).density y‖ ≤
      (16+4538*Cs)*t*(width d j)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) := by
  have ht : 0 ≤ t := (errorPrice_nonneg b (1/100)).trans hAt
  have hd1 : d ≤ 1 := by linarith
  have hwp (i : ℕ) := width_pos hd i
  have hw1 (i : ℕ) := (width_le hd.le i).trans hd1
  have hrw (i : ℕ) : r+width d i ≤ 3 := by linarith [width_le hd.le i,hr.2]
  let R (i : ℕ) := ∑ v, ∫ y, correction x z y*(kernel (k i) x y : ℂ)*(b v).density y
  have hid (i l : ℕ) : R l-R i =
      ∑ v, ∫ y, correction x z y*((kernel (k l) x y : ℂ)-kernel (k i) x y)*(b v).density y := by
    dsimp only [R]
    rw [← Finset.sum_sub_distrib]
    simp_rw [corrected_kernel_pairing_sub (b _).integrable (k i) (k l) x z (hrw i) (hrw l) hz]
  have hincr (i : ℕ) (hji : j ≤ i) (hin : i < n) :
      dist (R i) (R (i+1)) ≤ (16+4538*Cs)*t*(width d i)^(1/10 : ℝ) := by
    rw [dist_eq_norm,norm_sub_rev,hid]
    have hD3 : ∀ y ∈ thinShell x r (width d i), ‖y-x‖ ≤ 3 := by
      intro y hy
      have hh := (abs_le.mp (show |‖y-x‖-r| ≤ width d i from hy)).2
      linarith [hrw i]
    have hL : (216/width d (i+1)+216/width d i : ℝ) ≤ 648/width d i := by rw [width_succ]; exact le_of_eq (by ring)
    have hF := (complex_kernel_lipschitz (k (i+1)) x).sub (complex_kernel_lipschitz (k i) x)
    have hs := difference_support (k i) (k (i+1)) (width_antitone hd.le (Nat.le_succ i)) x
    by_cases hij : i = j
    · subst i
      exact scaled_corrected_active b hCs (hwp j) (hw1 j) hAt hF
        (measurableSet_thinShell x r (width d j)) (difference_bound (k j) (k (j+1)) x) hs hL x z hz hD3 hcap
    · exact scaled_corrected_inactive b hCs (hwp i) (hw1 i) hAt hF
        (measurableSet_thinShell x r (width d i)) (difference_bound (k i) (k (i+1)) x) hs hL
        (hsmall i (by omega) hin) x z hz hD3
  have hh := dist_width_tail hd.le (by norm_num : (0 : ℝ) < 1/10)
    (by positivity : 0 ≤ (16+4538*Cs)*t) hjn.le hincr
  rw [dist_eq_norm,norm_sub_rev,hid] at hh
  exact hh

end LocalCancellation

namespace DiskScales

lemma errorGapConstant_pos {Cs : ℝ} (hCs : 0 ≤ Cs) : 0 < errorGapConstant Cs := by
  have hden : 0 < 1-(1/2 : ℝ)^(1/10 : ℝ) := by linarith [norm_geometric_rpow_lt (by norm_num : (0 : ℝ) < 1/10)]
  unfold errorGapConstant
  positivity

lemma directionGapConstant_ge {Cs κ : ℝ} (hCs : 0 ≤ Cs) (hκ : 0 < κ) :
    16+4538*Cs ≤ directionGapConstant Cs κ := by
  have hden : 0 < 1-(1/2 : ℝ)^(1/10 : ℝ) := by linarith [norm_geometric_rpow_lt (by norm_num : (0 : ℝ) < 1/10)]
  have he : 0 ≤ errorGapConstant Cs/κ := div_nonneg (errorGapConstant_pos hCs).le hκ.le
  have hn : 0 ≤ (16+4538*Cs)/(1-(1/2 : ℝ)^(1/10 : ℝ)) := by positivity
  unfold directionGapConstant
  linarith

lemma directionGapConstant_pos {Cs κ : ℝ} (hCs : 0 ≤ Cs) (hκ : 0 < κ) :
    0 < directionGapConstant Cs κ := by
  have hh := directionGapConstant_ge hCs hκ
  linarith

lemma direction_cap_scale {Cs κ δ t : ℝ} (hCs : 0 ≤ Cs) (hκ : 0 < κ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : 0 ≤ t) :
    4*δ^(1/5 : ℝ)*((errorGapConstant Cs*t*δ^(-(1/50 : ℝ)))/κ)+14*(t*δ^(1/10 : ℝ))+
      (16+4538*Cs)*t*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) ≤
      directionGapConstant Cs κ*t*δ^(1/10 : ℝ) := by
  have hp : δ^(1/5 : ℝ)*δ^(-(1/50 : ℝ)) ≤ δ^(1/10 : ℝ) := by
    rw [← Real.rpow_add hδ]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  have hb := mul_le_mul_of_nonneg_left hp
    (by exact mul_nonneg (mul_nonneg (by norm_num) (div_nonneg (errorGapConstant_pos hCs).le hκ.le)) ht :
      0 ≤ 4*(errorGapConstant Cs/κ)*t)
  have hb' : 4*δ^(1/5 : ℝ)*((errorGapConstant Cs*t*δ^(-(1/50 : ℝ)))/κ) ≤
      4*(errorGapConstant Cs/κ)*t*δ^(1/10 : ℝ) := by
    calc
      _ = 4*(errorGapConstant Cs/κ)*t*(δ^(1/5 : ℝ)*δ^(-(1/50 : ℝ))) := by ring
      _ ≤ _ := hb
  have hnon : 0 ≤ (16+4538*Cs)*t*δ^(1/10 : ℝ) := by positivity
  calc
    _ ≤ 4*(errorGapConstant Cs/κ)*t*δ^(1/10 : ℝ)+14*(t*δ^(1/10 : ℝ))+
        (16+4538*Cs)*t*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) := by linarith
    _ ≤ (16+4538*Cs)*t*δ^(1/10 : ℝ)+
        (4*(errorGapConstant Cs/κ)*t*δ^(1/10 : ℝ)+14*(t*δ^(1/10 : ℝ))+
        (16+4538*Cs)*t*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) := le_add_of_nonneg_left hnon
    _ = _ := by unfold directionGapConstant; ring

end DiskScales

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

/-- The full finite/infinite active-width argument at a fixed center. The cap
premise is exactly the already proved shell concentration output, not a radius
selection or a projection estimate. -/
lemma direction_sequence_point {Cs κ d t r : ℝ} {e : ℂ} (a : ConeDensity e κ)
    (b : ι → ErrorPiece Cs) (he : ‖e‖ = 1) (hκ : 0 < κ)
    (hCs : 0 ≤ Cs) (hd : 0 < d) (hdq : d ≤ 1/4) (hr : r ∈ Icc (1 : ℝ) 2)
    (hAt : errorPrice b (1/100) ≤ t)
    (k : ∀ n : ℕ, RadiusDensity (r-width d n) (r+width d n)
      ⟨216/width d n, div_nonneg (by norm_num) (width_pos hd n).le⟩) (x : ℂ)
    (hM : ∀ n, (∫ y, star (y-x)*(kernel (k n) x y : ℂ)*a.density y)+
      (∑ v, ∫ y, star (y-x)*(kernel (k n) x y : ℂ)*(b v).density y) = 0)
    (hcap : ∀ j, t*(width d j)^(1/10 : ℝ) ≤ coarseMass b (width d j) (thinShell x r (width d j)) →
      (∫ y in Metric.ball x (r-width d j), ‖a.density y‖) ≤
        (errorGapConstant Cs/κ)*t*(width d j)^(-(1/50 : ℝ)) →
      ∃ z ∈ thinShell x r (width d j),
        (∫ y in thinShell x r (width d j) \ Metric.ball z ((width d j)^(1/5 : ℝ)), ‖a.density y‖)+
        coarseMass b (width d j) (thinShell x r (width d j) \ Metric.ball z ((width d j)^(1/5 : ℝ))) ≤
          2*(t*(width d j)^(1/10 : ℝ))) :
    max 0 (-inner ℝ e ((∫ y in Metric.ball x r, a.density y)+(∑ v, ∫ y in Metric.ball x r, (b v).density y))) ≤
      (1+216*Cs)/d^(1/100 : ℝ)*errorPrice b (1/100)+
      directionGapConstant Cs κ*t*d^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) := by
  classical
  have ht : 0 ≤ t := (errorPrice_nonneg b (1/100)).trans hAt
  have hd1 : d ≤ 1 := by linarith
  have hwp (i : ℕ) := width_pos hd i
  have hwq (i : ℕ) := (width_le hd.le i).trans hdq
  have hw1 (i : ℕ) := (width_le hd.le i).trans hd1
  have hrw (i : ℕ) : r+width d i ≤ 3 := by linarith [hwq i,hr.2]
  have hgpos := directionGapConstant_pos hCs hκ
  have hgle := directionGapConstant_ge hCs hκ
  let p (i : ℕ) := ∑ v, ∫ y, (kernel (k i) x y : ℂ)*(b v).density y
  let P (i : ℕ) := (∫ y, (kernel (k i) x y : ℂ)*a.density y)+p i
  let N (i : ℕ) := max 0 (-inner ℝ e (P i))
  let active (i : ℕ) := t*(width d i)^(1/10 : ℝ) ≤ coarseMass b (width d i) (thinShell x r (width d i))
  let inc (i : ℕ) := directionGapConstant Cs κ*t*(width d i)^(1/10 : ℝ)
  let B := (1+216*Cs)/d^(1/100 : ℝ)*errorPrice b (1/100)
  have hi0 (i : ℕ) : 0 ≤ inc i := mul_nonneg (mul_nonneg hgpos.le ht) (Real.rpow_nonneg (hwp i).le _)
  have hN0 (i : ℕ) : 0 ≤ N i := le_max_left _ _
  have hNerr (i : ℕ) : N i ≤ ‖p i‖ := cone_negative_le_error a he hκ.le
    (kernel_lipschitz (k i) x).continuous.aestronglyMeasurable
    (kernel_nonneg (k i) x) (kernel_le_one (k i) x) (p i)
  have hfirst (n : ℕ) (hn : ∀ i < n, ¬active i) : N n ≤ B+∑ i ∈ Finset.range n, inc i := by
    have hincr (i : ℕ) (hin : i < n) : dist (p i) (p (i+1)) ≤ inc i := by
      have hs : coarseMass b (width d i) (thinShell x r (width d i)) ≤ t*(width d i)^(1/10 : ℝ) :=
        le_of_lt (lt_of_not_ge (hn i hin))
      exact (inactive_kernel_distance b hCs hd hd1 hAt k x i hs).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hgle ht) (Real.rpow_nonneg (hwp i).le _))
    have hh := dist_le_range_sum_of_dist_le n (fun {i} hin => hincr i hin)
    have hp0 : ‖p 0‖ ≤ B := by
      have h := kernel_error_bound b hCs (hwp 0) (hw1 0) (k 0) x
      simpa only [p,B,width,pow_zero,mul_one] using h
    have hp : ‖p n‖ ≤ ‖p 0‖+dist (p 0) (p n) := by
      calc
        ‖p n‖ = ‖p 0+(p n-p 0)‖ := by congr 1; abel
        _ ≤ ‖p 0‖+‖p n-p 0‖ := norm_add_le _ _
        _ = _ := by rw [dist_eq_norm,norm_sub_rev]
    linarith [hNerr n]
  have hgap (j n : ℕ) (hjn : j < n) (ha : active j)
      (hn : ∀ i, j < i → i < n → ¬active i) : N n ≤ N j+inc j := by
    by_cases hnn : N n ≤ N j
    · exact hnn.trans (le_add_of_nonneg_right (hi0 j))
    have hsmall (i : ℕ) (hji : j < i) (hin : i < n) :
        coarseMass b (width d i) (thinShell x r (width d i)) ≤ t*(width d i)^(1/10 : ℝ) :=
      le_of_lt (lt_of_not_ge (hn i hji hin))
    obtain ⟨hpj,hpn⟩ := kernel_gap_errors b hCs hd hd1 hAt k x hjn hsmall
    change ‖p j‖ ≤ errorGapConstant Cs*t*(width d j)^(-(1/50 : ℝ)) at hpj
    change ‖p n‖ ≤ errorGapConstant Cs*t*(width d j)^(-(1/50 : ℝ)) at hpn
    have hneg : inner ℝ e (P n) < 0 := by
      by_contra hh
      have hh' : N n = 0 := max_eq_left (by linarith [le_of_not_gt hh])
      exact hnn (by rw [hh']; exact hN0 j)
    have hmass := cone_mass_of_nonpositive a he hκ
      (kernel_lipschitz (k n) x).continuous.aestronglyMeasurable
      (kernel_nonneg (k n) x) (kernel_le_one (k n) x) hneg.le
    have hinterior : (∫ y in Metric.ball x (r-width d j), ‖a.density y‖) ≤
        (errorGapConstant Cs/κ)*t*(width d j)^(-(1/50 : ℝ)) := by
      calc
        _ ≤ ∫ y, kernel (k n) x y*‖a.density y‖ :=
          interior_mass_le_kernel a.integrable (k n) x (width_antitone hd.le hjn.le)
        _ ≤ ‖p n‖/κ := hmass
        _ ≤ (errorGapConstant Cs*t*(width d j)^(-(1/50 : ℝ)))/κ := div_le_div_of_nonneg_right hpn hκ.le
        _ = _ := by ring
    obtain ⟨z,hz,hzc⟩ := hcap j ha hinterior
    have hzlo : (1 : ℝ)/2 ≤ ‖z-x‖ := by
      have hh := (abs_le.mp (show |‖z-x‖-r| ≤ width d j from hz)).1
      linarith [hr.1,hwq j]
    have hD3 : ∀ y ∈ thinShell x r (width d j), ‖y-x‖ ≤ 3 := by
      intro y hy
      have hh := (abs_le.mp (show |‖y-x‖-r| ≤ width d j from hy)).2
      linarith [hrw j]
    have hcapb : coarseMass b (width d j) (thinShell x r (width d j) \ Metric.ball z ((width d j)^(1/5 : ℝ))) ≤
        2*(t*(width d j)^(1/10 : ℝ)) := by
      have hn : 0 ≤ ∫ y in thinShell x r (width d j) \ Metric.ball z ((width d j)^(1/5 : ℝ)), ‖a.density y‖ :=
        integral_nonneg (fun y => norm_nonneg _)
      linarith
    have hcapa : (∫ y in thinShell x r (width d j) \ Metric.ball z ((width d j)^(1/5 : ℝ)), ‖a.density y‖) ≤
        2*(t*(width d j)^(1/10 : ℝ)) := by
      linarith [coarseMass_nonneg b (width d j) (thinShell x r (width d j) \ Metric.ball z ((width d j)^(1/5 : ℝ)))]
    let R := ∑ v, ∫ y, correction x z y*((kernel (k n) x y : ℂ)-kernel (k j) x y)*(b v).density y
    have hR : ‖R‖ ≤ (16+4538*Cs)*t*(width d j)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) :=
      corrected_kernel_gap b hCs hd hdq hr hAt k x z hjn hzlo hcapb hsmall
    have hsupp : ∀ y, kernel (k n) x y-kernel (k j) x y ≠ 0 → y ∈ thinShell x r (width d j) := by
      intro y hy
      apply difference_support (k j) (k n) (width_antitone hd.le hjn.le) x y
      simpa only [← Complex.ofReal_sub,ne_eq,Complex.ofReal_eq_zero] using hy
    have hcor : P n-P j =
        (∫ y, correction x z y*((kernel (k n) x y : ℂ)-kernel (k j) x y)*a.density y)+R :=
      balanced_kernel_gap_identity b a.integrable (k j) (k n) x z (hrw j) (hrw n)
        (width_antitone hd.le hjn.le) (hM j) (hM n)
    have hh := negative_gap_cap a he hκ (Real.rpow_nonneg (hwp j).le (1/5))
      (kernel_lipschitz (k j) x).continuous.aestronglyMeasurable
      (kernel_lipschitz (k n) x).continuous.aestronglyMeasurable
      (kernel_nonneg (k j) x) (kernel_le_one (k j) x)
      (kernel_nonneg (k n) x) (kernel_le_one (k n) x)
      (measurableSet_thinShell x r (width d j)) hsupp x z hzlo hD3 hcapa hpj hpn hneg hcor
    change N n ≤ N j+4*(width d j)^(1/5 : ℝ)*((errorGapConstant Cs*t*(width d j)^(-(1/50 : ℝ)))/κ)+
      7*(2*(t*(width d j)^(1/10 : ℝ)))+‖R‖ at hh
    have hscale := direction_cap_scale hCs hκ (hwp j) (hw1 j) ht
    dsimp only [inc]
    linarith
  let Z := (∫ y in Metric.ball x r, a.density y)+(∑ v, ∫ y in Metric.ball x r, (b v).density y)
  have hlimP : Tendsto P atTop (𝓝 Z) :=
    (tendsto_kernel_pairing k (tendsto_width d) x a.integrable).add
      (tendsto_finsetSum Finset.univ (fun v _ => tendsto_kernel_pairing k (tendsto_width d) x (b v).integrable))
  have hlimN : Tendsto N atTop (𝓝 (max 0 (-inner ℝ e Z))) :=
    tendsto_const_nhds.max ((tendsto_const_nhds.inner hlimP).neg)
  have hsm : Summable inc := (summable_width_rpow hd.le (by norm_num : (0 : ℝ) < 1/10)).mul_left _
  have hh := last_active_limit active N inc B _ hi0 hsm hlimN hfirst hgap
  dsimp only [inc] at hh
  rw [tsum_mul_left,tsum_width_rpow hd.le (by norm_num : (0 : ℝ) < 1/10)] at hh
  convert hh using 1; dsimp only [B,Z]; ring

end LocalCancellation

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

/-- Radius-independent exceptional union for the full directional sequence.
The cap property is produced by shell concentration for the actual densities. -/
theorem direction_sequence {e : ℂ} {κ Cs d t : ℝ} (a : ConeDensity e κ)
    (b : ι → ErrorPiece Cs) (he : ‖e‖ = 1) (hκ : 0 < κ)
    (hCs : 0 ≤ Cs) (hd : 0 < d) (hdq : d ≤ 1/4)
    (hgeom : ∀ δ : ℝ, 0 < δ → δ ≤ d → δ ≤ (δ^(1/5 : ℝ))^2/1600)
    (ht : 0 < t) (hAt : errorPrice b (1/100) ≤ t) :
    ∃ E : Set ℂ, MeasurableSet E ∧
      volume E ≤ ∑' n : ℕ, directionShellBound b κ t (width d n) ∧
      ∀ x ∉ E, ∀ r ∈ Icc (1 : ℝ) 2,
        ∀ k : ∀ n : ℕ, RadiusDensity (r-width d n) (r+width d n)
          ⟨216/width d n, div_nonneg (by norm_num) (width_pos hd n).le⟩,
        (∀ n, (∫ y, star (y-x)*(kernel (k n) x y : ℂ)*a.density y)+
          (∑ v, ∫ y, star (y-x)*(kernel (k n) x y : ℂ)*(b v).density y) = 0) →
        max 0 (-inner ℝ e ((∫ y in Metric.ball x r, a.density y)+
          (∑ v, ∫ y in Metric.ball x r, (b v).density y))) ≤
          (1+216*Cs)/d^(1/100 : ℝ)*errorPrice b (1/100)+
          directionGapConstant Cs κ*t*d^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) := by
  have : IsFiniteMeasure (densityMeasure a.density) := densityMeasure_finite a.integrable
  have hd1 : d ≤ 1 := by linarith
  have hwp (n : ℕ) := width_pos hd n
  have hw1 (n : ℕ) := (width_le hd.le n).trans hd1
  have hρ (n : ℕ) : 0 < (width d n)^(1/5 : ℝ) := Real.rpow_pos_of_pos (hwp n) _
  have hρ1 (n : ℕ) : (width d n)^(1/5 : ℝ) ≤ 1 :=
    Real.rpow_le_one (hwp n).le (hw1 n) (by norm_num)
  have hs (n : ℕ) := shell_concentration (coarseMeasure b (width d n)) (densityMeasure a.density)
    (hρ n) (hρ1 n) (hwp n) (hgeom _ (hwp n) (width_le hd.le n))
    (mul_nonneg (mul_nonneg (div_nonneg (errorGapConstant_pos hCs).le hκ.le) ht.le)
      (Real.rpow_nonneg (hwp n).le (-(1/50 : ℝ))))
    (mul_pos ht (Real.rpow_pos_of_pos (hwp n) (1/10 : ℝ)))
  choose E hE hEv hEst using hs
  refine ⟨⋃ n, E n, MeasurableSet.iUnion hE,
    (measure_iUnion_le E).trans (ENNReal.tsum_le_tsum ?_), ?_⟩
  · intro n
    simpa only [directionShellBound,coarseMeasure_apply b (width d n) MeasurableSet.univ] using hEv n
  · intro x hx r hr k hM
    apply direction_sequence_point a b he hκ hCs hd hdq hr hAt k x hM
    intro j ha hi
    have hxE : x ∉ E j := fun hh => hx (mem_iUnion.mpr ⟨j,hh⟩)
    obtain ⟨z,hz,hcap⟩ := hEst j x hxE r hr
      (by rw [coarseMeasure_apply b (width d j) (measurableSet_thinShell x r (width d j))]; exact ENNReal.ofReal_le_ofReal ha)
      (by rw [densityMeasure_apply a.integrable measurableSet_ball]; exact ENNReal.ofReal_le_ofReal hi)
    refine ⟨z,hz,?_⟩
    have hD : MeasurableSet (thinShell x r (width d j) \ Metric.ball z ((width d j)^(1/5 : ℝ))) :=
      (measurableSet_thinShell x r (width d j)).diff measurableSet_ball
    rw [Measure.add_apply, densityMeasure_apply a.integrable hD,
      coarseMeasure_apply b (width d j) hD, ← ENNReal.ofReal_add
        (integral_nonneg (fun _ => norm_nonneg _)) (coarseMass_nonneg b (width d j) _)] at hcap
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num)
      (mul_nonneg ht.le (Real.rpow_nonneg (hwp j).le _)))).mp hcap

end LocalCancellation

namespace DiskMoments
open DiskKernels

lemma neighborhood_kernel {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {x : ℂ} {r δ : ℝ}
    (hr : NeighborhoodRadius g x r) (hδ : 0 < δ) (hδq : δ ≤ 1/4) :
    ∃ k : RadiusDensity (r-δ) (r+δ) ⟨216/δ, by positivity⟩,
      (∫ y, kernel k x y • (star (y-x)*gradient g y)) = 0 := by
  apply balanced_kernel hg x hr.1 hδ hδq
  · apply hr.2 _ (by linarith [hr.1.1])
    rw [abs_le]
    constructor <;> linarith
  · apply hr.2 _ (by linarith [hr.1.1])
    rw [abs_le]
    constructor <;> linarith

end DiskMoments

namespace LocalCancellation
open DiskKernels DiskMoments DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

lemma mixed_moment_pairing_decomposition {Cs r δ : ℝ} (b : ι → ErrorPiece Cs)
    {a : ℂ → ℂ} (ha : Integrable a) {M : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M)
    (x : ℂ) {h : ℂ → ℂ} (hr : r+δ ≤ 3)
    (hh : ∀ᵐ y, y ∈ Metric.ball x 3 → a y+∑ j, (b j).density y = h y) :
    (∫ y, star (y-x)*(kernel k x y : ℂ)*a y)+
      (∑ j, ∫ y, star (y-x)*(kernel k x y : ℂ)*(b j).density y) =
      ∫ y, kernel k x y • (star (y-x)*h y) := by
  rw [← integral_finsetSum _ (fun j _ => moment_pairing_integrable (b j) k x hr),
    ← integral_add (general_moment_integrable ha k x hr)
      (integrable_finsetSum _ (fun j _ => moment_pairing_integrable (b j) k x hr))]
  apply integral_congr_ae
  filter_upwards [hh] with y hy
  simp only [← Finset.mul_sum, ← mul_add]
  by_cases hmem : y ∈ Metric.ball x 3
  · rw [hy hmem, Complex.real_smul]
    ring
  · have hk : kernel k x y = 0 := kernel_zero k x (fun hb => hmem (lt_of_lt_of_le hb hr))
    rw [hk, Complex.ofReal_zero, mul_zero, zero_mul, zero_smul]

lemma mixed_ball_pairing_decomposition {Cs r : ℝ} (b : ι → ErrorPiece Cs)
    {a : ℂ → ℂ} (ha : Integrable a) (x : ℂ) {h : ℂ → ℂ} (hr : r ≤ 3)
    (hh : ∀ᵐ y, y ∈ Metric.ball x 3 → a y+∑ j, (b j).density y = h y) :
    (∫ y in Metric.ball x r, a y)+(∑ j, ∫ y in Metric.ball x r, (b j).density y) =
      ∫ y in Metric.ball x r, h y := by
  rw [← integral_finsetSum _ (fun j _ => (b j).integrable.integrableOn),
    ← integral_add ha.integrableOn (integrable_finsetSum _ (fun j _ => (b j).integrable.integrableOn))]
  apply setIntegral_congr_ae measurableSet_ball
  filter_upwards [hh] with y hy hyb
  exact hy (lt_of_lt_of_le hyb hr)

/-- Directional estimate at all genuine neighborhood-maximizing radii,
with only the original local density equality. -/
theorem direction_raw {e : ℂ} {κ Cs d t : ℝ} (a : ConeDensity e κ)
    (b : ι → ErrorPiece Cs) (he : ‖e‖ = 1) (hκ : 0 < κ)
    (hCs : 0 ≤ Cs) (hd : 0 < d) (hdq : d ≤ 1/4)
    (hgeom : ∀ δ : ℝ, 0 < δ → δ ≤ d → δ ≤ (δ^(1/5 : ℝ))^2/1600)
    (ht : 0 < t) (hAt : errorPrice b (1/100) ≤ t)
    {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) :
    ∃ E : Set ℂ, MeasurableSet E ∧
      volume E ≤ ∑' n : ℕ, directionShellBound b κ t (width d n) ∧
      ∀ x ∉ E,
        (∀ᵐ y, y ∈ Metric.ball x 3 → a.density y+∑ j, (b j).density y = gradient g y) →
        ∀ r, NeighborhoodRadius g x r →
        max 0 (-inner ℝ e (∫ y in Metric.ball x r, gradient g y)) ≤
          (1+216*Cs)/d^(1/100 : ℝ)*errorPrice b (1/100)+
          directionGapConstant Cs κ*t*d^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) := by
  obtain ⟨E,hE,hEv,hEst⟩ := direction_sequence a b he hκ hCs hd hdq hgeom ht hAt
  refine ⟨E,hE,hEv,?_⟩
  intro x hx hh r hr
  choose k hk using fun n => neighborhood_kernel hg hr (width_pos hd n) ((width_le hd.le n).trans hdq)
  rw [← mixed_ball_pairing_decomposition b a.integrable x (by linarith [hr.1.2]) hh]
  apply hEst x hx r hr.1 k
  intro n
  rw [mixed_moment_pairing_decomposition b a.integrable (k n) x
    (by linarith [hr.1.2,(width_le hd.le n).trans hdq]) hh]
  exact hk n

end LocalCancellation

namespace DiskScales

lemma third_power_identity {δ : ℝ} (hδ : 0 < δ) :
    ((δ^(1/10 : ℝ))⁻¹ * (δ / (δ^(1/5 : ℝ))^2 * δ^(-(1/50 : ℝ)))) *
      (δ^(-(1/50 : ℝ))/δ^(1/10 : ℝ)) = δ^(9/25 : ℝ) := by
  rw [second_power_identity hδ, ← Real.rpow_sub hδ, ← Real.rpow_add hδ]
  norm_num

lemma direction_shell_tail_scaled {A t δ M H : ℝ} (hA : 0 ≤ A) (ht : 0 < t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM0 : 0 ≤ M) (hH : 0 ≤ H)
    (hM : M ≤ A*δ^(-(1/50 : ℝ))) :
    (ENNReal.ofReal (t*δ^(1/10 : ℝ)))⁻¹ ^ 2 *
      (ENNReal.ofReal (156*δ/δ^(1/5 : ℝ))*ENNReal.ofReal M*ENNReal.ofReal M) +
    (ENNReal.ofReal (t*δ^(1/10 : ℝ)))⁻¹ *
      ((ENNReal.ofReal (6*Real.pi)*ENNReal.ofReal
        (2*(200*δ/(δ^(1/5 : ℝ))^2)*(1+(H*t*δ^(-(1/50 : ℝ)))/(t*δ^(1/10 : ℝ)))))*ENNReal.ofReal M) ≤
    ENNReal.ofReal ((1+H)*(156*(A/t)^2*δ^(14/25 : ℝ)+2424*Real.pi*(A/t)*δ^(9/25 : ℝ))) := by
  have hU : 0 < t*δ^(1/10 : ℝ) := mul_pos ht (Real.rpow_pos_of_pos hδ _)
  rw [← ENNReal.ofReal_inv_of_pos hU, ← ENNReal.ofReal_pow (inv_nonneg.mpr hU.le)]
  have hp : 0 ≤ 156*δ/δ^(1/5 : ℝ) := by positivity
  have hp' : 0 ≤ 2*(200*δ/(δ^(1/5 : ℝ))^2)*(1+(H*t*δ^(-(1/50 : ℝ)))/(t*δ^(1/10 : ℝ))) := by positivity
  rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul (mul_nonneg hp hM0),
    ← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6*Real.pi by positivity),
    ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hp'),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hU.le),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hfirst : (t*δ^(1/10 : ℝ))⁻¹^2 * (156*δ/δ^(1/5 : ℝ)*M*M) ≤
      156*(A/t)^2*δ^(14/25 : ℝ) := by
    calc
      _ ≤ (t*δ^(1/10 : ℝ))⁻¹^2 *
          (156*δ/δ^(1/5 : ℝ)*(A*δ^(-(1/50 : ℝ)))*(A*δ^(-(1/50 : ℝ)))) := by gcongr
      _ = _ := by rw [← first_power_identity hδ]; simp only [mul_inv_rev]; ring
  have hratio : (H*t*δ^(-(1/50 : ℝ)))/(t*δ^(1/10 : ℝ)) = H*(δ^(-(1/50 : ℝ))/δ^(1/10 : ℝ)) := by
    field_simp
  have hsecond : (t*δ^(1/10 : ℝ))⁻¹ *
      (6*Real.pi*(2*(200*δ/(δ^(1/5 : ℝ))^2)*(1+(H*t*δ^(-(1/50 : ℝ)))/(t*δ^(1/10 : ℝ))))*M) ≤
      (1+H)*(2400*Real.pi*(A/t)*δ^(9/25 : ℝ)) := by
    calc
      _ ≤ (t*δ^(1/10 : ℝ))⁻¹ *
          (6*Real.pi*(2*(200*δ/(δ^(1/5 : ℝ))^2)*(1+(H*t*δ^(-(1/50 : ℝ)))/(t*δ^(1/10 : ℝ))))*(A*δ^(-(1/50 : ℝ)))) := by gcongr
      _ = 2400*Real.pi*(A/t)*δ^(12/25 : ℝ)+H*(2400*Real.pi*(A/t)*δ^(9/25 : ℝ)) := by
        rw [hratio, ← third_power_identity hδ, ← second_power_identity hδ]
        simp only [mul_inv_rev]
        ring
      _ ≤ 2400*Real.pi*(A/t)*δ^(9/25 : ℝ)+H*(2400*Real.pi*(A/t)*δ^(9/25 : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num : (9/25 : ℝ) ≤ 12/25))
          (by positivity : 0 ≤ 2400*Real.pi*(A/t))) le_rfl
      _ = _ := by ring
  have hfirst' : 156*(A/t)^2*δ^(14/25 : ℝ) ≤ (1+H)*(156*(A/t)^2*δ^(14/25 : ℝ)) :=
    le_mul_of_one_le_left (by positivity) (by linarith)
  have hextra : (1+H)*(2400*Real.pi*(A/t)*δ^(9/25 : ℝ)) ≤
      (1+H)*(2424*Real.pi*(A/t)*δ^(9/25 : ℝ)) := by gcongr; norm_num
  calc
    _ ≤ (1+H)*(156*(A/t)^2*δ^(14/25 : ℝ))+(1+H)*(2424*Real.pi*(A/t)*δ^(9/25 : ℝ)) :=
      add_le_add (hfirst.trans hfirst') (hsecond.trans hextra)
    _ = _ := by ring

lemma direction_start_identity {Cs κ A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    (1+216*Cs)/(A/t)^(1/100 : ℝ)*A+
      directionGapConstant Cs κ*t*(A/t)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) =
    t*((1+216*Cs)*(A/t)^(99/100 : ℝ)+
      directionGapConstant Cs κ*(A/t)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) := by
  have hq : 0 < A/t := div_pos hA ht
  have he : (A/t)/(A/t)^(1/100 : ℝ) = (A/t)^(99/100 : ℝ) := by
    have hh := Real.rpow_sub hq (1 : ℝ) (1/100 : ℝ)
    norm_num at hh
    exact hh.symm
  have hAt : t*(A/t) = A := by field_simp
  calc
    _ = t*((1+216*Cs)*((A/t)/(A/t)^(1/100 : ℝ))+
      directionGapConstant Cs κ*(A/t)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) := by
        rw [mul_add]
        congr 1
        · calc
            _ = (1+216*Cs)/(A/t)^(1/100 : ℝ)*(t*(A/t)) := by rw [hAt]
            _ = _ := by ring
        · ring
    _ = _ := by rw [he]

lemma exists_direction_parameters (Cs κ : ℝ) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1/4 ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ d₀ → δ ≤ (δ^(1/5 : ℝ))^2/1600) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
        (1+216*Cs)*δ^(99/100 : ℝ)+
          directionGapConstant Cs κ*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) ≤ 1) := by
  obtain ⟨d,hd,hdq,hgeom⟩ := exists_admissible_width
  have ht : Tendsto (fun δ : ℝ => (1+216*Cs)*δ^(99/100 : ℝ)+
      directionGapConstant Cs κ*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) (𝓝 0) (𝓝 0) := by
    have h1 := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 99/100)).tendsto 0
    have h2 := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1/10)).tendsto 0
    simpa using (h1.const_mul (1+216*Cs)).add ((h2.const_mul (directionGapConstant Cs κ)).div_const _)
  obtain ⟨l,u,hu,hs⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  let d₀ := min d (u/2)
  have hd0 : 0 < d₀ := lt_min hd (by linarith [hu.2])
  refine ⟨d₀,hd0,(min_le_left _ _).trans hdq,fun δ hδ hδd => hgeom δ hδ (hδd.trans (min_le_left _ _)), ?_⟩
  intro δ hδ hδd
  apply le_of_lt
  apply hs
  exact ⟨lt_trans hu.1 hδ, lt_of_le_of_lt hδd ((min_le_right _ _).trans_lt (by linarith [hu.2]))⟩

end DiskScales

namespace DiskScales

lemma directionTailConstant_pos {Cs κ : ℝ} (hCs : 0 ≤ Cs) (hκ : 0 < κ) :
    0 < directionTailConstant Cs κ := by
  unfold directionTailConstant
  have hh := errorGapConstant_pos hCs
  exact mul_pos (by positivity) sizeTailConstant_pos

end DiskScales

namespace LocalCancellation
open DiskKernels DiskMoments DiskGeometry DiskScales

/-- A genuine superlevel bound with exponent 34/25 > 1 for all neighborhood
maxima, independent of the number of positive or cancelling pieces. -/
theorem direction_tail {Cs κ : ℝ} (hCs : 0 ≤ Cs) (hκ : 0 < κ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ {ι : Type*} [Fintype ι] {e : ℂ} (a : ConeDensity e κ)
      (b : ι → ErrorPiece Cs), ‖e‖ = 1 →
      0 < errorPrice b (1/100) → ∀ t : ℝ, L*errorPrice b (1/100) ≤ t →
      ∀ g : ℂ → ℝ, ContDiff ℝ 1 g →
      ∃ E : Set ℂ, MeasurableSet E ∧
        volume E ≤ ENNReal.ofReal (directionTailConstant Cs κ*(errorPrice b (1/100)/t)^(34/25 : ℝ)) ∧
        ∀ x ∉ E,
          (∀ᵐ y, y ∈ Metric.ball x 3 → a.density y+∑ j, (b j).density y = gradient g y) →
          ∀ r, NeighborhoodRadius g x r →
            max 0 (-inner ℝ e (∫ y in Metric.ball x r, gradient g y)) ≤ t := by
  obtain ⟨d₀,hd0,hdq,hgeom,hsmall⟩ := exists_direction_parameters Cs κ
  have hL : 1 ≤ (1 : ℝ)/d₀ := (le_div_iff₀ hd0).mpr (by linarith)
  refine ⟨1/d₀,hL,?_⟩
  intro ι _ e a b he hA t ht g hg
  let A := errorPrice b (1/100)
  let H := errorGapConstant Cs/κ
  have hH : 0 ≤ H := div_nonneg (errorGapConstant_pos hCs).le hκ.le
  have hH1 : 0 ≤ 1+H := by linarith
  have hAt : A ≤ t := (le_mul_of_one_le_left hA.le hL).trans ht
  have ht0 : 0 < t := lt_of_lt_of_le hA hAt
  have hqd : A/t ≤ d₀ := by
    apply (div_le_iff₀ ht0).mpr
    have hh : A/d₀ ≤ t := by simpa only [A,one_div, div_eq_mul_inv, mul_comm, mul_one] using ht
    have hh' := (div_le_iff₀ hd0).mp hh
    linarith
  have hq0 : 0 < A/t := div_pos hA ht0
  have hq1 : A/t ≤ 1 := by linarith
  have hqq : A/t ≤ 1/4 := hqd.trans hdq
  obtain ⟨E,hE,hEv,hEst⟩ := direction_raw a b he hκ hCs hq0 hqq
    (fun δ hδ hδq => hgeom δ hδ (hδq.trans hqd)) ht0 hAt hg
  refine ⟨E,hE,?_,?_⟩
  · apply hEv.trans
    calc
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (1+H)*ENNReal.ofReal
          (156*(A/t)^2*(width (A/t) n)^(14/25 : ℝ)+
            2424*Real.pi*(A/t)*(width (A/t) n)^(9/25 : ℝ)) := by
        apply ENNReal.tsum_le_tsum
        intro n
        rw [← ENNReal.ofReal_mul hH1]
        apply direction_shell_tail_scaled hA.le ht0 (width_pos hq0 n)
          ((width_le hq0.le n).trans hq1) (coarseMass_nonneg b _ _) hH
        have hw0 := width_pos hq0 n
        have hh := coarseMass_bound b (by norm_num : (0 : ℝ) ≤ 1/100) hw0
        norm_num at hh
        rw [Real.rpow_neg hw0.le]
        exact hh
      _ = ENNReal.ofReal (1+H)*ENNReal.ofReal
          ((156/(1-(1/2 : ℝ)^(14/25 : ℝ)))*(A/t)^(64/25 : ℝ)+
            (2424*Real.pi/(1-(1/2 : ℝ)^(9/25 : ℝ)))*(A/t)^(34/25 : ℝ)) := by
        rw [ENNReal.tsum_mul_left,geometric_tail_sum hA.le ht0 hq0.le, starting_width_tail hA ht0]
      _ ≤ ENNReal.ofReal (1+H)*ENNReal.ofReal (sizeTailConstant*(A/t)^(34/25 : ℝ)) := by
        gcongr
        exact collapse_size_tail hq0 hq1
      _ = _ := by rw [← ENNReal.ofReal_mul hH1]; congr 1; dsimp only [directionTailConstant,H,A]; ring
  · intro x hx hh r hr
    apply (hEst x hx hh r hr).trans
    rw [direction_start_identity hA ht0]
    exact (mul_le_mul_of_nonneg_left (hsmall _ hq0 hqd) ht0.le).trans_eq (mul_one t)

lemma cone_ball_nonneg {e : ℂ} {κ : ℝ} (a : ConeDensity e κ) (hκ : 0 ≤ κ) (x : ℂ) (r : ℝ) :
    0 ≤ inner ℝ e (∫ y in Metric.ball x r, a.density y) := by
  rw [← integral_inner a.integrable.integrableOn e]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_of_ae a.cone] with y hy
  exact (mul_nonneg hκ (norm_nonneg _)).trans hy

/-- Full Borel integrable directional price. This is the hard local
cancellation estimate, not an assumed maximal-operator endpoint. -/
theorem direction_majorant {Cs κ : ℝ} (hCs : 0 ≤ Cs) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] {e : ℂ} (a : ConeDensity e κ)
      (b : ι → ErrorPiece Cs), ‖e‖ = 1 →
      ∀ g : ℂ → ℝ, ContDiff ℝ 1 g → ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
      ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
        (∫⁻ x in Q, F x) ≤ ENNReal.ofReal (C*errorPrice b (1/100)) ∧
        ∀ x, (∀ᵐ y, y ∈ Metric.ball x 3 → a.density y+∑ j, (b j).density y = gradient g y) →
          ∀ r, NeighborhoodRadius g x r →
            ENNReal.ofReal (max 0 (-inner ℝ e (∫ y in Metric.ball x r, gradient g y))) ≤ F x := by
  obtain ⟨L,hL,hdir⟩ := direction_tail hCs hκ
  let c : ℝ := (1/2 : ℝ)^(34/25 : ℝ)
  have hc : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hc1 : 2*c < 1 := by
    have hh := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1/2)
      (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 34/25)
    norm_num at hh
    linarith
  let C := L*(1+2*directionTailConstant Cs κ/(1-2*c))
  have hD := directionTailConstant_pos hCs hκ
  have hC : 0 < C := mul_pos (by linarith) (by
    have := sub_pos.mpr hc1
    positivity)
  refine ⟨C,hC,?_⟩
  intro ι _ e a b he g hg Q hQ
  let A := errorPrice b (1/100)
  by_cases hAz : A = 0
  · refine ⟨0,measurable_const,?_,?_⟩
    · simp only [Pi.zero_apply, lintegral_zero, A, hAz, mul_zero, ENNReal.ofReal_zero, le_refl]
    · intro x hh r hr
      have hz := errorPrice_zero b hAz
      have hs : (∑ j, ∫ y in Metric.ball x r, (b j).density y) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        exact integral_eq_zero_of_ae (ae_restrict_of_ae (hz j))
      have hb := mixed_ball_pairing_decomposition b a.integrable x (by linarith [hr.1.2] : r ≤ 3) hh
      rw [← hb,hs,add_zero,max_eq_left (neg_nonpos.mpr (cone_ball_nonneg a hκ.le x r)),ENNReal.ofReal_zero]
      exact le_refl _
  · have hA : 0 < A := lt_of_le_of_ne (errorPrice_nonneg b _) (Ne.symm hAz)
    have ht : 0 < L*A := mul_pos (by linarith) hA
    have hts (n : ℕ) : L*A ≤ L*A*2^n := le_mul_of_one_le_right ht.le (one_le_pow₀ (by norm_num))
    choose E hE hEv hbound using fun n : ℕ => hdir a b he hA (L*A*2^n) (hts n) g hg
    refine ⟨DyadicMajorant.price (L*A) E, DyadicMajorant.measurable_price _ hE,?_,?_⟩
    · have htail (n : ℕ) : volume (E n) ≤ ENNReal.ofReal (directionTailConstant Cs κ*c^n) := by
        apply (hEv n).trans
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ hD.le
        calc
          _ ≤ ((1/2 : ℝ)^n)^(34/25 : ℝ) := Real.rpow_le_rpow (by positivity) (dyadic_ratio hA hL n) (by norm_num)
          _ = c^n := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm (n : ℝ),
              Real.rpow_mul (by norm_num), Real.rpow_natCast]
      have hi := DyadicMajorant.lintegral_price_geometric volume (by norm_num : (0 : ℝ) ≤ 1) hQ ht.le
        hD.le hc hc1 hE htail
      convert hi using 1
      congr 1
      dsimp [C,A]
      ring
    · intro x hh r hr
      apply DyadicMajorant.majorizes ht
      intro n hn
      exact hbound n x hn hh r hr

end LocalCancellation

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.ScalarTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace ScalarCancellation
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {ι : Type*} [Fintype ι]

lemma roots_abs_mass (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    (∫ x, |roots μ w f k q x| ∂μ) = |∫ x, refined w f k q x ∂μ| := by
  cases k with
  | zero => exact (root_spec (hf q)).2.2.1
  | succ k =>
    have hs := root_spec (integrable_finsetSum Finset.univ
      (fun s _ => (roots_integrable w hf k s).const_mul (w k q s)))
    change (∫ x, |root μ _ x| ∂μ) = _
    rw [hs.2.2.1,← hs.2.1]
    exact congrArg abs (roots_mass w hf (k+1) q)

/-- The whole scalar cancellation tree is built by backward splitting. Each
nonterminal zero-mass piece costs at most its positive refinement norm defect. -/
theorem errors_cost (w : ℕ → ι → ι → ℝ) (hw : ∀ k q s, 0 ≤ w k q s)
    {f : ι → α → ℝ} (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    (∫ x, |errors μ w f (k+1) q x| ∂μ) ≤
      (∑ s, w k q s*|∫ x, refined w f k s x ∂μ|)-|∫ x, refined w f (k+1) q x ∂μ| := by
  have hi : Integrable (fun x => ∑ s, w k q s*roots μ w f k s x) μ :=
    integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _)
  have hs := root_spec hi
  change (∫ x, |(∑ s, w k q s*roots μ w f k s x)-root μ _ x| ∂μ) ≤ _
  rw [hs.2.2.2.1]
  have hm : (∫ x, ∑ s, w k q s*roots μ w f k s x ∂μ) = ∫ x, refined w f (k+1) q x ∂μ := by
    rw [← hs.2.1]
    exact roots_mass w hf (k+1) q
  rw [hm]
  apply sub_le_sub_right
  calc
    _ ≤ ∫ x, ∑ s, w k q s*|roots μ w f k s x| ∂μ := by
      apply integral_mono hi.abs (integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).abs.const_mul _))
      intro x
      calc
        _ ≤ ∑ s, |w k q s*roots μ w f k s x| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp_rw [abs_mul,abs_of_nonneg (hw k q _)]
    _ = _ := by
      rw [integral_finsetSum _ (fun s _ => (roots_integrable w hf k s).abs.const_mul _)]
      simp_rw [integral_const_mul,roots_abs_mass w hf]

lemma errors_terminal_cost (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (q : ι) :
    (∫ x, |errors μ w f 0 q x| ∂μ) = (∫ x, |f q x| ∂μ)-|∫ x, f q x ∂μ| :=
  (root_spec (hf q)).2.2.2.1

end ScalarCancellation

namespace ScalarCancellation
open Finset
variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι]

/-- Exact expansion in a coherent family of refinement coefficients. The
finite zero-mass pieces are the explicitly constructed `errors`, not merely
scalar mass certificates. -/
theorem telescoped_decomposition [DecidableEq ι] (w : ℕ → ι → ι → ℝ) (f : ι → α → ℝ)
    (Λ : ℕ → ℕ → ι → ι → ℝ)
    (hdiag : ∀ k q s, Λ k k q s = if q = s then 1 else 0)
    (hstep : ∀ k j q s, j ≤ k → Λ (k+1) j q s = ∑ a, w k q a*Λ k j a s)
    (k : ℕ) (q : ι) (x : α) :
    refined w f k q x = roots μ w f k q x +
      ∑ j ∈ range (k+1), ∑ s, Λ k j q s*errors μ w f j s x := by
  classical
  induction k generalizing q with
  | zero =>
    simp only [Nat.zero_add,Finset.range_one,sum_singleton,hdiag,ite_mul,one_mul,zero_mul]
    rw [sum_ite_eq univ q]
    simp only [Finset.mem_univ,ite_true,errors,refined]
    ring
  | succ k ih =>
    rw [sum_range_succ]
    have hlast : (∑ s, Λ (k+1) (k+1) q s*errors μ w f (k+1) s x) = errors μ w f (k+1) q x := by
      simp only [hdiag,ite_mul,one_mul,zero_mul]
      simp
    rw [hlast,errors,refined]
    simp_rw [ih]
    simp only [mul_add,sum_add_distrib]
    have hsum : (∑ a, w k q a*(∑ j ∈ range (k+1), ∑ s, Λ k j a s*errors μ w f j s x)) =
        ∑ j ∈ range (k+1), ∑ s, Λ (k+1) j q s*errors μ w f j s x := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      rw [sum_comm]
      apply sum_congr rfl
      intro s _
      rw [hstep k j q s (Nat.le_of_lt_succ (mem_range.mp hj)),sum_mul]
      apply sum_congr rfl
      intro a _
      ring
    rw [hsum]
    ring

end ScalarCancellation

open MeasureTheory Set
open scoped ENNReal NNReal Topology
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Kernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace DyadicHats

lemma step_column (q : ℤ × ℤ) : (∑' p : ℤ × ℤ, step p q) = 1 := by
  calc
    _ = ∑' p, hat 1 p (((q.1:ℝ)/2 : ℂ)+((q.2:ℝ)/2 : ℂ)*Complex.I) := by
      apply tsum_congr
      intro p
      simp [step,hat]
    _ = 1 := tsum_hat _ _

end DyadicHats

open MeasureTheory Set Metric
open scoped ENNReal NNReal
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section

open Finset
open scoped RealInnerProductSpace
noncomputable section
namespace FiniteLabels
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma law_le_one (μ : Law ι) (i : ι) : μ i ≤ 1 := by
  rw [← μ.total]
  exact single_le_sum (fun j _ => μ.nonneg j) (mem_univ i)

lemma move_apply (μ : Law ι) (P : ι → Law κ) (j : κ) :
    move μ P j = ∑ i, μ i*P i j := rfl

end FiniteLabels

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace VectorRefinement

/-- Exact quadratic defect of a positive vector refinement, including zero parent mass. -/
theorem quadratic_defect {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w a : ι → ℝ) (θ : ι → E) (n : E) (A : ℝ)
    (hn : ‖n‖ = 1) (hθ : ∀ i, ‖θ i‖ = 1)
    (href : A • n = ∑ i, (w i*a i) • θ i) :
    (∑ i, w i*a i)-A = (1/2:ℝ)*∑ i, w i*a i*‖θ i-n‖^2 := by
  have hinner : A = ∑ i, w i*a i*⟪θ i,n⟫ := by
    have h := congrArg (fun v : E => ⟪v,n⟫) href
    simpa only [real_inner_smul_left,sum_inner,real_inner_self_eq_norm_sq,hn,one_pow,mul_one] using h
  rw [hinner,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_sub_sq_real,hθ i,hn]
  ring

lemma sq_norm_triangle {E : Type*} [SeminormedAddCommGroup E] (x y z : E) :
    ‖x-z‖^2 ≤ 2*(‖x-y‖^2+‖z-y‖^2) := by
  have h := norm_sub_le_norm_sub_add_norm_sub x y z
  rw [norm_sub_rev y z] at h
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr h
  nlinarith [sq_nonneg (‖x-y‖-‖z-y‖)]

/-- Two sufficiently represented children cannot have a large angular disagreement
without spending the actual parent's triangle defect. -/
theorem pair_defect_bound {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w a : ι → ℝ) (θ : ι → E) (n : E) (A : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i)
    (hn : ‖n‖ = 1) (hθ : ∀ i, ‖θ i‖ = 1)
    (href : A • n = ∑ i, (w i*a i) • θ i)
    {q s : ι} (hwaq : 1/4 ≤ w q) (hwas : 9/64 ≤ w s) (has : a q ≤ a s) :
    a q*‖θ q-θ s‖^2 ≤ 48*((∑ i, w i*a i)-A) := by
  let D := (∑ i, w i*a i)-A
  have hD := quadratic_defect w a θ n A hn hθ href
  have hi (i : ι) : w i*a i*‖θ i-n‖^2 ≤ 2*D := by
    have hs : w i*a i*‖θ i-n‖^2 ≤ ∑ j, w j*a j*‖θ j-n‖^2 :=
      Finset.single_le_sum (fun j _ => mul_nonneg (mul_nonneg (hw j) (ha j)) (sq_nonneg ‖θ j-n‖)) (Finset.mem_univ i)
    dsimp [D]
    linarith
  have hD0 : 0 ≤ D := by
    have hs : 0 ≤ ∑ i, w i*a i*‖θ i-n‖^2 := Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (hw i) (ha i)) (sq_nonneg _)
    dsimp [D]; linarith
  have hq : a q*‖θ q-n‖^2 ≤ 8*D := by
    have hm := mul_le_mul_of_nonneg_right hwaq (mul_nonneg (ha q) (sq_nonneg ‖θ q-n‖))
    nlinarith [hi q]
  have hs : a q*‖θ s-n‖^2 ≤ (128/9:ℝ)*D := by
    have hm := mul_le_mul_of_nonneg_right hwas (mul_nonneg (ha s) (sq_nonneg ‖θ s-n‖))
    have hmas := mul_le_mul_of_nonneg_right has (sq_nonneg ‖θ s-n‖)
    nlinarith [hi s]
  have ht := mul_le_mul_of_nonneg_left (sq_norm_triangle (θ q) n (θ s)) (ha q)
  change _ ≤ 48*D
  nlinarith

end VectorRefinement

open MeasureTheory Set
open scoped ENNReal NNReal Topology
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Refinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

namespace DiskMoments

lemma hasFDerivAt_signedAverage {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    HasFDerivAt (fun x => signedAverage g x t)
      ((1/Real.pi) • ∫ z in Metric.ball 0 1, fderiv ℝ g (x+t • z)) x := by
  let F : ℂ → ℂ → ℝ := fun x z => g (x+t • z)
  have hFi : IntegrableOn (F x) (Metric.ball 0 1) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 1)
      (hg.continuous.comp (by fun_prop)).continuousOn).mono_set Metric.ball_subset_closedBall
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Metric.ball (0:ℂ) 1)) (F := F)
    (F' := fun x z => fderiv ℝ g (x+t • z)) (bound := fun _ => D)
    (s := univ) (x₀ := x) univ_mem
    (Eventually.of_forall (fun x => (hg.continuous.comp (by fun_prop)).aestronglyMeasurable))
    hFi ((hg.continuous_fderiv one_ne_zero).comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ (fun z x _ => hD (x+t • z))) (integrableOn_const (by finiteness))
    (ae_of_all _ (fun z x _ => by
      simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq,F] using
        (hg.differentiable one_ne_zero (x+t • z)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (t • z))))
  convert! hd.const_mul (1/Real.pi) using 1
  · funext y
    simpa only [F,div_eq_mul_inv,one_div,mul_comm,mul_one] using signedAverage_fixedDomain g y ht

end DiskMoments

namespace DyadicHats

lemma boxNorm_le_norm (x : ℂ) : boxNorm x ≤ ‖x‖ :=
  max_le (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
lemma boxNorm_add_le (x y : ℂ) : boxNorm (x+y) ≤ boxNorm x+boxNorm y := by
  apply max_le
  · exact (abs_add_le _ _).trans (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact (abs_add_le _ _).trans (add_le_add (le_max_right _ _) (le_max_right _ _))
lemma boxNorm_neg (x : ℂ) : boxNorm (-x) = boxNorm x := by simp [boxNorm]
lemma boxNorm_sub_comm (x y : ℂ) : boxNorm (x-y) = boxNorm (y-x) := by
  rw [← neg_sub y x,boxNorm_neg]

/-- Globally uniform spatial Lipschitz bound for the literal bilinear hats. -/
lemma lipschitz_hat {r : ℝ} (hr : 0 < r) (p : ℤ × ℤ) :
    LipschitzWith (Real.toNNReal (2/r)) (hat r p) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  let a := tent (x.re/r-p.1)
  let b := tent (x.im/r-p.2)
  let c := tent (y.re/r-p.1)
  let d := tent (y.im/r-p.2)
  have h1 : |a-c| ≤ ‖x-y‖/r := by
    have h := lipschitz_tent.dist_le_mul (x.re/r-p.1) (y.re/r-p.1)
    simp only [Real.dist_eq,NNReal.coe_one,one_mul,sub_sub_sub_cancel_right,← sub_div,
      abs_div,abs_of_pos hr] at h
    exact h.trans (div_le_div_of_nonneg_right (Complex.abs_re_le_norm (x-y)) hr.le)
  have h2 : |b-d| ≤ ‖x-y‖/r := by
    have h := lipschitz_tent.dist_le_mul (x.im/r-p.2) (y.im/r-p.2)
    simp only [Real.dist_eq,NNReal.coe_one,one_mul,sub_sub_sub_cancel_right,← sub_div,
      abs_div,abs_of_pos hr] at h
    exact h.trans (div_le_div_of_nonneg_right (Complex.abs_im_le_norm (x-y)) hr.le)
  have hab : |a*b-c*d| ≤ |a-c|+|b-d| := by
    calc
      _ = |(a-c)*b+c*(b-d)| := by congr 1; ring
      _ ≤ |(a-c)*b|+|c*(b-d)| := abs_add_le _ _
      _ = |a-c| *b+c*|b-d| := by rw [abs_mul,abs_mul,abs_of_nonneg (tent_nonneg _),abs_of_nonneg (tent_nonneg _)]
      _ ≤ |a-c| *1+1*|b-d| := add_le_add
        (mul_le_mul_of_nonneg_left (tent_le_one _) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (tent_le_one _) (abs_nonneg _))
      _ = _ := by ring
  change |a*b-c*d| ≤ _
  rw [Real.coe_toNNReal (2/r) (by positivity),dist_eq_norm]
  calc
    _ ≤ ‖x-y‖/r+‖x-y‖/r := hab.trans (add_le_add h1 h2)
    _ = _ := by ring

end DyadicHats

namespace DyadicHats
open scoped BigOperators

lemma scalarMass_le_integral {h : ℂ → ℂ} (r : ℝ) (p : ℤ × ℤ) :
    scalarMass h r p ≤ ∫ y, hat r p y * ‖h y‖ := by
  unfold scalarMass vectorMass
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hat_nonneg _ _ _)] using
    norm_integral_le_integral_norm (fun y => hat r p y • h y)

/-- Any finite set of roots carries at most the total L1 density, uniformly
in the scale. This proves the full-grid mass budget once finite support is used. -/
lemma sum_scalarMass_le {h : ℂ → ℂ} (hh : Integrable h) (r : ℝ) (S : Finset (ℤ × ℤ)) :
    ∑ p ∈ S, scalarMass h r p ≤ ∫ y, ‖h y‖ := by
  have hi (p : ℤ × ℤ) : Integrable (fun y => hat r p y * ‖h y‖) := by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hat_nonneg _ _ _)] using
      (integrable_hat_smul hh r p).norm
  calc
    _ ≤ ∑ p ∈ S, ∫ y, hat r p y * ‖h y‖ := Finset.sum_le_sum (fun p _ => scalarMass_le_integral r p)
    _ = ∫ y, ∑ p ∈ S, hat r p y * ‖h y‖ := (integral_finsetSum _ (fun p _ => hi p)).symm
    _ ≤ ∫ y, ‖h y‖ := by
      apply integral_mono (integrable_finsetSum _ (fun p _ => hi p)) hh.norm
      intro y
      change (∑ p ∈ S, hat r p y * ‖h y‖) ≤ ‖h y‖
      rw [← Finset.sum_mul]
      have hs := Summable.sum_le_tsum S (fun p _ => hat_nonneg r p y) (summable_hat r y)
      rw [tsum_hat] at hs
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (norm_nonneg (h y))

end DyadicHats

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
noncomputable section

open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

namespace DyadicHats

lemma parent_in_box {N : ℕ} {p q : ℤ × ℤ} (hq : q ∈ indexBox N) (hpq : step p q ≠ 0) :
    p ∈ indexBox N := by
  have hq1 : -(N:ℤ) ≤ q.1 ∧ q.1 ≤ N := Finset.mem_Icc.mp (Finset.mem_product.mp hq).1
  have hq2 : -(N:ℤ) ≤ q.2 ∧ q.2 ≤ N := Finset.mem_Icc.mp (Finset.mem_product.mp hq).2
  have hh : 0 < step p q := lt_of_le_of_ne (step_nonneg p q) (Ne.symm hpq)
  have h1 := (tent_pos_iff _).mp (pos_of_mul_pos_left hh (tent_nonneg _))
  have h2 := (tent_pos_iff _).mp (pos_of_mul_pos_right hh (tent_nonneg _))
  have hbound (j k : ℤ) (hk : -(N:ℤ) ≤ k ∧ k ≤ N) (ha : |(k:ℝ)/2-j| < 1) :
      j ∈ Finset.Icc (-(N:ℤ)) N := by
    have hlo : -(N:ℝ) ≤ k := by exact_mod_cast hk.1
    have hhi : (k:ℝ) ≤ N := by exact_mod_cast hk.2
    have hj := abs_lt.mp ha
    simp only [Finset.mem_Icc]
    constructor
    · by_contra hn
      have : j ≤ -(N:ℤ)-1 := by omega
      have : (j:ℝ) ≤ -(N:ℝ)-1 := by exact_mod_cast this
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    · by_contra hn
      have : (N:ℤ)+1 ≤ j := by omega
      have : (N:ℝ)+1 ≤ j := by exact_mod_cast this
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
  exact Finset.mem_product.mpr ⟨hbound _ _ hq1 h1,hbound _ _ hq2 h2⟩

/-- Restriction to a finite box retains the exact column normalization of the
positive dyadic refinement matrix; it does not normalize its rows. -/
lemma grid_step_column (N : ℕ) (q : Grid N) : (∑ p : Grid N, step p q) = 1 := by
  have he := step_column q.val
  rw [tsum_eq_sum (s := indexBox N)] at he
  · exact (Finset.sum_coe_sort (indexBox N) (fun p => step p q)).trans he
  · intro p hp
    by_contra hn
    exact hp (parent_in_box q.property hn)

lemma density_partition_grid {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (x : ℂ) :
    (∑ p : Grid N, hat r p x*h x) = h x := by
  have he : (∑' p : ℤ × ℤ, hat r p x*h x) = ∑ p ∈ indexBox N, hat r p x*h x :=
    tsum_eq_sum (fun p hp => hat_mul_zero_outside hr hN hs hp x)
  rw [Finset.sum_coe_sort (indexBox N) (fun p => hat r p x*h x),← he,
    tsum_mul_right,tsum_hat,one_mul]

end DyadicHats

end
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.DirectionLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

noncomputable section

namespace DyadicHats
open scoped BigOperators

variable {N : ℕ}

lemma densityRoot_abs_mass {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    (∫ x, |densityRoot N r h k q x|) = |∫ x, hat (scale r k) q x*h x| := by
  have he := ScalarCancellation.roots_abs_mass (weights N) (pieces_integrable hh r) k q
  simpa only [densityRoot,refined_eq_density hr hR hN hs] using he

lemma densityError_cost {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    (∫ x, |densityError N r h k q x|) ≤ 2*densityDefect N r h k q := by
  cases k with
  | zero =>
    have he := ScalarCancellation.errors_terminal_cost (weights N) (pieces_integrable hh r) q
    simp only [pieces,abs_mul,abs_of_nonneg (hat_nonneg r q _)] at he
    rw [densityDefect]
    change (∫ x, |ScalarCancellation.errors volume (weights N) (pieces N r h) 0 q x|) ≤ _
    rw [he]
    linarith
  | succ k =>
    have he := ScalarCancellation.errors_cost (weights N) (fun _ p s => step_nonneg p s)
      (pieces_integrable hh r) k q
    simp only [refined_eq_density hr hR hN hs,weights] at he
    change (∫ x, |ScalarCancellation.errors volume (weights N) (pieces N r h) (k+1) q x|) ≤ _
    rw [densityDefect]
    linarith

end DyadicHats

namespace DyadicHats
open Finset

lemma coeff_nonneg (N d : ℕ) (p q : Grid N) : 0 ≤ coeff N d p q := by
  induction d generalizing p with
  | zero => simp only [coeff]; split_ifs <;> norm_num
  | succ d ih => exact sum_nonneg fun a _ => mul_nonneg (step_nonneg p a) (ih a)

lemma coeff_column (N d : ℕ) (q : Grid N) : (∑ p : Grid N, coeff N d p q) = 1 := by
  induction d with
  | zero => simp [coeff]
  | succ d ih =>
    simp only [coeff]
    rw [Finset.sum_comm]
    simp_rw [← sum_mul,grid_step_column,one_mul]
    exact ih

/-- All lower-level error densities, with their actual coherent coefficients,
reconstruct the genuine coarse hat density exactly. -/
theorem density_decomposition {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    (k : ℕ) (q : Grid N) (x : ℂ) :
    hat (scale r k) q x*h x = densityRoot N r h k q x+
      ∑ j ∈ range (k+1), ∑ s : Grid N, coeff N (k-j) q s*densityError N r h j s x := by
  rw [← refined_eq_density hr hR hN hs]
  apply ScalarCancellation.telescoped_decomposition (weights N) (pieces N r h)
    (fun k j p s => coeff N (k-j) p s)
  · intro j p s
    simp only [Nat.sub_self,coeff]
  · intro k j p s hj
    rw [show k+1-j = k-j+1 by omega,coeff]
    rfl

lemma terminal_abs_sum {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) :
    (∑ q : Grid N, ∫ x, hat r q x*|h x|) = ∫ x, |h x| := by
  rw [← integral_finsetSum (Finset.univ : Finset (Grid N)) (fun q _ => integrable_hat_mul hh.abs r q)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  apply density_partition_grid hr hN
  intro y hy
  exact hs y (fun hz => hy (by rw [hz,abs_zero]))

lemma densityDefect_sum_succ (N : ℕ) (r : ℝ) (h : ℂ → ℝ) (k : ℕ) :
    (∑ q : Grid N, densityDefect N r h (k+1) q) =
      ((∑ q : Grid N, |∫ x, hat (scale r k) q x*h x|)-
       (∑ q : Grid N, |∫ x, hat (scale r (k+1)) q x*h x|))/2 := by
  simp only [densityDefect]
  rw [← sum_div,sum_sub_distrib]
  congr 2
  rw [Finset.sum_comm]
  simp_rw [← sum_mul,grid_step_column,one_mul]

/-- Exact telescoping of the literal scalar defects, including the finest
terminal split. No depth-dependent or terminal remainder is discarded. -/
theorem densityDefect_budget_eq {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (n : ℕ) :
    (∑ k ∈ range (n+1), ∑ q : Grid N, densityDefect N r h k q) =
      ((∫ x, |h x|)-(∑ q : Grid N, |∫ x, hat (scale r n) q x*h x|))/2 := by
  induction n with
  | zero =>
    simp only [Nat.zero_add,range_one,sum_singleton,densityDefect,
      scale,pow_zero,one_mul]
    rw [← sum_div,sum_sub_distrib]
    rw [terminal_abs_sum hr hN hh hs]
  | succ n ih =>
    rw [sum_range_succ,ih,densityDefect_sum_succ]
    ring

lemma densityDefect_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    0 ≤ densityDefect N r h k q := by
  have he := densityError_cost hr hR hN hh hs k q
  have hn : 0 ≤ ∫ x, |densityError N r h k q x| := integral_nonneg (fun x => abs_nonneg _)
  linarith

lemma densityDefect_budget {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (n : ℕ) :
    (∑ k ∈ range (n+1), ∑ q : Grid N, densityDefect N r h k q) ≤ (∫ x, |h x|)/2 := by
  rw [densityDefect_budget_eq hr hN hh hs]
  have he : 0 ≤ ∑ q : Grid N, |∫ x, hat (scale r n) q x*h x| := sum_nonneg fun _ _ => abs_nonneg _
  linarith

lemma scalarPrice_sum (N : ℕ) (r : ℝ) (h : ℂ → ℝ) (ρ : ℝ) (k : ℕ) :
    (∑ q : Grid N, scalarPrice N r h ρ k q) =
      ∑ j ∈ range (k+1), ρ^(k-j)*∑ s : Grid N, densityDefect N r h j s := by
  simp only [scalarPrice]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro j _
  rw [← mul_sum,Finset.sum_comm]
  congr 1
  simp_rw [← sum_mul,coeff_column,one_mul]

end DyadicHats

namespace DyadicHats
open Finset

lemma discount_recurrence (ρ : ℝ) (a : ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ range (k+2), ρ^(k+1-j)*a j) =
      a (k+1)+ρ*(∑ j ∈ range (k+1), ρ^(k-j)*a j) := by
  rw [sum_range_succ]
  simp only [Nat.sub_self,pow_zero,one_mul,mul_sum]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [show k+1-j = (k-j)+1 by have := mem_range.mp hj; omega,pow_succ]
  ring

lemma triangle_discount_bound {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (n : ℕ) :
    (∑ k ∈ range (n+1), ∑ j ∈ range (k+1), ρ^(k-j)*a j) ≤
      (1-ρ)⁻¹*∑ j ∈ range (n+1), a j := by
  let b : ℕ → ℝ := fun k => ∑ j ∈ range (k+1), ρ^(k-j)*a j
  have hb : ∀ k, 0 ≤ b k := fun k => sum_nonneg fun j _ => mul_nonneg (pow_nonneg hρ _) (ha j)
  have hi : ∀ n, (1-ρ)*(∑ k ∈ range (n+1), b k) =
      (∑ j ∈ range (n+1), a j)-ρ*b n := by
    intro n
    induction n with
    | zero => simp [b]; ring
    | succ n ih =>
      rw [sum_range_succ (f := b) (n := n+1),sum_range_succ (f := a) (n := n+1),mul_add,ih]
      have he : b (n+1) = a (n+1)+ρ*b n := discount_recurrence ρ a n
      rw [he]
      ring
  have hle : (1-ρ)*(∑ k ∈ range (n+1), b k) ≤ ∑ j ∈ range (n+1), a j := by
    rw [hi]
    exact sub_le_self _ (mul_nonneg hρ (hb n))
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ (sub_pos.mpr hρ1)).mpr (by rwa [mul_comm])

theorem scalarPrice_budget {N : ℕ} {r R ρ : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (n : ℕ) :
    (∑ k ∈ range (n+1), ∑ q : Grid N, scalarPrice N r h ρ k q) ≤
      (1-ρ)⁻¹*((∫ x, |h x|)/2) := by
  simp_rw [scalarPrice_sum]
  apply (triangle_discount_bound hρ hρ1
    (fun j => sum_nonneg fun q _ => densityDefect_nonneg hr hR hN hh hs j q) n).trans
  exact mul_le_mul_of_nonneg_left (densityDefect_budget hr hN hh hs n)
    (inv_nonneg.mpr (sub_nonneg.mpr hρ1.le))

end DyadicHats

namespace DyadicHats
open Finset

lemma activeIndices_card (r : ℝ) (x : ℂ) : (activeIndices r x).card ≤ 4 := by
  change (({⌊x.re/r⌋,⌊x.re/r⌋+1} : Finset ℤ) ×ˢ
    ({⌊x.im/r⌋,⌊x.im/r⌋+1} : Finset ℤ)).card ≤ 4
  rw [Finset.card_product]
  exact (Nat.mul_le_mul (card_insert_le ..) (card_insert_le ..)).trans (by simp)

lemma interpolate_eq_sum (r : ℝ) (f : ℤ × ℤ → ℝ) (x : ℂ)
    (S : Finset (ℤ × ℤ)) (hS : activeIndices r x ⊆ S) :
    interpolate r f x = ∑ p ∈ S, hat r p x*f p := by
  apply tsum_eq_sum
  intro p hp
  rw [hat_zero_of_not_active r x (fun hn => hp (hS hn)),zero_mul]

lemma interpolate_add (r : ℝ) (f g : ℤ × ℤ → ℝ) (x : ℂ) :
    interpolate r (fun p => f p+g p) x = interpolate r f x+interpolate r g x := by
  simp only [interpolate,mul_add]
  exact (summable_weighted_hat r x f).tsum_add (summable_weighted_hat r x g)

/-- Only eight tents can contribute to a difference of two interpolated values.
This is the quantitative global Lipschitz bound with no grid cardinality loss. -/
theorem interpolate_lipschitz {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    {f : ℤ × ℤ → ℝ} (hf : ∀ p, |f p| ≤ B) :
    LipschitzWith (Real.toNNReal (16*B/r)) (interpolate r f) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  let S := activeIndices r x ∪ activeIndices r y
  have hcard : S.card ≤ 8 := (Finset.card_union_le (activeIndices r x) (activeIndices r y)).trans
    (by have := activeIndices_card r x; have := activeIndices_card r y; omega)
  have hsum : |interpolate r f x-interpolate r f y| ≤
      (S.card:ℝ)*((2/r)*‖x-y‖*B) := by
    rw [interpolate_eq_sum r f x S subset_union_left,interpolate_eq_sum r f y S subset_union_right,
      ← sum_sub_distrib]
    calc
      _ ≤ ∑ p ∈ S, |hat r p x*f p-hat r p y*f p| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ S, (2/r)*‖x-y‖*B := by
        apply sum_le_sum
        intro p _
        rw [← sub_mul,abs_mul]
        have hb := (lipschitz_hat hr p).dist_le_mul x y
        rw [Real.dist_eq,Real.coe_toNNReal (2/r) (by positivity),dist_eq_norm] at hb
        exact mul_le_mul hb (hf p) (abs_nonneg _) (by positivity)
      _ = _ := by rw [sum_const,nsmul_eq_mul]
  rw [Real.dist_eq,Real.coe_toNNReal (16*B/r) (by positivity),dist_eq_norm]
  have hcard' : (S.card:ℝ) ≤ 8 := by exact_mod_cast hcard
  calc
    _ ≤ (8:ℝ)*((2/r)*‖x-y‖*B) := hsum.trans (mul_le_mul_of_nonneg_right hcard' (by positivity))
    _ = _ := by ring

end DyadicHats

namespace FiniteLabels
open DyadicHats
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma delta_diff_le_one (i j k : ι) : |delta i k-delta j k| ≤ 1 := by
  exact abs_sub_le_iff.mpr ⟨by linarith [(delta i).nonneg k,law_le_one (delta i) k,(delta j).nonneg k],
    by linarith [(delta j).nonneg k,law_le_one (delta j) k,(delta i).nonneg k]⟩

lemma spatialRow_component_lipschitz (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hpB : ∀ z, p z ≤ B) (j : ι) :
    LipschitzWith (Real.toNNReal (16*B/r)) (fun x => spatialRow old target p hp0 hp1 r x j) := by
  have hl := interpolate_lipschitz hr hB (f := fun z => p z*(delta (target z) j-delta old j))
    (fun z => by rw [abs_mul,abs_of_nonneg (hp0 z)]; exact
      (mul_le_mul_of_nonneg_left (delta_diff_le_one _ _ _) (hp0 z)).trans (by simpa using hpB z))
  change LipschitzWith (Real.toNNReal (16*B/r))
    (fun x => delta old j+interpolate r (fun z => p z*(delta (target z) j-delta old j)) x)
  simpa only [zero_add] using (LipschitzWith.const (delta old j)).add hl

end FiniteLabels

namespace DyadicHats
open Finset Filter

lemma interpolate_congr_on (r : ℝ) (x : ℂ) {f g : ℤ × ℤ → ℝ}
    (h : ∀ p, hat r p x ≠ 0 → f p = g p) : interpolate r f x = interpolate r g x := by
  apply tsum_congr
  intro p
  by_cases hp : hat r p x = 0
  · simp only [hp,zero_mul]
  · rw [h p hp]

lemma hat_vertex_local {r : ℝ} (hr : 0 < r) {x q : ℂ}
    (hx : boxNorm (x-q) < 199*r) {p : ℤ × ℤ} (hp : hat r p x ≠ 0) :
    boxNorm (point r p-q) ≤ 200*r := by
  have hd := (hat_ne_zero_iff hr p x).mp hp
  have ht := boxNorm_add_le (point r p-x) (x-q)
  rw [sub_add_sub_cancel,boxNorm_sub_comm (point r p) x] at ht
  linarith

end DyadicHats

namespace FiniteLabels

lemma probability_lt_one_iff {τ d : ℝ} (hτ : 0 < τ) : probability τ d < 1 ↔ d < 2*τ := by
  rw [probability,min_lt_iff]
  constructor
  · intro h
    rcases h with h|h
    · exact (lt_irrefl _ h).elim
    have hm := le_max_left (d-τ) 0
    have hn : 0 ≤ τ⁻¹*max (d-τ) 0 := by positivity
    have ht : τ⁻¹*max (d-τ) 0 < 1 := by nlinarith
    rw [inv_mul_eq_div,div_lt_one hτ] at ht
    linarith
  · intro h
    right
    have hm : max (d-τ) 0 < τ := max_lt (by linarith) hτ
    have hn : 0 ≤ τ⁻¹*max (d-τ) 0 := by positivity
    have ht : τ⁻¹*max (d-τ) 0 < 1 := by rw [inv_mul_eq_div,div_lt_one hτ]; exact hm
    nlinarith

end FiniteLabels

namespace DyadicHats
open Finset

lemma hat_at_point {r : ℝ} (hr : r ≠ 0) (p q : ℤ × ℤ) :
    hat r p (point r q) = if p=q then 1 else 0 := by
  have ht (a b : ℤ) : tent ((b:ℝ)-(a:ℝ)) = if a=b then 1 else 0 := by
    by_cases h : a=b
    · simp [h,tent]
    · rw [ite_eq_right h]
      apply tent_eq_zero_of_one_le
      have hi : (1:ℤ) ≤ |b-a| := Int.one_le_abs (sub_ne_zero.mpr (Ne.symm h))
      exact_mod_cast hi
  simp only [hat,point,mul_div_cancel_left₀ _ hr,ht]
  split_ifs <;> simp_all [Prod.ext_iff]

lemma hat_vertex_bound {r : ℝ} (hr : 0 < r) {N : ℕ} {x : ℂ}
    (hx1 : |x.re| ≤ r*N) (hx2 : |x.im| ≤ r*N)
    {p : ℤ × ℤ} (hp : hat r p x ≠ 0) : p ∈ indexBox N := by
  have h := (hat_ne_zero_iff hr p x).mp hp
  have h1 := lt_of_le_of_lt (le_max_left |(x-point r p).re| |(x-point r p).im|) h
  have h2 := lt_of_le_of_lt (le_max_right |(x-point r p).re| |(x-point r p).im|) h
  simp only [Complex.sub_re,Complex.sub_im,point] at h1 h2
  have hb (t : ℝ) (j : ℤ) (ht : |t| ≤ r*N) (hj : |t-r*j| < r) :
      j ∈ Finset.Icc (-(N:ℤ)) N := by
    have ht' := abs_le.mp ht
    have hj' := abs_lt.mp hj
    have hlo : -(N:ℝ)-1 < (j:ℝ) := by nlinarith
    have hhi : (j:ℝ) < (N:ℝ)+1 := by nlinarith
    have hlo' : -(N:ℤ)-1 < j := by exact_mod_cast hlo
    have hhi' : j < (N:ℤ)+1 := by exact_mod_cast hhi
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  exact Finset.mem_product.mpr ⟨hb _ _ hx1 h1,hb _ _ hx2 h2⟩

lemma velocity_bound_on_grid {N : ℕ} {r : ℝ} (hr : 0 < r) (k : ℕ) (q : Grid N) :
    |(point r q).re| ≤ scale r k*N ∧ |(point r q).im| ≤ scale r k*N := by
  have h1 := Finset.mem_Icc.mp (Finset.mem_product.mp q.property).1
  have h2 := Finset.mem_Icc.mp (Finset.mem_product.mp q.property).2
  have hh (j : ℤ) (hj : -(N:ℤ) ≤ j ∧ j ≤ N) : |r*j| ≤ scale r k*N := by
    have hj' : |(j:ℝ)| ≤ N := abs_le.mpr ⟨by exact_mod_cast hj.1,by exact_mod_cast hj.2⟩
    rw [abs_mul,abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hj' hr.le).trans
      (mul_le_mul_of_nonneg_right (le_scale hr.le k) (Nat.cast_nonneg N))
  exact ⟨hh q.val.1 h1,hh q.val.2 h2⟩

end DyadicHats

namespace DyadicHats

lemma coeff_eq_hat {N : ℕ} {r : ℝ} (hr : 0 < r) (k : ℕ) (p q : Grid N) :
    coeff N k p q = hat (scale r k) p (point r q) := by
  induction k generalizing p with
  | zero =>
    simp only [coeff,scale,pow_zero,one_mul,hat_at_point hr.ne']
    by_cases hpq : p=q
    · rw [ite_eq_left hpq,ite_eq_left (congrArg Subtype.val hpq)]
    · rw [ite_eq_right hpq,ite_eq_right (fun h => hpq (Subtype.ext h))]
  | succ k ih =>
    rw [coeff,scale_succ,hat_refine,tsum_eq_sum (s := indexBox N)]
    · rw [← sum_coe_sort (indexBox N) (fun j => step p j*hat (scale r k) j (point r q))]
      apply sum_congr rfl
      intro j hj
      rw [ih]
    · intro j hj
      have hz : hat (scale r k) j (point r q) = 0 := by
        by_contra hn
        have hb := velocity_bound_on_grid hr k q
        exact hj (hat_vertex_bound (scale_pos hr k) hb.1 hb.2 hn)
      rw [hz,mul_zero]

lemma hat_refine_grid_at {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {x : ℂ} (hx : ‖x‖ ≤ R) (p : Grid N) :
    hat (2*r) p x = ∑ q : Grid N, step p q*hat r q x := by
  rw [hat_refine,tsum_eq_sum (s := indexBox N)]
  · exact (sum_coe_sort (indexBox N) (fun q => step p q*hat r q x)).symm
  · intro q hq
    have hz : hat r q x = 0 := by
      by_contra hn
      exact hq (mem_indexBox_of_le hr hN hx hn)
    rw [hz,mul_zero]

lemma vectorMass_grid_refine {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (p : Grid N) :
    vectorMass h (2*r) p = ∑ q : Grid N, step p q • vectorMass h r q := by
  let f := fun y => ∑ q : Grid N, step p q • (hat r q y • h y)
  have hf : (fun y => hat (2*r) p y • h y) = f := by
    funext y
    by_cases hy : h y=0
    · simp only [f,hy,smul_zero,sum_const_zero]
    · rw [hat_refine_grid_at hr hN (hs y hy) p,sum_smul]
      simp only [f,smul_smul]
  rw [vectorMass,hf]
  dsimp only [f]
  have hi (q : Grid N) : Integrable (fun y => step p q • (hat r q y • h y)) :=
    Integrable.smul (step p q) (integrable_hat_smul hh r q)
  rw [integral_finsetSum Finset.univ (fun q _ => hi q)]
  apply sum_congr rfl
  intro q hq
  rw [integral_smul]
  rfl

lemma vectorMass_coeff {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : Grid N) :
    vectorMass h (scale r k) p = ∑ q : Grid N, coeff N k p q • vectorMass h r q := by
  induction k generalizing p with
  | zero => simp [coeff,scale]
  | succ k ih =>
    rw [scale_succ,vectorMass_grid_refine (scale_pos hr k) (scale_index_bound hr hR hN k) hh hs]
    simp only [ih,smul_sum,smul_smul,coeff,sum_smul]
    exact Finset.sum_comm

lemma sum_scalarMass_grid_le {N : ℕ} {h : ℂ → ℂ} (hh : Integrable h) (r : ℝ) :
    (∑ q : Grid N, scalarMass h r q) ≤ ∫ y, ‖h y‖ := by
  rw [sum_coe_sort (indexBox N) (fun q => scalarMass h r q)]
  exact sum_scalarMass_le hh r (indexBox N)

end DyadicHats

namespace DyadicHats
open Finset

lemma hat_lower {r a : ℝ} (hr : 0 < r) (ha : a ≤ 1) (p : ℤ × ℤ) (x : ℂ)
    (hx : boxNorm (x-point r p) ≤ a*r) : (1-a)^2 ≤ hat r p x := by
  have h1 := (le_max_left |(x-point r p).re| |(x-point r p).im|).trans hx
  have h2 := (le_max_right |(x-point r p).re| |(x-point r p).im|).trans hx
  simp only [Complex.sub_re,Complex.sub_im,point] at h1 h2
  have hh (t : ℝ) (j : ℤ) (h : |t-r*j| ≤ a*r) : 1-a ≤ tent (t/r-j) := by
    have he : t/r-j = (t-r*j)/r := by field_simp
    rw [he,tent,abs_div,abs_of_pos hr]
    have hd : |t-r*j|/r ≤ a := (div_le_iff₀ hr).mpr h
    exact (sub_le_sub_left hd 1).trans (le_max_left _ _)
  calc
    (1-a)^2 = (1-a)*(1-a) := by ring
    _ ≤ tent (x.re/r-p.1)*tent (x.im/r-p.2) :=
      mul_le_mul (hh _ _ h1) (hh _ _ h2) (sub_nonneg.mpr ha) (tent_nonneg _)
    _ = _ := rfl

lemma nearParent_int_bound (j : ℤ) : |j-4096*((j+2048)/4096)| ≤ 2048 := by
  rw [abs_le]
  omega

lemma nearParent_box {r : ℝ} (hr : 0 < r) (q : ℤ × ℤ) :
    boxNorm (point r q-point (4096*r) (nearParent q)) ≤ (1/2 : ℝ)*(4096*r) := by
  have hh (j : ℤ) : |r*j-(4096*r)*((j+2048)/4096:ℤ)| ≤ (1/2:ℝ)*(4096*r) := by
    have hi : |(j:ℝ)-4096*((j+2048)/4096:ℤ)| ≤ 2048 := by exact_mod_cast nearParent_int_bound j
    have he : r*j-(4096*r)*((j+2048)/4096:ℤ) = r*((j:ℝ)-4096*((j+2048)/4096:ℤ)) := by ring
    rw [he,abs_mul,abs_of_pos hr]
    nlinarith
  exact max_le (hh q.1) (hh q.2)

lemma nearParent_hat_lower {r : ℝ} (hr : 0 < r) (q w : ℤ × ℤ)
    (hw : boxNorm (point r w-point r q) ≤ 500*r) :
    1/4 ≤ hat (scale r 12) (nearParent q) (point r q) ∧
    9/64 ≤ hat (scale r 12) (nearParent q) (point r w) := by
  have hs : scale r 12 = 4096*r := by norm_num [scale]
  have hq := nearParent_box hr q
  have ht := boxNorm_add_le (point r w-point r q) (point r q-point (4096*r) (nearParent q))
  rw [sub_add_sub_cancel] at ht
  have hw' : boxNorm (point r w-point (4096*r) (nearParent q)) ≤ (5/8:ℝ)*(4096*r) := by
    linarith
  have h1 := hat_lower (by positivity : 0 < 4096*r) (by norm_num : (1/2:ℝ) ≤ 1) (nearParent q) (point r q) hq
  have h2 := hat_lower (by positivity : 0 < 4096*r) (by norm_num : (5/8:ℝ) ≤ 1) (nearParent q) (point r w) hw'
  rw [hs]
  norm_num at h1 h2 ⊢
  exact ⟨h1,h2⟩

lemma nearParent_fiber_card (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) :
    (S.filter (fun q => nearParent q=p)).card ≤ 4097^2 := by
  let T := (Finset.Icc (4096*p.1-2048) (4096*p.1+2048)).product
    (Finset.Icc (4096*p.2-2048) (4096*p.2+2048))
  have hsub : S.filter (fun q => nearParent q=p) ⊆ T := by
    intro q hq
    have he := (Finset.mem_filter.mp hq).2
    have h1 := nearParent_int_bound q.1
    have h2 := nearParent_int_bound q.2
    have he1 : (q.1+2048)/4096=p.1 := congrArg Prod.fst he
    have he2 : (q.2+2048)/4096=p.2 := congrArg Prod.snd he
    rw [he1,abs_le] at h1
    rw [he2,abs_le] at h2
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,
      Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩
  apply (Finset.card_le_card hsub).trans
  dsimp only [T]
  change ((Finset.Icc (4096*p.1-2048) (4096*p.1+2048)) ×ˢ
    (Finset.Icc (4096*p.2-2048) (4096*p.2+2048))).card ≤ 4097^2
  rw [Finset.card_product,Int.card_Icc,Int.card_Icc]
  have he (j : ℤ) : 4096*j+2048+1-(4096*j-2048)=4097 := by ring
  rw [he,he]
  change (4097:ℕ)*4097 ≤ 4097^2
  norm_num

end DyadicHats

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.DirectionEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

noncomputable section

namespace DirectionNeighbors
open DyadicHats Finset

lemma mem_window_iff {r : ℝ} (hr : 0 < r) (d : ℕ) (q z : ℤ × ℤ) :
    z ∈ window d q ↔ boxNorm (point r z-point r q) ≤ (d:ℝ)*r := by
  have hh (a b : ℤ) : |r*a-r*b| ≤ (d:ℝ)*r ↔ b-(d:ℤ) ≤ a ∧ a ≤ b+d := by
    rw [← mul_sub,abs_mul,abs_of_pos hr,mul_comm (d:ℝ) r,mul_le_mul_iff_right₀ hr]
    have hc : |(a:ℝ)-(b:ℝ)| ≤ (d:ℝ) ↔ |a-b| ≤ (d:ℤ) := by
      exact_mod_cast Iff.rfl
    rw [hc,abs_le]
    omega
  change (_ ∈ ((Finset.Icc _ _) ×ˢ (Finset.Icc _ _))) ↔ max _ _ ≤ _
  rw [Finset.mem_product,Finset.mem_Icc,Finset.mem_Icc,max_le_iff]
  exact (hh _ _).symm.and (hh _ _).symm

lemma maxVertex_mem (f : ℤ × ℤ → ℝ) (d : ℕ) (q : ℤ × ℤ) :
    maxVertex f d q ∈ window d q := (Classical.choose_spec (max_exists f d q)).1
lemma le_maxVertex (f : ℤ × ℤ → ℝ) (d : ℕ) (q : ℤ × ℤ) {z : ℤ × ℤ}
    (hz : z ∈ window d q) : f z ≤ f (maxVertex f d q) :=
  (Classical.choose_spec (max_exists f d q)).2 z hz

lemma energy_nonneg (h : ℂ → ℂ) (r : ℝ) (q : ℤ × ℤ) : 0 ≤ energy h r q := sq_nonneg _

lemma energy_controls {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q z : ℤ × ℤ)
    (hz : boxNorm (point r z-point r q) ≤ 200*r) :
    ‖Theta h r z-theta h r q‖^2 ≤ energy h r q := by
  apply le_maxVertex (fun z => ‖Theta h r z-theta h r q‖^2) 200 q
  exact (mem_window_iff hr 200 q z).mpr (by simpa using hz)

lemma worstVertex_near {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ) :
    boxNorm (point r (worstVertex h r q)-point r q) ≤ 200*r := by
  have hm := maxVertex_mem (fun z => ‖Theta h r z-theta h r q‖^2) 200 q
  simpa only [worstVertex,Nat.cast_ofNat] using (mem_window_iff hr 200 q _).mp hm

lemma chosen_near {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (z : ℤ × ℤ) :
    boxNorm (point r (chosen h r z)-point r z) ≤ 300*r := by
  simpa only [chosen,Nat.cast_ofNat] using
    (mem_window_iff hr 300 z _).mp (maxVertex_mem (scalarMass h r) 300 z)

/-- The actual chosen neighbor supplies at least the root's mass and is within
500 fine-grid units, precisely the inputs spent by the coarse triangle defect. -/
lemma worst_chosen_spec {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ) :
    scalarMass h r q ≤ scalarMass h r (chosen h r (worstVertex h r q)) ∧
    boxNorm (point r (chosen h r (worstVertex h r q))-point r q) ≤ 500*r := by
  let z := worstVertex h r q
  have hz : boxNorm (point r z-point r q) ≤ 200*r := worstVertex_near hr h q
  have hz' : boxNorm (point r q-point r z) ≤ 300*r := by
    rw [boxNorm_sub_comm]
    linarith
  have ha := le_maxVertex (scalarMass h r) 300 z ((mem_window_iff hr 300 z q).mpr (by simpa using hz'))
  have hw := chosen_near hr h z
  have ht := boxNorm_add_le (point r (chosen h r z)-point r z) (point r z-point r q)
  rw [sub_add_sub_cancel] at ht
  exact ⟨ha,by linarith⟩

end DirectionNeighbors

namespace DirectionNeighbors
open DyadicHats

lemma vectorMass_mem_grid {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    {q : ℤ × ℤ} (hq : vectorMass h r q ≠ 0) : q ∈ indexBox N := by
  by_contra hn
  apply hq
  apply integral_eq_zero_of_ae
  filter_upwards with y
  by_cases hy : h y=0
  · simp only [hy,smul_zero,Pi.zero_apply]
  · have hh : hat r q y=0 := by
      by_contra hz
      exact hn (mem_indexBox_of_le hr hN (hs y hy) hz)
    simp only [hh,zero_smul,Pi.zero_apply]

lemma direction_refine {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (d : ℕ) (p : Grid N) :
    scalarMass h (scale r d) p • theta h (scale r d) p =
      ∑ q : Grid N, (coeff N d p q*scalarMass h r q) • theta h r q := by
  rw [show scalarMass h (scale r d) p • theta h (scale r d) p =
    vectorMass h (scale r d) p from IntrinsicMarks.mass_direction 1 _]
  rw [vectorMass_coeff hr hR hN hh hs]
  apply Finset.sum_congr rfl
  intro q _
  rw [mul_smul]
  congr 1
  exact (IntrinsicMarks.mass_direction 1 _).symm

lemma coarseDefect_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (d : ℕ) (p : Grid N) :
    0 ≤ coarseDefect N h r d p := by
  have he := VectorRefinement.quadratic_defect (coeff N d p) (fun q : Grid N => scalarMass h r q)
    (fun q : Grid N => theta h r q) (theta h (scale r d) p) (scalarMass h (scale r d) p)
    (norm_theta _ _ _) (fun _ => norm_theta _ _ _) (direction_refine hr hR hN hh hs d p)
  rw [coarseDefect,he]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun q _ =>
    mul_nonneg (mul_nonneg (coeff_nonneg _ _ _ _) (norm_nonneg _)) (sq_nonneg _)

lemma coarseDefect_sum (N : ℕ) (h : ℂ → ℂ) (r : ℝ) (d : ℕ) :
    (∑ p : Grid N, coarseDefect N h r d p) =
      (∑ q : Grid N, scalarMass h r q)-(∑ p : Grid N, scalarMass h (scale r d) p) := by
  simp only [coarseDefect,Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,coeff_column,one_mul]

/-- The actual maximally differing neighbor spends true vector cancellation,
not an independently postulated directional budget. -/
lemma neighbor_charge {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (q : Grid N) :
    scalarMass h r q*energy h r q ≤ 48*coarseDefect N h r 12 (parent N q) := by
  by_cases hq : scalarMass h r q=0
  · rw [hq,zero_mul]
    exact mul_nonneg (by norm_num) (coarseDefect_nonneg hr hR hN hh hs 12 _)
  have hqpos : 0 < scalarMass h r q := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hq)
  let z := chosen h r (worstVertex h r q)
  have hz := worst_chosen_spec hr h q
  have hzpos : 0 < scalarMass h r z := hqpos.trans_le hz.1
  have hzmem : z ∈ indexBox N := vectorMass_mem_grid hr hN hs (norm_ne_zero_iff.mp (ne_of_gt hzpos))
  let s : Grid N := ⟨z,hzmem⟩
  have hweights := nearParent_hat_lower hr q z hz.2
  have hwq : 1/4 ≤ coeff N 12 (parent N q) q := by
    rw [coeff_eq_hat hr]
    exact hweights.1
  have hws : 9/64 ≤ coeff N 12 (parent N q) s := by
    rw [coeff_eq_hat hr]
    exact hweights.2
  have he := VectorRefinement.pair_defect_bound (coeff N 12 (parent N q))
    (fun p : Grid N => scalarMass h r p) (fun p : Grid N => theta h r p)
    (theta h (scale r 12) (parent N q)) (scalarMass h (scale r 12) (parent N q))
    (fun p => coeff_nonneg N 12 _ p) (fun _ => norm_nonneg _)
    (norm_theta _ _ _) (fun _ => norm_theta _ _ _)
    (direction_refine hr hR hN hh hs 12 _) hwq hws hz.1
  change scalarMass h r q*‖theta h r z-theta h r q‖^2 ≤ _
  rw [norm_sub_rev]
  exact he

lemma parent_fiber_card (N : ℕ) (p : Grid N) :
    (Finset.univ.filter (fun q : Grid N => parent N q=p)).card ≤ 4097^2 := by
  let F := Finset.univ.filter (fun q : Grid N => parent N q=p)
  let e : Grid N ↪ ℤ × ℤ := ⟨Subtype.val,Subtype.val_injective⟩
  have hm : F.map e ⊆ (indexBox N).filter (fun q => nearParent q=p.val) := by
    intro q hq
    obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp hq
    apply Finset.mem_filter.mpr
    exact ⟨s.property,congrArg Subtype.val (Finset.mem_filter.mp hs).2⟩
  calc
    _ = (F.map e).card := (Finset.card_map e).symm
    _ ≤ ((indexBox N).filter (fun q => nearParent q=p.val)).card := Finset.card_le_card hm
    _ ≤ 4097^2 := nearParent_fiber_card _ _

lemma parent_sum_bound (N : ℕ) (a : Grid N → ℝ) (ha : ∀ p, 0 ≤ a p) :
    (∑ q : Grid N, a (parent N q)) ≤ (4097:ℝ)^2*∑ p : Grid N, a p := by
  rw [← Finset.sum_fiberwise Finset.univ (parent N) (fun q => a (parent N q)),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  calc
    _ = ∑ q ∈ Finset.univ.filter (fun q => parent N q=p), a p := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [(Finset.mem_filter.mp hq).2]
    _ = ((Finset.univ.filter (fun q => parent N q=p)).card:ℝ)*a p := by simp
    _ ≤ (4097:ℝ)^2*a p := by
      apply mul_le_mul_of_nonneg_right _ (ha p)
      exact_mod_cast parent_fiber_card N p

/-- Uniform one-scale neighbor energy bound by the actual twelve-scale mass drop. -/
theorem level_energy_budget {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) :
    (∑ q : Grid N, scalarMass h r q*energy h r q) ≤
      (48*(4097:ℝ)^2)*((∑ q : Grid N, scalarMass h r q)-
        ∑ p : Grid N, scalarMass h (scale r 12) p) := by
  have h1 := Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset (Grid N))) =>
    neighbor_charge hr hR hN hh hs q)
  have h2 := parent_sum_bound N (coarseDefect N h r 12)
    (fun p => coarseDefect_nonneg hr hR hN hh hs 12 p)
  rw [← Finset.mul_sum] at h1
  have h3 := h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 48))
  rw [coarseDefect_sum] at h3
  simpa only [mul_assoc] using h3

end DirectionNeighbors

namespace DirectionNeighbors
open DyadicHats
lemma scale_scale (r : ℝ) (k d : ℕ) : scale (scale r k) d = scale r (k+d) := by
  simp only [scale,pow_add]
  ring

lemma shifted_mass_bound (A : ℕ → ℝ) {V : ℝ} (h0 : ∀ k, 0 ≤ A k)
    (hV : ∀ k, A k ≤ V) (m d : ℕ) :
    (∑ k ∈ Finset.range m, (A k-A (k+d))) ≤ d*V := by
  have he : (∑ k ∈ Finset.range m, A k)+(∑ k ∈ Finset.range d, A (k+m)) =
      (∑ k ∈ Finset.range d, A k)+(∑ k ∈ Finset.range m, A (k+d)) := by
    calc
      _ = ∑ k ∈ Finset.range (m+d), A k := by
        simpa only [Nat.add_comm] using (Finset.sum_range_add A m d).symm
      _ = ∑ k ∈ Finset.range (d+m), A k := by rw [Nat.add_comm m d]
      _ = _ := by simpa only [Nat.add_comm] using Finset.sum_range_add A d m
  have hprefix : (∑ k ∈ Finset.range d, A k) ≤ d*V := by
    calc
      _ ≤ ∑ _k ∈ Finset.range d, V := Finset.sum_le_sum (fun k _ => hV k)
      _ = _ := by simp
  have htail : 0 ≤ ∑ k ∈ Finset.range d, A (k+m) := Finset.sum_nonneg (fun k _ => h0 _)
  rw [Finset.sum_sub_distrib]
  linarith

theorem neighbor_energy_budget {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) :
    (∑ k ∈ Finset.range m, ∑ q : Grid N,
      scalarMass h (scale r k) q*energy h (scale r k) q) ≤
      (576*(4097:ℝ)^2)*(∫ y, ‖h y‖) := by
  let A := fun k => ∑ q : Grid N, scalarMass h (scale r k) q
  have he (k : ℕ) :
      (∑ q : Grid N, scalarMass h (scale r k) q*energy h (scale r k) q) ≤
        (48*(4097:ℝ)^2)*(A k-A (k+12)) := by
    simpa only [scale_scale] using level_energy_budget (scale_pos hr k) hR
      (scale_index_bound hr hR hN k) hh hs
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range m) => he k)
  rw [← Finset.mul_sum] at hsum
  have hA0 (k : ℕ) : 0 ≤ A k := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hAV (k : ℕ) : A k ≤ ∫ y, ‖h y‖ := sum_scalarMass_grid_le hh _
  have hb := shifted_mass_bound A hA0 hAV m 12
  have hf := hsum.trans (mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ 48*(4097:ℝ)^2))
  norm_num at hf ⊢
  nlinarith only [hf]
end DirectionNeighbors

/-! Actual fixed palette and literal cone coordinates. -/

open MeasureTheory Set
open scoped RealInnerProductSpace
noncomputable section
namespace ConeCoordinates

lemma sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
lemma sqrt3_bounds : 3/2 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 2 := by
  have := sqrt3_sq
  have := sqrt3_pos
  constructor <;> nlinarith
lemma inner_re (n z : ℂ) : inner ℝ n z = (star n*z).re := by
  simp [real_inner_eq_re_inner ℂ, RCLike.inner_apply, Complex.mul_re]
  ring
lemma coordinate_apply (n z : ℂ) (s : ℝ) :
    coordinate n s z = (star n*z).re / Real.sqrt 3 + s*(star n*z).im := by
  change (1/Real.sqrt 3)*inner ℝ n z + s*inner ℝ (Complex.I*n) z = _
  rw [inner_re,inner_im]
  ring
lemma expansion {n : ℂ} (hn : ‖n‖ = 1) (z : ℂ) :
    coordinate n 1 z • axis n 1 + coordinate n (-1) z • axis n (-1) = z := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt sqrt3_pos
  have hz : n*(star n*z) = z := by rw [← mul_assoc,mul_star_of_unit hn,one_mul]
  have he : coordinate n 1 z • axis n 1 + coordinate n (-1) z • axis n (-1) =
      n*(star n*z) := by
    apply Complex.ext <;> simp [axis,coordinate_apply,Complex.mul_re,Complex.mul_im] <;> field_simp <;> ring
  exact he.trans hz
lemma coordinate_norm_le {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : |s| ≤ 1) (z : ℂ) :
    |coordinate n s z| ≤ 2 * ‖z‖ := by
  have ha : |inner ℝ n z| ≤ ‖z‖ := by simpa [hn] using abs_real_inner_le_norm n z
  have hb : |inner ℝ (Complex.I*n) z| ≤ ‖z‖ := by
    simpa [norm_mul,hn] using abs_real_inner_le_norm (Complex.I*n) z
  have hr : 1 / Real.sqrt 3 ≤ 1 := by rw [div_le_one sqrt3_pos]; linarith [sqrt3_bounds]
  have hnon : 0 ≤ 1 / Real.sqrt 3 := (div_pos (by norm_num) sqrt3_pos).le
  calc
    |coordinate n s z| ≤ (1/Real.sqrt 3)*|inner ℝ n z| + |s| *|inner ℝ (Complex.I*n) z| := by
      change |(1/Real.sqrt 3)*inner ℝ n z + s*inner ℝ (Complex.I*n) z| ≤ _
      simpa only [abs_mul,abs_of_nonneg hnon] using
        abs_add_le ((1/Real.sqrt 3)*inner ℝ n z) (s*inner ℝ (Complex.I*n) z)
    _ ≤ 1*‖z‖+1*‖z‖ := add_le_add (mul_le_mul hr ha (abs_nonneg _) (by norm_num))
      (mul_le_mul hs hb (abs_nonneg _) (by norm_num))
    _ = 2*‖z‖ := by ring

lemma good_of_close {n z : ℂ} (hn : ‖n‖ = 1) (hclose : ‖z-n‖ ≤ 1/10) : Good n z := by
  have ha : |inner ℝ n (z-n)| ≤ 1/10 := by
    have h := abs_real_inner_le_norm n (z-n)
    simp only [hn,one_mul] at h
    exact h.trans hclose
  have hb : |inner ℝ (Complex.I*n) (z-n)| ≤ 1/10 := by
    have h := abs_real_inner_le_norm (Complex.I*n) (z-n)
    simp only [norm_mul,Complex.norm_I,hn,one_mul] at h
    exact h.trans hclose
  have hin : inner ℝ n n = 1 := by simp [hn]
  have hip : inner ℝ (Complex.I*n) n = 0 := by
    rw [inner_im,show star n*n = 1 by simpa [mul_comm] using mul_star_of_unit hn]
    simp
  simp only [inner_sub_right,hin,hip,sub_zero] at ha hb
  have hab := (abs_le.mp ha).1
  have hbb := abs_le.mp hb
  have hs := sqrt3_bounds
  have ha' : 1/10 ≤ inner ℝ n z / Real.sqrt 3 := by
    apply (le_div_iff₀ sqrt3_pos).2
    nlinarith
  change 0 ≤ (1/Real.sqrt 3)*inner ℝ n z + 1*inner ℝ (Complex.I*n) z ∧
    0 ≤ (1/Real.sqrt 3)*inner ℝ n z + (-1)*inner ℝ (Complex.I*n) z
  have hei : (1/Real.sqrt 3)*inner ℝ n z = inner ℝ n z / Real.sqrt 3 := by ring
  rw [hei]
  constructor <;> nlinarith

lemma quantize_close (z : ℂ) (hz : ‖z‖ = 1) : ‖z-(quantize z hz : ℂ)‖ < 1/2000 :=
  (Classical.choose_spec (fixedPalette.cover z hz)).2

end ConeCoordinates

end
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Prices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace ConeScalar
open ConeCoordinates DyadicHats IntrinsicMarks

lemma root_mass_norm {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N)
    {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s^2 = 1) :
    (∫ y, ‖densityRoot N r (fun x => coordinate n s (h x)) k q y • axis n s‖) =
      |coordinate n s (vectorMass h (scale r k) q)| := by
  simp only [norm_smul,axis_norm hn hs,Real.norm_eq_abs,mul_one]
  rw [densityRoot_abs_mass hr hR hN (scalar_integrable hh _) (scalar_support hsupp _),scalar_mass hh]

lemma root_bound {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N)
    {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s^2 = 1) :
    (∫ y, ‖densityRoot N r (fun x => coordinate n s (h x)) k q y • axis n s‖) ≤
      2*scalarMass h (scale r k) q := by
  rw [root_mass_norm hr hR hN hh hsupp k q hn hs]
  apply coordinate_norm_le hn
  exact (abs_le_one_iff_mul_self_le_one).mpr (by nlinarith)

end ConeScalar

namespace AffineDensities

lemma mass_rescale (h : ℂ → ℂ) (p : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ X, ‖rescale p r h X‖) = r⁻¹*(∫ y, ‖h y‖) := by
  simp only [rescale,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr.le,integral_const_mul]
  have he := Measure.integral_comp_smul volume (fun y : ℂ => ‖h (p+y)‖) r
  simp only [Complex.finrank_real_complex,smul_eq_mul,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r))] at he
  rw [he, integral_add_left_eq_self (fun y : ℂ => ‖h y‖)]
  field_simp

end AffineDensities

namespace PricePieces
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities

lemma errorPiece_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k j : ℕ) (hj : j ≤ k) (p : ℂ) (q : Grid N)
    {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s^2 = 1) :
    (errorPiece hh hr k j hj p q n s).mass ≤ (scale r k)⁻¹*
      (2*densityDefect N r (fun x => coordinate n s (h x)) j q) := by
  change (∫ X, ‖rescale _ _ _ X‖) ≤ _
  rw [mass_rescale _ _ (scale_pos hr k)]
  simp only [norm_smul,axis_norm hn hs,mul_one,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (densityError_cost hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) j q)
    (inv_nonneg.mpr (scale_pos hr k).le)

end PricePieces

namespace LocalCancellation

lemma ErrorPiece.mass_weight {Cs : ℝ} (b : ErrorPiece Cs) {w : ℝ} (hw : 0 ≤ w) :
    (b.weight w).mass = w*b.mass := by
  simp only [ErrorPiece.mass,ErrorPiece.weight,norm_smul,Real.norm_eq_abs,abs_of_nonneg hw,
    integral_const_mul]

end LocalCancellation

namespace PricePieces
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities

lemma vector_decomposition {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    (k : ℕ) (q : Grid N) {n : ℂ} (hn : ‖n‖ = 1) (y : ℂ) :
    hat (scale r k) q y • h y = rootVector N r h k q n y+
      ∑ j ∈ Finset.range (k+1), ∑ s : Grid N, coeff N (k-j) q s • errorVector N r h j s n y := by
  have hp := density_decomposition hr hR hN (scalar_support hsupp (coordinate n 1)) k q y
  have hm := density_decomposition hr hR hN (scalar_support hsupp (coordinate n (-1))) k q y
  have hx := congrArg (fun z : ℂ => hat (scale r k) q y • z) (expansion hn (h y))
  rw [smul_add,smul_smul,smul_smul,hp,hm,add_smul,add_smul] at hx
  simp only [rootVector,errorVector,smul_add,smul_smul,Finset.sum_add_distrib]
  rw [← hx]
  simp only [Finset.sum_smul]
  abel

lemma rootVector_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) {n : ℂ} (hn : ‖n‖ = 1) :
    (∫ y, ‖rootVector N r h k q n y‖) ≤ 4*scalarMass h (scale r k) q := by
  calc
    _ ≤ (∫ y, ‖densityRoot N r (fun x => coordinate n 1 (h x)) k q y • axis n 1‖)+
      (∫ y, ‖densityRoot N r (fun x => coordinate n (-1) (h x)) k q y • axis n (-1)‖) :=
      by
        rw [← integral_add (root_vector_integrable hh r k q n 1).norm
          (root_vector_integrable hh r k q n (-1)).norm]
        exact integral_mono (rootVector_integrable hh r k q n).norm
          ((root_vector_integrable hh r k q n 1).norm.add
            (root_vector_integrable hh r k q n (-1)).norm) (fun y => norm_add_le _ _)
    _ ≤ 2*scalarMass h (scale r k) q+2*scalarMass h (scale r k) q :=
      add_le_add (root_bound hr hR hN hh hsupp k q hn (by norm_num))
        (root_bound hr hR hN hh hsupp k q hn (by norm_num))
    _ = _ := by ring

end PricePieces

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar Finset

lemma rho_pos : 0 < rho := Real.rpow_pos_of_pos (by norm_num) _
lemma rho_lt_one : rho < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)

lemma scale_ratio {r : ℝ} (hr : 0 < r) {j k : ℕ} (hj : j ≤ k) :
    scale r j / scale r k = (1/2:ℝ)^(k-j) := by
  dsimp [scale]
  rw [mul_div_mul_right _ _ hr.ne']
  have hk : k = j+(k-j) := (Nat.add_sub_of_le hj).symm
  conv_lhs => rw [hk,pow_add]
  simp only [div_pow,one_pow]
  field_simp

lemma scale_discount {r : ℝ} (hr : 0 < r) {j k : ℕ} (hj : j ≤ k) :
    (scale r j / scale r k)^(1/100:ℝ) = rho^(k-j) := by
  rw [scale_ratio hr hj]
  unfold rho
  rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num),mul_comm ((k-j:ℕ):ℝ),
    Real.rpow_mul (by norm_num),Real.rpow_natCast]

lemma scalarPrice_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    0 ≤ scalarPrice N r h rho k q := by
  apply sum_nonneg
  intro j _
  apply mul_nonneg (pow_nonneg rho_pos.le _)
  exact sum_nonneg (fun s _ => mul_nonneg (coeff_nonneg N (k-j) q s)
    (densityDefect_nonneg hr hR hN hh hsupp j s))

lemma rootPrice_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    0 ≤ rootPrice N r h k q := by
  apply sum_nonneg
  intro n _
  exact add_nonneg
    (scalarPrice_nonneg hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) k q)
    (scalarPrice_nonneg hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) k q)

lemma coordinate_total_le {h : ℂ → ℂ} (hh : Integrable h) {n : ℂ} (hn : ‖n‖ = 1)
    {s : ℝ} (hs : |s| ≤ 1) : (∫ x, |coordinate n s (h x)|) ≤ 2*(∫ x, ‖h x‖) := by
  rw [← integral_const_mul]
  exact integral_mono (scalar_integrable hh _).abs (hh.norm.const_mul 2)
    (fun x => coordinate_norm_le hn hs _)

lemma coordinate_price_budget {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) {n : ℂ} (hn : ‖n‖ = 1)
    {s : ℝ} (hs : |s| ≤ 1) (m : ℕ) :
    (∑ k ∈ range (m+1), ∑ q : Grid N,
      scalarPrice N r (fun x => coordinate n s (h x)) rho k q) ≤
        (1-rho)⁻¹*(∫ x, ‖h x‖) := by
  apply (scalarPrice_budget hr hR hN (scalar_integrable hh _) (scalar_support hsupp _)
    rho_pos.le rho_lt_one m).trans
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by linarith [rho_lt_one]))
  have he := coordinate_total_le hh hn hs
  linarith

/-- The genuine all-label root price has a uniform total budget, including
the terminal scalar splits at the finest scale. -/
theorem rootPrice_budget {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) :
    (∑ k ∈ range (m+1), ∑ q : Grid N, rootPrice N r h k q) ≤
      (2*(fixedPalette.labels.card:ℝ)*(1-rho)⁻¹)*(∫ x, ‖h x‖) := by
  unfold rootPrice
  simp_rw [Finset.sum_comm (s := univ) (t := fixedPalette.labels)]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _n ∈ fixedPalette.labels, 2*((1-rho)⁻¹*(∫ x, ‖h x‖)) := by
      apply sum_le_sum
      intro n hn
      simp_rw [sum_add_distrib]
      have hp := coordinate_price_budget hr hR hN hh hsupp (fixedPalette.unit n hn)
        (by norm_num : |(1:ℝ)| ≤ 1) m
      have hm := coordinate_price_budget hr hR hN hh hsupp (fixedPalette.unit n hn)
        (by norm_num : |(-1:ℝ)| ≤ 1) m
      linarith
    _ = _ := by rw [sum_const,nsmul_eq_mul]; ring

end CommonPrices

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.SpatialLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace FiniteLabels
open DyadicHats
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma spatialRow_mixture (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) (r : ℝ) (x : ℂ) (j : ι) :
    spatialRow old target p hp0 hp1 r x j =
      interpolate r (fun z => (1-p z)*delta old j+p z*delta (target z) j) x := by
  have he (z : ℤ × ℤ) : (1-p z)*delta old j+p z*delta (target z) j =
      delta old j+p z*(delta (target z) j-delta old j) := by ring
  simp_rw [he]
  rw [interpolate_add,interpolate_const]
  rfl

lemma spatialRow_vanish (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) (r : ℝ) (x : ℂ) (j : ι)
    (hj : ∀ z, hat r z x ≠ 0 → (1-p z)*delta old j+p z*delta (target z) j = 0) :
    spatialRow old target p hp0 hp1 r x j = 0 := by
  rw [spatialRow_mixture]
  have he : interpolate r (fun z => (1-p z)*delta old j+p z*delta (target z) j) x =
      interpolate r (fun _ => 0) x := interpolate_congr_on r x hj
  rw [he,interpolate_const]

end FiniteLabels

namespace ActualLabels
open FiniteLabels ConeCoordinates DirectionNeighbors DyadicHats

lemma label_unit (n : Label) : ‖(n:ℂ)‖ = 1 := fixedPalette.unit n n.property

lemma target_close (h : ℂ → ℂ) (r : ℝ) (z : ℤ × ℤ) :
    ‖Theta h r z-(target h r z:ℂ)‖ < 1/2000 := quantize_close _ _

lemma nearby_sample_close {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) (z : ℤ × ℤ) (hz : hat r z x ≠ 0) :
    ‖Theta h r z-theta h r q‖ ≤ 1/1000 := by
  have hloc : boxNorm (point r z-point r q) ≤ 200*r :=
    hat_vertex_local hr (by linarith) hz
  have he := energy_controls hr h q z hloc
  nlinarith [norm_nonneg (Theta h r z-theta h r q)]

lemma sampled_good {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) (z : ℤ × ℤ) (hz : hat r z x ≠ 0) :
    Good (target h r z) (theta h r q) := by
  apply good_of_close (label_unit _)
  have he := nearby_sample_close hr h q hx hE z hz
  have ht := target_close h r z
  have hn : ‖theta h r q-(target h r z:ℂ)‖ ≤ ‖theta h r q-Theta h r z‖+‖Theta h r z-(target h r z:ℂ)‖ := by
    simpa only [dist_eq_norm] using dist_triangle (theta h r q) (Theta h r z) (target h r z:ℂ)
  have he' : ‖theta h r q-Theta h r z‖ ≤ 1/1000 := by simpa only [norm_sub_rev] using he
  linarith

lemma retained_good {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) (z : ℤ × ℤ) (hz : hat r z x ≠ 0)
    (n : Label) (hp : switchChance h r n z < 1) : Good (n:ℂ) (theta h r q) := by
  have hd := (probability_lt_one_iff (by norm_num : (0:ℝ)<1/100)).mp hp
  have he := nearby_sample_close hr h q hx hE z hz
  apply good_of_close (label_unit n)
  have hn : ‖theta h r q-(n:ℂ)‖ ≤ ‖theta h r q-Theta h r z‖+‖Theta h r z-(n:ℂ)‖ := by
    simpa only [dist_eq_norm] using dist_triangle (theta h r q) (Theta h r z) (n:ℂ)
  have he' : ‖theta h r q-Theta h r z‖ ≤ 1/1000 := by simpa only [norm_sub_rev] using he
  have hd' : ‖Theta h r z-(n:ℂ)‖ < 2*(1/100:ℝ) := by simpa only [norm_sub_rev] using hd
  linarith

lemma initial_bad_zero {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) (n : Label)
    (hn : ¬Good (n:ℂ) (theta h r q)) : initial h r x n = 0 := by
  apply spatialRow_vanish
  intro z hz
  have ht : n ≠ target h r z := fun ht => hn (ht ▸ sampled_good hr h q hx hE z hz)
  simp [delta,ht]

lemma row_bad_zero {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) (old n : Label)
    (hn : ¬Good (n:ℂ) (theta h r q)) : row h r x old n = 0 := by
  apply spatialRow_vanish
  intro z hz
  have ht : n ≠ target h r z := fun ht => hn (ht ▸ sampled_good hr h q hx hE z hz)
  by_cases ho : n = old
  · subst n
    have hp : switchChance h r old z = 1 := le_antisymm (switchChance_le_one h r old z)
      (le_of_not_gt (fun hp => hn (retained_good hr h q hx hE z hz old hp)))
    simp [hp,delta,ht]
  · simp [delta,ho,ht]

theorem marginal_bad_zero (h : ℂ → ℂ) (r : ℕ → ℝ) (k : ℕ) (hr : 0 < r k)
    (q : ℤ × ℤ) {x : ℂ} (hx : boxNorm (x-point (r k) q) ≤ 50*r k)
    (hE : energy h (r k) q ≤ (1/1000:ℝ)^2) (n : Label)
    (hn : ¬Good (n:ℂ) (theta h (r k) q)) : marginal h r k x n = 0 := by
  cases k with
  | zero => exact initial_bad_zero hr h q hx hE n hn
  | succ k =>
    simp only [marginal,move_apply,row_bad_zero hr h q hx hE _ n hn,mul_zero,Finset.sum_const_zero]

end ActualLabels

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Packing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar Finset PricePieces LocalCancellation AffineDensities

lemma sign_sq (b : Bool) : sign b^2 = 1 := by cases b <;> norm_num [sign]

lemma rootWeight_nonneg {N : ℕ} (S : Finset (Grid N)) (k j : ℕ) (s : Grid N) :
    0 ≤ rootWeight S k j s := sum_nonneg (fun q _ => coeff_nonneg N (k-j) q s)

lemma smallPiece_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) (i : ErrorIndex N k) :
    (smallPiece hh hr k p S n i).mass ≤ (scale r k)⁻¹*2*
      (rootWeight S k i.1 i.2.1*densityDefect N r (fun x => coordinate n (sign i.2.2) (h x)) i.1 i.2.1) := by
  rw [smallPiece,ErrorPiece.mass_weight _ (rootWeight_nonneg ..)]
  calc
    _ ≤ rootWeight S k i.1 i.2.1*((scale r k)⁻¹*
        (2*densityDefect N r (fun x => coordinate n (sign i.2.2) (h x)) i.1 i.2.1)) :=
      mul_le_mul_of_nonneg_left (errorPiece_mass hr hR hN hh hsupp k i.1
        (Nat.le_of_lt_succ i.1.isLt) p i.2.1 hn (sign_sq _)) (rootWeight_nonneg ..)
    _ = _ := by ring

lemma discounted_smallPiece_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) (i : ErrorIndex N k) :
    (smallPiece hh hr k p S n i).size^(1/100:ℝ)*(smallPiece hh hr k p S n i).mass ≤
      (scale r k)⁻¹*2*(rho^(k-i.1)*
        (rootWeight S k i.1 i.2.1*densityDefect N r (fun x => coordinate n (sign i.2.2) (h x)) i.1 i.2.1)) := by
  have hs : (smallPiece hh hr k p S n i).size^(1/100:ℝ) = rho^(k-i.1) :=
    scale_discount hr (Nat.le_of_lt_succ i.1.isLt)
  rw [hs]
  calc
    _ ≤ rho^(k-i.1)*((scale r k)⁻¹*2*
        (rootWeight S k i.1 i.2.1*densityDefect N r (fun x => coordinate n (sign i.2.2) (h x)) i.1 i.2.1)) :=
      mul_le_mul_of_nonneg_left (smallPiece_mass hr hR hN hh hsupp k p S hn i) (pow_nonneg rho_pos.le _)
    _ = _ := by ring

lemma weighted_defect_sum {N : ℕ} (r : ℝ) (h : ℂ → ℝ) (k : ℕ) (S : Finset (Grid N)) :
    (∑ j : Fin (k+1), ∑ s : Grid N, rho^(k-j.val)*(rootWeight S k j s*densityDefect N r h j s)) =
      ∑ q ∈ S, scalarPrice N r h rho k q := by
  simp only [rootWeight,sum_mul,mul_sum]
  simp_rw [Finset.sum_comm (s := univ) (t := S)]
  apply sum_congr rfl
  intro q _
  unfold scalarPrice
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j _
  rw [mul_sum]

lemma smallPiece_price {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) :
    errorPrice (smallPiece hh hr k p S n) (1/100) ≤ (scale r k)⁻¹*2*
      ∑ q ∈ S, (scalarPrice N r (fun x => coordinate n 1 (h x)) rho k q+
        scalarPrice N r (fun x => coordinate n (-1) (h x)) rho k q) := by
  apply (sum_le_sum (fun i _ => discounted_smallPiece_mass hr hR hN hh hsupp k p S hn i)).trans_eq
  rw [← mul_sum]
  congr 1
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,sign,Bool.false_eq_true,
    ite_false,ite_true,sum_add_distrib]
  rw [weighted_defect_sum,weighted_defect_sum,← sum_add_distrib]

lemma smallPiece_common_price {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : n ∈ fixedPalette.labels) :
    errorPrice (smallPiece hh hr k p S n) (1/100) ≤ (scale r k)⁻¹*2*cellPrice N r h k S := by
  apply (smallPiece_price hr hR hN hh hsupp k p S (fixedPalette.unit n hn)).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (inv_nonneg.mpr (scale_pos hr k).le) (by norm_num))
  apply sum_le_sum
  intro q _
  apply single_le_sum _ hn
  intro n _
  exact add_nonneg
    (scalarPrice_nonneg hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) k q)
    (scalarPrice_nonneg hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) k q)

end CommonPrices

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar Finset PricePieces LocalCancellation AffineDensities

lemma rootSum_partition {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) (y : ℂ) :
    rootSum h r k (goodRoots h r k S n) n y+rootSum h r k (badRoots h r k S n) n y = rootSum h r k S n y := by
  classical
  exact sum_filter_add_sum_filter_not S (fun q => Good n (DirectionNeighbors.theta h (scale r k) q)) _

lemma rootSum_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) :
    (∫ y, ‖rootSum h r k S n y‖) ≤ 4*∑ q ∈ S, scalarMass h (scale r k) q := by
  calc
    _ ≤ ∫ y, ∑ q ∈ S, ‖rootVector N r h k q n y‖ :=
      integral_mono (rootSum_integrable hh r k S n).norm
        (integrable_finsetSum S (fun _ _ => (rootVector_integrable hh r k _ n).norm))
        (fun y => norm_sum_le _ _)
    _ = ∑ q ∈ S, ∫ y, ‖rootVector N r h k q n y‖ :=
      integral_finsetSum S (fun _ _ => (rootVector_integrable hh r k _ n).norm)
    _ ≤ _ := by rw [mul_sum]; exact sum_le_sum (fun q _ => rootVector_mass hr hR hN hh hsupp k q hn)

lemma badPiece_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) :
    (badPiece hr hh k p S n).mass ≤ (scale r k)⁻¹*4*badPrice h r k S n := by
  change (∫ X, ‖rescale p (scale r k) (rootSum h r k (badRoots h r k S n) n) X‖) ≤ _
  rw [mass_rescale _ _ (scale_pos hr k)]
  simpa only [mul_assoc,badPrice] using mul_le_mul_of_nonneg_left
    (rootSum_mass hr hR hN hh hsupp k (badRoots h r k S n) hn) (inv_nonneg.mpr (scale_pos hr k).le)

lemma cellErrors_price {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : n ∈ fixedPalette.labels) :
    errorPrice (cellErrors hr hh k p S n) (1/100) ≤
      (scale r k)⁻¹*(4*badPrice h r k S n+2*cellPrice N r h k S) := by
  simp only [errorPrice,Fintype.sum_option,cellErrors,show (badPiece hr hh k p S n).size = 1 from rfl,
    Real.one_rpow,one_mul]
  have h1 := badPiece_mass hr hR hN hh hsupp k p S (fixedPalette.unit n hn)
  have h2 := smallPiece_common_price hr hR hN hh hsupp k p S hn
  unfold errorPrice at h2
  linarith

end CommonPrices

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar Finset PricePieces LocalCancellation AffineDensities

lemma smallPiece_pair_sum {N : ℕ} {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} (hh : Integrable h)
    (k : ℕ) (p : ℂ) (S : Finset (Grid N)) (n : ℂ) (j : Fin (k+1)) (q : Grid N) (X : ℂ) :
    (∑ b : Bool, (smallPiece hh hr k p S n (j,q,b)).density X) =
      rootWeight S k j q • rescale p (scale r k) (errorVector N r h j q n) X := by
  simp only [Fintype.sum_bool,smallPiece,ErrorPiece.weight,errorPiece,sign,
    Bool.false_eq_true,ite_false,ite_true,rescale,errorVector]
  module

lemma smallPiece_sum {N : ℕ} {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} (hh : Integrable h)
    (k : ℕ) (p : ℂ) (S : Finset (Grid N)) (n : ℂ) (X : ℂ) :
    (∑ i : ErrorIndex N k, (smallPiece hh hr k p S n i).density X) =
      rescale p (scale r k) (fun y => ∑ q ∈ S, ∑ j ∈ range (k+1),
        ∑ s : Grid N, coeff N (k-j) q s • errorVector N r h j s n y) X := by
  simp only [Fintype.sum_prod_type,smallPiece_pair_sum,rootWeight,sum_smul,rescale,smul_sum]
  simp_rw [Finset.sum_comm (s := univ) (t := S)]
  apply sum_congr rfl
  intro q _
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro s _
  module

/-- Exact cell decomposition before imposing the local partition-of-unity
region. Both its scalar coordinates and all error densities are the actual
finite dyadic construction. -/
theorem cell_decomposition {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s = 1 ∨ s = -1) (X : ℂ) :
    (goodCone hr hR hN hh hsupp k p S hn hs).density X+
      (∑ i, (cellErrors hr hh k p S n i).density X) =
      rescale p (scale r k) (fun y => (∑ q ∈ S, hat (scale r k) q y) • h y) X := by
  rw [Fintype.sum_option]
  change rescale p (scale r k) (rootSum h r k (goodRoots h r k S n) n) X+
    (rescale p (scale r k) (rootSum h r k (badRoots h r k S n) n) X+
      ∑ i : ErrorIndex N k, (smallPiece hh hr k p S n i).density X) = _
  rw [smallPiece_sum]
  simp only [rescale,← smul_add,← add_assoc,rootSum_partition]
  rw [sum_smul]
  congr 1
  simp only [rootSum,← sum_add_distrib]
  exact sum_congr rfl (fun q _ => (vector_decomposition hr hR hN hsupp k q hn _).symm)

end CommonPrices

namespace DirectionNeighbors
open DyadicHats
lemma mem_window_comm (d : ℕ) (p q : ℤ × ℤ) : p ∈ window d q ↔ q ∈ window d p := by
  rw [mem_window_iff (by norm_num : (0:ℝ) < 1),mem_window_iff (by norm_num : (0:ℝ) < 1),boxNorm_sub_comm]

lemma card_window (d : ℕ) (q : ℤ × ℤ) : (window d q).card = (2*d+1)^2 := by
  change ((Finset.Icc (q.1-(d:ℤ)) (q.1+d)) ×ˢ
    (Finset.Icc (q.2-(d:ℤ)) (q.2+d))).card = _
  rw [Finset.card_product,Int.card_Icc,Int.card_Icc]
  have hq (z : ℤ) : (z+(d:ℤ)+1-(z-d)).toNat = 2*d+1 := by omega
  rw [hq,hq,pow_two]

end DirectionNeighbors

namespace CommonPrices
open DyadicHats ConeCoordinates Finset DirectionNeighbors

lemma cellPrice_spatial {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, cellPrice N r h k (cellRoots N p)) ≤ 1681*∑ q : Grid N, rootPrice N r h k q := by
  simp only [cellPrice,cellRoots,sum_filter]
  rw [Finset.sum_comm]
  rw [mul_sum]
  apply sum_le_sum
  intro q _
  have hn := rootPrice_nonneg hr hR hN hh hsupp k q
  have hs : P.filter (fun p => (q:ℤ×ℤ) ∈ window 20 p) ⊆ window 20 q := by
    intro p hp
    exact (mem_window_comm 20 _ _).mp (mem_filter.mp hp).2
  have hc : ((P.filter (fun p => (q:ℤ×ℤ) ∈ window 20 p)).card : ℝ) ≤ 1681 := by
    have hc := Finset.card_le_card hs
    rw [card_window] at hc
    exact_mod_cast hc
  rw [← sum_filter,sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hc hn

/-- The common geometric price has a genuine uniform spatial-and-scale
budget, including every desired finite set of observation cells. -/
theorem cellPrice_budget {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) :
    (∑ k ∈ range (m+1), ∑ p ∈ P k, cellPrice N r h k (cellRoots N p)) ≤
      1681*((fixedPalette.labels.card:ℝ)*2/(1-rho))*(∫ y, ‖h y‖) := by
  calc
    _ ≤ ∑ k ∈ range (m+1), 1681*∑ q : Grid N, rootPrice N r h k q :=
      sum_le_sum (fun k _ => cellPrice_spatial hr hR hN hh hsupp k (P k))
    _ = 1681*(∑ k ∈ range (m+1), ∑ q : Grid N, rootPrice N r h k q) := by rw [mul_sum]
    _ ≤ _ := by
      have ht := mul_le_mul_of_nonneg_left (rootPrice_budget hr hR hN hh hsupp m) (by norm_num : (0:ℝ) ≤ 1681)
      have he : 1681*(2*(fixedPalette.labels.card:ℝ)*(1-rho)⁻¹*(∫ y, ‖h y‖)) =
          1681*((fixedPalette.labels.card:ℝ)*2/(1-rho))*(∫ y, ‖h y‖) := by ring
      exact ht.trans_eq he

end CommonPrices

namespace AffineDensities
lemma gradient_affine {g : ℂ → ℝ} (hg : Differentiable ℝ g) (p : ℂ) (r : ℝ) (X : ℂ) :
    gradient (fun Y => g (p+r • Y)) X = rescale p r (gradient g) X := by
  have hA : HasFDerivAt (fun Y : ℂ => p+r • Y) (r • ContinuousLinearMap.id ℝ ℂ) X :=
    ((hasFDerivAt_id X).const_smul r).const_add p
  have hc := (hg (p+r • X)).hasFDerivAt.comp X hA
  change HasFDerivAt (fun Y => g (p+r • Y)) _ X at hc
  apply (InnerProductSpace.toDual ℝ ℂ).injective
  simp only [toDual_gradient,rescale,map_smul]
  rw [hc.fderiv]
  ext z
  simp
end AffineDensities

namespace DyadicHats
open Finset
lemma vector_partition_grid {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (x : ℂ) :
    (∑ p : Grid N, hat r p x) • h x = h x := by
  by_cases hx : h x = 0
  · simp only [hx,smul_zero]
  · have he := density_partition_grid hr hN (h := fun y => ‖h y‖)
      (fun y hy => hs y (fun hh => hy (by rw [hh,norm_zero]))) x
    rw [← sum_mul] at he
    have hsum : (∑ p : Grid N, hat r p x) = 1 := by
      apply mul_right_cancel₀ (norm_ne_zero_iff.mpr hx)
      simpa only [one_mul] using he
    rw [hsum,one_smul]
end DyadicHats

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments

lemma hat_mem_cellRoots {N : ℕ} {r : ℝ} (hr : 0 < r) (p : ℤ × ℤ) (X : ℂ) (hX : ‖X‖ ≤ 12)
    (q : Grid N) (hq : hat r q (point r p+r • X) ≠ 0) : q ∈ cellRoots N p := by
  have hl := (hat_ne_zero_iff hr q (point r p+r • X)).mp hq
  have hnorm : boxNorm (r • X) ≤ 12*r := by
    apply (boxNorm_le_norm _).trans
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    nlinarith
  have hh := boxNorm_add_le (point r q-(point r p+r • X)) (r • X)
  rw [boxNorm_sub_comm (point r q)] at hh
  have hie : point r q-(point r p+r • X)+r • X = point r q-point r p := by abel
  rw [hie] at hh
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  rw [mem_window_iff hr 20]
  norm_num
  linarith

lemma cell_partition {N : ℕ} {r R : ℝ} (hr : 0 < r) (hN : R/r+1 ≤ (N:ℝ))
    {h : ℂ → ℂ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (p : ℤ × ℤ) (X : ℂ) (hX : ‖X‖ ≤ 12) :
    (∑ q ∈ cellRoots N p, hat r q (point r p+r • X)) • h (point r p+r • X) = h (point r p+r • X) := by
  have he : (∑ q ∈ cellRoots N p, hat r q (point r p+r • X)) =
      ∑ q : Grid N, hat r q (point r p+r • X) := by
    apply sum_subset (subset_univ _)
    intro q _ hq
    by_contra hh
    exact hq (hat_mem_cellRoots hr p X hX q hh)
  rw [he]
  exact vector_partition_grid hr hN hs _

lemma cell_decomposition_gradient {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {g : ℂ → ℝ} (hg : Differentiable ℝ g)
    (hh : Integrable (gradient g)) (hsupp : ∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R)
    (k : ℕ) (p : ℤ × ℤ) {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (X : ℂ) (hX : ‖X‖ ≤ 12) :
    (goodCone hr hR hN hh hsupp k (point (scale r k) p) (cellRoots N p) hn hs).density X+
      (∑ i, (cellErrors hr hh k (point (scale r k) p) (cellRoots N p) n i).density X) =
      gradient (fun Y => g (point (scale r k) p+scale r k • Y)) X := by
  rw [cell_decomposition hr hR hN hh hsupp k _ _ hn hs,gradient_affine hg]
  simp only [rescale]
  rw [cell_partition (scale_pos hr k) (scale_index_bound hr hR hN k) hsupp p X hX]

/-- The hard directional local price, instantiated with the actual common-price
cone decomposition on the actual neighboring grid roots. -/
theorem directional_cell_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) → ∀ (k : ℕ) (p : ℤ × ℤ)
    {n : ℂ}, n ∈ fixedPalette.labels → ∀ {s : ℝ}, (s = 1 ∨ s = -1) →
    ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ X in Q, F X) ≤ ENNReal.ofReal (C*(scale r k)⁻¹*
        (badPrice (gradient g) r k (cellRoots N p) n+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ X, ‖X‖ ≤ 2 → ∀ t,
        NeighborhoodRadius (fun Y => g (point (scale r k) p+scale r k • Y)) X t →
        ENNReal.ofReal (max 0 (-inner ℝ (axis n s)
          (∫ Y in Metric.ball X t, gradient (fun Z => g (point (scale r k) p+scale r k • Z)) Y))) ≤ F X := by
  obtain ⟨C,hC,hmajor⟩ := direction_majorant (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) < 1/2)
  refine ⟨4*C,by positivity,?_⟩
  intro N r R hr hR hN g hg hh hsupp k p n hn s hs Q hQ
  have hnu := fixedPalette.unit n hn
  let a := goodCone hr hR hN hh hsupp k (point (scale r k) p) (cellRoots N p) hnu hs
  let b := cellErrors hr hh k (point (scale r k) p) (cellRoots N p) n
  have hg' : ContDiff ℝ 1 (fun Y => g (point (scale r k) p+scale r k • Y)) := hg.comp (by fun_prop)
  obtain ⟨F,hFm,hFi,hFb⟩ := hmajor a b (axis_norm hnu (by rcases hs with rfl | rfl <;> norm_num)) _ hg' Q hQ
  refine ⟨F,hFm,?_,?_⟩
  · apply hFi.trans
    apply ENNReal.ofReal_le_ofReal
    have hb := cellErrors_price hr hR hN hh hsupp k (point (scale r k) p) (cellRoots N p) hn
    have hD : 0 ≤ cellPrice N r (gradient g) k (cellRoots N p) :=
      sum_nonneg (fun q _ => rootPrice_nonneg hr hR hN hh hsupp k q)
    change errorPrice b (1/100) ≤ _ at hb
    have hrk := scale_pos hr k
    nlinarith [mul_le_mul_of_nonneg_left hb hC.le,inv_nonneg.mpr hrk.le,
      mul_nonneg (inv_nonneg.mpr hrk.le) hD]
  · intro X hX t ht
    apply hFb X _ t ht
    filter_upwards with Y hY
    apply cell_decomposition_gradient hr hR hN (hg.differentiable one_ne_zero) hh hsupp k p hnu hs
    have hy : ‖Y-X‖ < 3 := by simpa only [Metric.mem_ball,dist_eq_norm] using hY
    have htri := norm_add_le (Y-X) X
    rw [sub_add_cancel] at htri
    linarith

end CommonPrices

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Envelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace DyadicHats
lemma point_mem_neighborhood {r : ℝ} (hr : 0 ≤ r) (q : ℤ × ℤ) : point r q ∈ neighborhood r q := by
  change boxNorm (point r q-point r q) ≤ _
  simp only [sub_self,boxNorm]
  simpa using (mul_nonneg (by norm_num : (0:ℝ) ≤ 25) hr)
end DyadicHats

namespace DyadicHats
lemma localSup_le {f : ℂ → ℝ} {r A : ℝ} (hr : 0 ≤ r) (q : ℤ × ℤ)
    (h : ∀ x ∈ neighborhood r q, f x ≤ A) : localSup f r q ≤ A := by
  apply csSup_le (Set.Nonempty.image f ⟨point r q,point_mem_neighborhood hr q⟩)
  rintro z ⟨x,hx,rfl⟩
  exact h x hx
lemma le_localSup {f : ℂ → ℝ} {r A : ℝ} (q : ℤ × ℤ)
    (h : ∀ x ∈ neighborhood r q, f x ≤ A) {x : ℂ} (hx : x ∈ neighborhood r q) :
    f x ≤ localSup f r q := le_csSup ⟨A,by rintro z ⟨y,hy,rfl⟩; exact h y hy⟩ ⟨x,hx,rfl⟩
lemma localSup_nonneg {f : ℂ → ℝ} {r A : ℝ} (hr : 0 ≤ r) (q : ℤ × ℤ)
    (h0 : ∀ x, 0 ≤ f x) (h : ∀ x ∈ neighborhood r q, f x ≤ A) : 0 ≤ localSup f r q :=
  (h0 (point r q)).trans (le_localSup q h (point_mem_neighborhood hr q))
end DyadicHats

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Potentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace AffineDensities
lemma fderiv_affine_bound {g : ℂ → ℝ} (hg : Differentiable ℝ g) (p : ℂ) (r : ℝ)
    {D : ℝ} (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) :
    ∃ B : ℝ, ∀ X, ‖fderiv ℝ (fun Y => g (p+r • Y)) X‖ ≤ B := by
  refine ⟨D*|r|,?_⟩
  intro X
  have hA : HasFDerivAt (fun Y : ℂ => p+r • Y)
      (r • ContinuousLinearMap.id ℝ ℂ) X := by
    simpa using ((hasFDerivAt_id X).const_smul r).const_add p
  have hd := (hg (p+r • X)).hasFDerivAt.comp X hA
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs,ContinuousLinearMap.norm_id, mul_one]
  exact mul_le_mul_of_nonneg_right (hD _) (abs_nonneg _)
end AffineDensities

namespace PhysicalCells
open MeasureTheory Set

lemma unitCell_measurable : MeasurableSet unitCell :=
  (Complex.measurable_re measurableSet_Ico).inter (Complex.measurable_im measurableSet_Ico)
lemma toUnit_continuous (p : ℂ) (r : ℝ) : Continuous (toUnit p r) := by unfold toUnit; fun_prop
lemma cell_measurable (p : ℂ) (r : ℝ) : MeasurableSet (cell p r) :=
  (toUnit_continuous p r).measurable unitCell_measurable
lemma volume_unitCell : volume unitCell = 1 := by
  have he := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (s := Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1) (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet
  change volume unitCell = _ at he
  rw [he]
  change (volume.prod volume) (Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1) = 1
  rw [Measure.prod_prod]
  norm_num
lemma norm_unitCell {X : ℂ} (hX : X ∈ unitCell) : ‖X‖ ≤ 2 := by
  have h := Complex.norm_le_abs_re_add_abs_im X
  rw [abs_of_nonneg hX.1.1,abs_of_nonneg hX.2.1] at h
  linarith [hX.1.2,hX.2.2]
lemma toUnit_affine (p : ℂ) {r : ℝ} (hr : r ≠ 0) (X : ℂ) : toUnit p r (p+r • X) = X := by
  simp [toUnit,hr]
lemma affine_toUnit (p : ℂ) {r : ℝ} (hr : r ≠ 0) (y : ℂ) : p+r • toUnit p r y = y := by
  simp [toUnit,hr]

lemma lintegral_smul (F : ℂ → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ X : ℂ, F (r • X)) = ENNReal.ofReal ((r^2)⁻¹)*(∫⁻ y, F y) := by
  have he := (lintegral_map_equiv (μ := volume) F
    (Homeomorph.smul (isUnit_iff_ne_zero.mpr hr).unit).toMeasurableEquiv).symm
  change (∫⁻ X : ℂ, F (r • X)) = ∫⁻ y, F y ∂Measure.map (fun X : ℂ => r • X) volume at he
  rw [he,Measure.map_addHaar_smul volume hr,lintegral_smul_measure]
  simp only [Complex.finrank_real_complex,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r)),smul_eq_mul]

lemma lintegral_toUnit (F : ℂ → ℝ≥0∞) (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ y : ℂ, F (toUnit p r y)) = ENNReal.ofReal (r^2)*(∫⁻ X, F X) := by
  calc
    (∫⁻ y : ℂ, F (r⁻¹ • (y-p))) = ∫⁻ y : ℂ, F (r⁻¹ • y) :=
      lintegral_sub_right_eq_self (μ := (volume : Measure ℂ)) (fun y : ℂ => F (r⁻¹ • y)) p
    _ = _ := by rw [lintegral_smul _ (inv_ne_zero hr),inv_pow,inv_inv]

/-- Exact physical-space change of variables, with the two-dimensional volume
factor and no integrability or measurability assumptions on the majorant. -/
lemma lintegral_cell (F : ℂ → ℝ≥0∞) (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ y in cell p r, F y) = ENNReal.ofReal (r^2)*∫⁻ X in unitCell, F (p+r • X) := by
  rw [← lintegral_indicator (cell_measurable p r),← lintegral_indicator unitCell_measurable]
  have he (y : ℂ) : (cell p r).indicator F y =
      unitCell.indicator (fun X => F (p+r • X)) (toUnit p r y) := by
    by_cases hy : y ∈ cell p r
    · rw [Set.indicator_of_mem hy,Set.indicator_of_mem (show toUnit p r y ∈ unitCell from hy),affine_toUnit p hr]
    · rw [Set.indicator_of_notMem hy,Set.indicator_of_notMem (show toUnit p r y ∉ unitCell from hy)]
  simp_rw [he]
  exact lintegral_toUnit _ p hr

lemma cell_majorant {F : ℂ → ℝ≥0∞} (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ y in cell p r, F (toUnit p r y)) = ENNReal.ofReal (r^2)*∫⁻ X in unitCell, F X := by
  rw [lintegral_cell _ p hr]
  simp only [toUnit_affine p hr]
end PhysicalCells

namespace DiskMoments
lemma signedAverage_affine (g : ℂ → ℝ) (p X : ℂ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    signedAverage (fun Y => g (p+r • Y)) X t = signedAverage g (p+r • X) (r*t) := by
  rw [signedAverage_fixedDomain _ _ ht,signedAverage_fixedDomain _ _ (mul_pos hr ht)]
  congr 1
  apply setIntegral_congr_fun measurableSet_ball
  intro Z _
  change g (p+r • (X+t • Z)) = g (p+r • X+(r*t) • Z)
  congr 1
  rw [smul_add,smul_smul]
  abel

lemma gradient_signedAverage {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    gradient (fun y => signedAverage g y t) x =
      (Real.pi*t^2)⁻¹ • ∫ y in Metric.ball x t, gradient g y := by
  have hi : IntegrableOn (fun z : ℂ => fderiv ℝ g (x+t • z)) (Metric.ball 0 1) :=
    (((hg.continuous_fderiv one_ne_zero).comp (by fun_prop)).continuousOn.integrableOn_compact
      (isCompact_closedBall (0:ℂ) 1)).mono_set Metric.ball_subset_closedBall
  rw [gradient,(hasFDerivAt_signedAverage hg hD x ht).fderiv,map_smul]
  have he := (InnerProductSpace.toDual ℝ ℂ).symm.toContinuousLinearMap.integral_comp_comm hi
  change (∫ z in Metric.ball (0:ℂ) 1, (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ g (x+t • z))) =
    (InnerProductSpace.toDual ℝ ℂ).symm (∫ z in Metric.ball (0:ℂ) 1, fderiv ℝ g (x+t • z)) at he
  rw [← he]
  change (1/Real.pi) • (∫ z in Metric.ball (0:ℂ) 1, gradient g (x+t • z)) = _
  rw [integral_scale_ball (fun z => gradient g (x+z)) ht,integral_translate_ball,smul_smul]
  congr 1
  ring

lemma gradient_average_affine {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (p X : ℂ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    gradient (fun Y => signedAverage (fun Z => g (p+r • Z)) Y t) X =
      r • gradient (fun y => signedAverage g y (r*t)) (p+r • X) := by
  have he : (fun Y => signedAverage (fun Z => g (p+r • Z)) Y t) =
      (fun Y => signedAverage g (p+r • Y) (r*t)) := by
    funext Y
    exact signedAverage_affine g p Y hr ht
  rw [he]
  exact AffineDensities.gradient_affine (fun y =>
    (hasFDerivAt_signedAverage hg hD y (mul_pos hr ht)).differentiableAt) p r X

lemma neighborhoodRadius_affine {g : ℂ → ℝ} (p X : ℂ) {r t : ℝ} (hr : 0 < r)
    (ht : PhysicalNeighborhoodRadius g r (p+r • X) (r*t)) :
    NeighborhoodRadius (fun Y => g (p+r • Y)) X t := by
  have ht1 : 1 ≤ t := (le_of_mul_le_mul_left (by simpa only [mul_one] using ht.1.1) hr)
  have ht2 : t ≤ 2 := (le_of_mul_le_mul_left (by simpa only [mul_comm 2 r] using ht.1.2) hr)
  refine ⟨⟨ht1,ht2⟩,?_⟩
  intro s hs habs
  rw [signedAverage_affine _ _ _ hr hs,signedAverage_affine _ _ _ hr (by linarith)]
  apply ht.2 (r*s) (mul_pos hr hs)
  rw [← mul_sub,abs_mul,abs_of_pos hr]
  nlinarith

end DiskMoments

namespace PhysicalCells
lemma derivative_majorant_integral {F : ℂ → ℝ≥0∞} {C P : ℝ} (p : ℂ) {r : ℝ}
    (hr : 0 < r) (hF : (∫⁻ X in unitCell, F X) ≤ ENNReal.ofReal (C*r⁻¹*P)) :
    (∫⁻ y in cell p r, ENNReal.ofReal r⁻¹*F (toUnit p r y)) ≤ ENNReal.ofReal (C*P) := by
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,cell_majorant p hr.ne']
  apply (mul_le_mul' le_rfl (mul_le_mul' le_rfl hF)).trans_eq
  rw [← ENNReal.ofReal_mul (sq_nonneg r),← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
  congr 1
  field_simp

end PhysicalCells

namespace DiskMoments

lemma average_gradient_negative_le {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x n : ℂ) {t : ℝ} (ht : 1 ≤ t) :
    max 0 (-inner ℝ n (gradient (fun y => signedAverage g y t) x)) ≤
      max 0 (-inner ℝ n (∫ y in Metric.ball x t, gradient g y)) := by
  have hp : 0 < Real.pi*t^2 := mul_pos Real.pi_pos (sq_pos_of_pos (by linarith))
  have h1 : 1 ≤ Real.pi*t^2 := by nlinarith [Real.pi_gt_three,sq_nonneg (t-1)]
  rw [gradient_signedAverage hg hD x (by linarith),inner_smul_right,← mul_neg,
    ← mul_zero (Real.pi*t^2)⁻¹,← mul_max_of_nonneg _ _ (inv_nonneg.mpr hp.le)]
  simp only [mul_zero]
  exact mul_le_of_le_one_left (le_max_left _ _) ((inv_le_one₀ hp).mpr h1)

lemma physical_gradient_negative_majorant {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (p X n : ℂ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    {F : ℝ≥0∞}
    (hF : ENNReal.ofReal (max 0 (-inner ℝ n
      (gradient (fun Y => signedAverage (fun Z => g (p+r • Z)) Y t) X))) ≤ F) :
    ENNReal.ofReal (max 0 (-inner ℝ n (gradient (fun y => signedAverage g y (r*t)) (p+r • X)))) ≤
      ENNReal.ofReal r⁻¹*F := by
  have h : ENNReal.ofReal r⁻¹*_ ≤ ENNReal.ofReal r⁻¹*F := mul_le_mul' le_rfl hF
  rw [gradient_average_affine hg hD p X hr ht,inner_smul_right,← mul_neg,
    ← mul_zero r,← mul_max_of_nonneg _ _ hr.le,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le),inv_mul_cancel_left₀ hr.ne'] at h
  simpa only [mul_zero] using h
end DiskMoments

namespace CommonPrices
open DyadicHats ConeCoordinates LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments PricePieces PhysicalCells

theorem physical_directional_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ)
    {n : ℂ}, n ∈ fixedPalette.labels → ∀ {s : ℝ}, (s = 1 ∨ s = -1) →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ y in cell (point (scale r k) p) (scale r k), F y) ≤ ENNReal.ofReal
        (C*(badPrice (gradient g) r k (cellRoots N p) n+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t,
        PhysicalNeighborhoodRadius g (scale r k) y t →
        ENNReal.ofReal (max 0 (-inner ℝ (axis n s) (gradient (fun z => signedAverage g z t) y))) ≤ F y := by
  obtain ⟨C,hC,hmajor⟩ := directional_cell_price
  refine ⟨C,hC,?_⟩
  intro N r R hr hR hN g hg hh hsupp hD k p n hn s hs
  obtain ⟨D,hD⟩ := hD
  obtain ⟨D',hD'⟩ := fderiv_affine_bound (hg.differentiable one_ne_zero) (point (scale r k) p) (scale r k) hD
  obtain ⟨F,hFm,hFi,hFb⟩ := hmajor hr hR hN hg hh hsupp k p hn hs unitCell (by rw [volume_unitCell]; norm_num)
  refine ⟨fun y => ENNReal.ofReal (scale r k)⁻¹*F (toUnit (point (scale r k) p) (scale r k) y),
    measurable_const.mul (hFm.comp (toUnit_continuous _ _).measurable),
    derivative_majorant_integral _ (scale_pos hr k) hFi,?_⟩
  intro y hy t ht
  let X := toUnit (point (scale r k) p) (scale r k) y
  have hX : ‖X‖ ≤ 2 := norm_unitCell hy
  have he : point (scale r k) p+scale r k • X = y := affine_toUnit _ (scale_pos hr k).ne' y
  have ht' : PhysicalNeighborhoodRadius g (scale r k)
      (point (scale r k) p+scale r k • X) (scale r k*(t/scale r k)) := by
    simpa only [he,mul_div_cancel₀ _ (scale_pos hr k).ne'] using ht
  have htn := neighborhoodRadius_affine _ X (scale_pos hr k) ht'
  have hg' : ContDiff ℝ 1 (fun Z => g (point (scale r k) p+scale r k • Z)) := hg.comp (by fun_prop)
  have hb := (ENNReal.ofReal_le_ofReal (average_gradient_negative_le hg' hD' X (axis n s) htn.1.1)).trans
    (hFb X hX _ htn)
  have hf := physical_gradient_negative_majorant hg hD (point (scale r k) p) X (axis n s)
    (scale_pos hr k) (by linarith [htn.1.1]) hb
  simpa only [he,mul_div_cancel₀ _ (scale_pos hr k).ne'] using hf

end CommonPrices

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Runs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace ActualLabels
open FiniteLabels SignedAssembly Finset ConeCoordinates

lemma observation_lipschitz (h : ℂ → ℂ) (r : ℕ → ℝ) (k : ℕ) (hr : 0 < r k)
    (n j : Label) : LipschitzWith (Real.toNNReal (16/r k)) (fun x => observation h r k x n j) := by
  cases k with
  | zero =>
    simpa only [mul_one,observation,initial,row] using spatialRow_component_lipschitz (quantize 1 (by norm_num))
      (target h (r 0)) (fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl) hr
      (by norm_num : (0:ℝ) ≤ 1) (fun _ => le_rfl) j
  | succ k =>
    simpa only [mul_one,observation,initial,row] using spatialRow_component_lipschitz n (target h (r (k+1)))
      (switchChance h (r (k+1)) n) (switchChance_nonneg h (r (k+1)) n)
      (switchChance_le_one h (r (k+1)) n) hr (by norm_num : (0:ℝ) ≤ 1)
      (switchChance_le_one h (r (k+1)) n) j

end ActualLabels

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.SpatialBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace PhysicalCells
open DyadicHats DirectionNeighbors CommonPrices Finset

lemma toUnit_point_re (r : ℝ) (hr : r ≠ 0) (p : ℤ × ℤ) (y : ℂ) :
    (toUnit (point r p) r y).re = y.re/r-p.1 := by
  simp only [toUnit,Complex.smul_re,Complex.sub_re,point,smul_eq_mul]
  field_simp

lemma toUnit_point_im (r : ℝ) (hr : r ≠ 0) (p : ℤ × ℤ) (y : ℂ) :
    (toUnit (point r p) r y).im = y.im/r-p.2 := by
  simp only [toUnit,Complex.smul_im,Complex.sub_im,point,smul_eq_mul]
  field_simp

lemma mem_index_cell {r : ℝ} (hr : 0 < r) (y : ℂ) :
    y ∈ cell (point r (gridIndex r y)) r := by
  change (toUnit _ r y).re ∈ Set.Ico (0:ℝ) 1 ∧ (toUnit _ r y).im ∈ Set.Ico (0:ℝ) 1
  rw [toUnit_point_re r hr.ne',toUnit_point_im r hr.ne']
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact sub_nonneg.mpr (Int.floor_le _)
  · dsimp only [gridIndex]; linarith [Int.lt_floor_add_one (y.re/r)]
  · exact sub_nonneg.mpr (Int.floor_le _)
  · dsimp only [gridIndex]; linarith [Int.lt_floor_add_one (y.im/r)]

lemma mem_cell_box {r : ℝ} (hr : 0 < r) {p : ℤ × ℤ} {y : ℂ}
    (hy : y ∈ cell (point r p) r) : boxNorm (y-point r p) ≤ r := by
  change (toUnit _ r y).re ∈ Set.Ico (0:ℝ) 1 ∧ (toUnit _ r y).im ∈ Set.Ico (0:ℝ) 1 at hy
  rw [toUnit_point_re r hr.ne',toUnit_point_im r hr.ne'] at hy
  have h (a : ℝ) (b : ℤ) (hab : a/r-b ∈ Set.Ico (0:ℝ) 1) : |a-r*b| ≤ r := by
    have hl : (b:ℝ) ≤ a/r := by linarith [hab.1]
    have hu : a/r < (b:ℝ)+1 := by linarith [hab.2]
    have hl' := (le_div_iff₀ hr).mp hl
    have hu' := (div_lt_iff₀ hr).mp hu
    apply abs_le.mpr
    constructor <;> nlinarith
  exact max_le (h y.re p.1 hy.1) (h y.im p.2 hy.2)

lemma tsum_ofReal_le {ι : Type*} (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i) (A : ℝ)
    (hbudget : ∀ s : Finset ι, ∑ i ∈ s, B i ≤ A) :
    (∑' i, ENNReal.ofReal (B i)) ≤ ENNReal.ofReal A := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hB i)]
  exact ENNReal.ofReal_le_ofReal (hbudget s)

end PhysicalCells

namespace CommonPrices
open DyadicHats DirectionNeighbors Finset ConeCoordinates

lemma cellRoots_budget {N : ℕ} (B : Grid N → ℝ) (hB : ∀ q, 0 ≤ B q)
    (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, ∑ q ∈ cellRoots N p, B q) ≤ 1681*∑ q, B q := by
  simp only [cellRoots,sum_filter]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply sum_le_sum
  intro q _
  have hs : P.filter (fun p => (q:ℤ×ℤ) ∈ window 20 p) ⊆ window 20 q := by
    intro p hp
    exact (mem_window_comm 20 _ _).mp (mem_filter.mp hp).2
  have hc : ((P.filter (fun p => (q:ℤ×ℤ) ∈ window 20 p)).card : ℝ) ≤ 1681 := by
    have hc := Finset.card_le_card hs
    rw [card_window] at hc
    exact_mod_cast hc
  rw [← sum_filter,sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hc (hB q)

lemma badPrice_nonneg {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) :
    0 ≤ badPrice h r k S n := sum_nonneg (fun _ _ => norm_nonneg _)

lemma badPrice_le_rootMass {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) :
    badPrice h r k S n ≤ rootMass h r k S := by
  classical
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => norm_nonneg _)
end CommonPrices

namespace ActualLabels
open DyadicHats DirectionNeighbors FiniteLabels CommonPrices ConeCoordinates Finset

lemma marginal_localSup_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (k : ℕ) (hr : 0 < r k)
    (p : ℤ × ℤ) (n : Label) : 0 ≤ localSup (fun x => marginal h r k x n) (r k) p :=
  localSup_nonneg hr.le p (fun x => (marginal h r k x).nonneg n) (fun _ _ => law_le_one _ _)

lemma marginal_localSup_le_one (h : ℂ → ℂ) (r : ℕ → ℝ) (k : ℕ) (hr : 0 < r k)
    (p : ℤ × ℤ) (n : Label) : localSup (fun x => marginal h r k x n) (r k) p ≤ 1 :=
  localSup_le hr.le p (fun _ _ => law_le_one _ _)

lemma marginal_localSup_bad_zero {N : ℕ} (h : ℂ → ℂ) (r : ℕ → ℝ) (k : ℕ) (hr : 0 < r k)
    (p : ℤ × ℤ) (q : Grid N) (hq : q ∈ cellRoots N p)
    (hE : energy h (r k) q ≤ (1/1000:ℝ)^2) (n : Label)
    (hn : ¬Good (n:ℂ) (theta h (r k) q)) : localSup (fun x => marginal h r k x n) (r k) p = 0 := by
  apply le_antisymm _ (marginal_localSup_nonneg h r k hr p n)
  apply localSup_le hr.le p
  intro y hy
  have hqp : boxNorm (point (r k) p-point (r k) q) ≤ 20*r k := by
    rw [boxNorm_sub_comm]
    exact (mem_window_iff hr 20 p q).mp (mem_filter.mp hq).2
  have hb := boxNorm_add_le (y-point (r k) p) (point (r k) p-point (r k) q)
  rw [sub_add_sub_cancel] at hb
  have hy' : boxNorm (y-point (r k) p) ≤ 25*r k := hy
  rw [marginal_bad_zero h r k hr q (by linarith) hE n hn]

/-- The actual bad-root charge is paid by geometric energy, not a separately
assumed probability budget. -/
lemma marginal_badPrice_bound {N : ℕ} (h : ℂ → ℂ) (r : ℕ → ℝ) (base : ℝ)
    (k j : ℕ) (hr : 0 < r k) (hrj : r k = scale base j) (p : ℤ × ℤ) (n : Label) :
    localSup (fun x => marginal h r k x n) (r k) p*badPrice h base j (cellRoots N p) n ≤
      1000000*∑ q ∈ cellRoots N p, scalarMass h (r k) q*energy h (r k) q := by
  classical
  have hp0 := marginal_localSup_nonneg h r k hr p n
  have hp1 := marginal_localSup_le_one h r k hr p n
  unfold badPrice
  rw [mul_sum]
  calc
    _ ≤ ∑ q ∈ badRoots h base j (cellRoots N p) n,
        1000000*(scalarMass h (r k) q*energy h (r k) q) := by
      apply sum_le_sum
      intro q hq
      have hqp := (mem_filter.mp hq).1
      have hbad : ¬Good (n:ℂ) (theta h (r k) q) := by
        simpa only [hrj] using (mem_filter.mp hq).2
      rw [← hrj]
      by_cases hE : energy h (r k) q ≤ (1/1000:ℝ)^2
      · rw [marginal_localSup_bad_zero h r k hr p q hqp hE n hbad,zero_mul]
        exact mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _) (energy_nonneg _ _ _))
      · have he : 1 ≤ 1000000*energy h (r k) q := by norm_num at hE; linarith
        have hb := mul_le_mul_of_nonneg_right hp1 (norm_nonneg (vectorMass h (r k) q))
        have hc := mul_le_mul_of_nonneg_right he (norm_nonneg (vectorMass h (r k) q))
        dsimp only [scalarMass] at ⊢
        nlinarith
    _ ≤ _ := by
      rw [mul_sum]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q _ _ =>
        mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _) (energy_nonneg _ _ _)))
end ActualLabels

namespace PhysicalCells
open DyadicHats Finset

lemma patch_measurable (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p)) :
    Measurable (patch r F) :=
  Measurable.tsum (fun p => (hF p).indicator (cell_measurable _ _))

lemma le_patch (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (p : ℤ × ℤ) {x : ℂ}
    (hx : x ∈ cell (point r p) r) : F p x ≤ patch r F x := by
  have he := ENNReal.le_tsum (f := fun q => (cell (point r q) r).indicator (F q) x) p
  simpa only [patch,Set.indicator_of_mem hx] using he

lemma lintegral_patch (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p)) :
    (∫⁻ x, patch r F x) = ∑' p, ∫⁻ x in cell (point r p) r, F p x := by
  simp only [patch]
  rw [lintegral_tsum (f := fun p x => (cell (point r p) r).indicator (F p) x) (fun p => ((hF p).indicator (cell_measurable _ _)).aemeasurable)]
  simp_rw [lintegral_indicator (cell_measurable _ _)]

lemma lintegral_patch_budget (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p))
    (B : (ℤ × ℤ) → ℝ) (hB : ∀ p, 0 ≤ B p) (A : ℝ)
    (hcell : ∀ p, (∫⁻ x in cell (point r p) r, F p x) ≤ ENNReal.ofReal (B p))
    (hbudget : ∀ P : Finset (ℤ × ℤ), ∑ p ∈ P, B p ≤ A) :
    (∫⁻ x, patch r F x) ≤ ENNReal.ofReal A := by
  rw [lintegral_patch r F hF]
  exact (ENNReal.tsum_le_tsum hcell).trans (tsum_ofReal_le B hB A hbudget)

lemma patch_finite (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p))
    {A : ℝ} (hi : (∫⁻ x, patch r F x) ≤ ENNReal.ofReal A) :
    ∀ᵐ x, patch r F x ≠ ⊤ := by
  exact (ae_lt_top (patch_measurable r F hF) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi)).mono
    (fun _ hx => hx.ne)

lemma patch_integrable (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p))
    {A : ℝ} (hi : (∫⁻ x, patch r F x) ≤ ENNReal.ofReal A) :
    Integrable (fun x => (patch r F x).toReal) :=
  integrable_toReal_of_lintegral_ne_top (patch_measurable r F hF).aemeasurable
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi)

lemma real_le_patch {r : ℝ} (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (p : ℤ × ℤ) {x : ℂ}
    (hx : x ∈ cell (point r p) r) (hf : patch r F x ≠ ⊤) {a : ℝ}
    (hb : ENNReal.ofReal a ≤ F p x) : a ≤ (patch r F x).toReal := by
  exact (le_max_left a 0).trans (by
    rw [← ENNReal.toReal_ofReal']
    exact (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hf).mpr (hb.trans (le_patch r F p hx)))

/-- Take the cell supremum of a weight only after the local price has been
proved. This is the common production rule for all three spatial budgets. -/
lemma weighted_patch_bound (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p))
    (W : ℂ → ℝ≥0∞) (hW : Measurable W) (A B : (ℤ × ℤ) → ℝ)
    (hA : ∀ p, 0 ≤ A p) (_hB : ∀ p, 0 ≤ B p)
    (hcell : ∀ p, (∫⁻ x in cell (point r p) r, F p x) ≤ ENNReal.ofReal (B p))
    (hWB : ∀ p x, x ∈ cell (point r p) r → W x ≤ ENNReal.ofReal (A p)) :
    (∫⁻ x, W x*patch r F x) ≤ ∑' p, ENNReal.ofReal (A p*B p) := by
  simp only [patch,← ENNReal.tsum_mul_left]
  rw [lintegral_tsum (f := fun p x => W x*(cell (point r p) r).indicator (F p) x) (fun p => (hW.mul ((hF p).indicator (cell_measurable _ _))).aemeasurable)]
  apply ENNReal.tsum_le_tsum
  intro p
  have he : (fun x => W x*(cell (point r p) r).indicator (F p) x) =
      (cell (point r p) r).indicator (fun x => W x*F p x) := by
    funext x
    by_cases hx : x ∈ cell (point r p) r <;> simp [hx]
  rw [he,lintegral_indicator (cell_measurable _ _)]
  calc
    _ ≤ ∫⁻ x in cell (point r p) r, ENNReal.ofReal (A p)*F p x := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (cell_measurable (point r p) r)] with x hx
      exact mul_le_mul' (hWB p x hx) le_rfl
    _ = ENNReal.ofReal (A p)*(∫⁻ x in cell (point r p) r, F p x) :=
      lintegral_const_mul _ (hF p)
    _ ≤ ENNReal.ofReal (A p)*ENNReal.ofReal (B p) := mul_le_mul' le_rfl (hcell p)
    _ = _ := (ENNReal.ofReal_mul (hA p)).symm
end PhysicalCells

namespace ActualLabels
open DyadicHats FiniteLabels GeometricFilter Finset

lemma geometricRadii_pos {base : ℝ} (hb : 0 < base) (m k : ℕ) :
    0 < geometricRadii base m k := div_pos (scale_pos hb m) (by positivity)
lemma geometricRadii_eq (base : ℝ) {m k : ℕ} (hk : k ≤ m) :
    geometricRadii base m k = scale base (m-k) := by
  unfold geometricRadii scale
  rw [show m = (m-k)+k by omega,pow_add]
  field_simp
  rw [show m-k+k-k = m-k by omega]
  ring

end ActualLabels

namespace CommonPrices
open DyadicHats ConeCoordinates Finset

lemma priceConstant_nonneg : 0 ≤ priceConstant := by
  unfold priceConstant
  exact mul_nonneg (by norm_num) (div_nonneg (by positivity) (by linarith [rho_lt_one]))
lemma cellPrice_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (S : Finset (Grid N)) :
    0 ≤ cellPrice N r h k S := sum_nonneg (fun q _ => rootPrice_nonneg hr hR hN hh hsupp k q)
lemma rootMass_cell_budget {N : ℕ} {h : ℂ → ℂ} (hh : Integrable h) (r : ℝ)
    (k : ℕ) (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, rootMass h r k (cellRoots N p)) ≤ 1681*(∫ y, ‖h y‖) := by
  exact (cellRoots_budget _ (fun q => norm_nonneg (vectorMass h (scale r k) q)) P).trans
    (mul_le_mul_of_nonneg_left (sum_scalarMass_grid_le hh _) (by norm_num))
end CommonPrices

namespace ActualLabels
open DyadicHats GeometricFilter PhysicalCells CommonPrices DirectionNeighbors FiniteLabels Finset ActualMarkTrees

lemma geometricRadii_reverse (base : ℝ) {m j : ℕ} (hj : j ≤ m) :
    geometricRadii base m (m-j) = scale base j := by
  rw [geometricRadii_eq base (Nat.sub_le m j),Nat.sub_sub_self hj]

lemma marginal_bad_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) (n : Label) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      localSup (fun x => marginal h (geometricRadii base m) (m-j) x n) (scale base j) p*
        badPrice h base j (cellRoots N p) n) ≤
      (1000000*1681*(576*(4097:ℝ)^2))*(∫ y, ‖h y‖) := by
  calc
    _ ≤ ∑ j ∈ range (m+1), 1000000*1681*∑ q : Grid N,
        scalarMass h (scale base j) q*energy h (scale base j) q := by
      apply sum_le_sum
      intro j hj
      have hjm : j ≤ m := by have := mem_range.mp hj; omega
      calc
        _ ≤ ∑ p ∈ P j, 1000000*∑ q ∈ cellRoots N p,
            scalarMass h (scale base j) q*energy h (scale base j) q := by
          apply sum_le_sum
          intro p _
          have ht := marginal_badPrice_bound (N := N) h (geometricRadii base m) base (m-j) j
            (geometricRadii_pos hb m (m-j)) (geometricRadii_reverse base hjm) p n
          simpa only [geometricRadii_reverse base hjm] using ht
        _ ≤ _ := by
          rw [← mul_sum,mul_assoc]
          exact mul_le_mul_of_nonneg_left (cellRoots_budget _
            (fun q => mul_nonneg (norm_nonneg _) (energy_nonneg _ _ _)) (P j)) (by norm_num)
    _ ≤ _ := by
      rw [← mul_sum]
      have ht := mul_le_mul_of_nonneg_left (neighbor_energy_budget hb hR hN hh hsupp (m+1))
        (by norm_num : (0:ℝ) ≤ 1000000*1681)
      nlinarith only [ht]

lemma marginal_price_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) (n : Label) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      localSup (fun x => marginal h (geometricRadii base m) (m-j) x n) (scale base j) p*
        cellPrice N base h j (cellRoots N p)) ≤ priceConstant*(∫ y, ‖h y‖) := by
  apply le_trans _ (cellPrice_budget hb hR hN hh hsupp m P)
  apply sum_le_sum
  intro j hj
  have hjm : j ≤ m := by have := mem_range.mp hj; omega
  apply sum_le_sum
  intro p _
  have hbnd : localSup (fun x => marginal h (geometricRadii base m) (m-j) x n) (scale base j) p ≤ 1 := by
    rw [← geometricRadii_reverse base hjm]
    exact marginal_localSup_le_one h _ (m-j) (geometricRadii_pos hb m (m-j)) p n
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hbnd (cellPrice_nonneg hb hR hN hh hsupp j _)
end ActualLabels

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.BandBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace ActualLabels
open DyadicHats PhysicalCells CommonPrices ActualMarkTrees Finset FiniteLabels

lemma directPriceConstant_pos : 0 < directPriceConstant := by
  unfold directPriceConstant
  have := priceConstant_nonneg
  positivity

lemma marginal_total_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) (n : Label) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      localSup (fun x => marginal h (geometricRadii base m) (m-j) x n) (scale base j) p*
        (badPrice h base j (cellRoots N p) n+cellPrice N base h j (cellRoots N p))) ≤
      directPriceConstant*(∫ y, ‖h y‖) := by
  simp only [mul_add,sum_add_distrib]
  have h1 := marginal_bad_budget hb hR hN hh hsupp m P n
  have h2 := marginal_price_budget hb hR hN hh hsupp m P n
  unfold directPriceConstant
  nlinarith only [h1,h2]
end ActualLabels

namespace CommonPrices
open DyadicHats Finset
lemma cellPrice_level_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (j : ℕ) (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, cellPrice N base h j (cellRoots N p)) ≤ priceConstant*(∫ y, ‖h y‖) := by
  have hi := single_le_sum (s := range (j+1))
    (f := fun k => ∑ p ∈ P, cellPrice N base h k (cellRoots N p))
    (fun k _ => sum_nonneg (fun p _ => cellPrice_nonneg hb hR hN hh hsupp k _))
    (by simp : j ∈ range (j+1))
  exact hi.trans (cellPrice_budget hb hR hN hh hsupp j (fun _ => P))

lemma total_level_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (j : ℕ) (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, (rootMass h base j (cellRoots N p)+cellPrice N base h j (cellRoots N p))) ≤
      (1681+priceConstant)*(∫ y, ‖h y‖) := by
  rw [sum_add_distrib,add_mul]
  exact add_le_add (rootMass_cell_budget hh base j P) (cellPrice_level_budget hb hR hN hh hsupp j P)
end CommonPrices

namespace ActualLabels
open DyadicHats GeometricFilter PhysicalCells FiniteLabels Finset

lemma marginal_continuous (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (k : ℕ) (n : Label) :
    Continuous (fun x => marginal h r k x n) := by
  induction k generalizing n with
  | zero => exact (observation_lipschitz h r 0 (hr 0) n n).continuous
  | succ k ih =>
    change Continuous (fun x => ∑ j : Label, marginal h r k x j*row h (r (k+1)) x j n)
    apply continuous_finsetSum
    intro j _
    exact (ih j).mul (observation_lipschitz h r (k+1) (hr (k+1)) j n).continuous

end ActualLabels

namespace PhysicalCells
open Finset
lemma sum_tsum_ofReal_le {ι κ : Type*} (s : Finset ι) (B : ι → κ → ℝ)
    (hB : ∀ i ∈ s, ∀ p, 0 ≤ B i p) (A : ℝ)
    (hbudget : ∀ P : Finset κ, ∑ i ∈ s, ∑ p ∈ P, B i p ≤ A) :
    (∑ i ∈ s, ∑' p, ENNReal.ofReal (B i p)) ≤ ENNReal.ofReal A := by
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => hB i hi _)]
  apply tsum_ofReal_le _ (fun p => sum_nonneg (fun i hi => hB i hi p))
  intro P
  rw [Finset.sum_comm]
  exact hbudget P

lemma integrated_weighted_patches {ι : Type*}
    (s : Finset ι) (r : ι → ℝ) (F : ι → (ℤ × ℤ) → ℂ → ℝ≥0∞)
    (hF : ∀ i ∈ s, ∀ p, Measurable (F i p))
    (W : ι → ℂ → ℝ≥0∞) (hW : ∀ i ∈ s, Measurable (W i))
    (A B : ι → (ℤ × ℤ) → ℝ) (hA : ∀ i ∈ s, ∀ p, 0 ≤ A i p)
    (hB : ∀ i ∈ s, ∀ p, 0 ≤ B i p)
    (hcell : ∀ i ∈ s, ∀ p, (∫⁻ x in cell (DyadicHats.point (r i) p) (r i), F i p x) ≤ ENNReal.ofReal (B i p))
    (hWB : ∀ i ∈ s, ∀ p x, x ∈ cell (DyadicHats.point (r i) p) (r i) → W i x ≤ ENNReal.ofReal (A i p))
    (C : ℝ) (hbudget : ∀ P : Finset (ℤ × ℤ), ∑ i ∈ s, ∑ p ∈ P, A i p*B i p ≤ C) :
    (∑ i ∈ s, ∫⁻ x, W i x*patch (r i) (F i) x) ≤ ENNReal.ofReal C := by
  apply le_trans (sum_le_sum (fun i hi => weighted_patch_bound (r i) (F i) (hF i hi)
    (W i) (hW i hi) (A i) (B i) (hA i hi) (hB i hi) (hcell i hi) (hWB i hi)))
  exact sum_tsum_ofReal_le s _ (fun i hi p => mul_nonneg (hA i hi p) (hB i hi p)) C hbudget
end PhysicalCells

namespace CommonPrices
open DyadicHats ConeCoordinates Finset DiskMoments PhysicalCells SignedRuns FiniteLabels ActualLabels

/-- Combine the two actual signed directional prices; the labels are unchanged. -/
theorem physical_unfavorable_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ) (n : Label),
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ y in cell (point (scale r k) p) (scale r k), F y) ≤ ENNReal.ofReal
        (C*(badPrice (gradient g) r k (cellRoots N p) n+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t,
        PhysicalNeighborhoodRadius g (scale r k) y t →
        ENNReal.ofReal (unfavorable n (gradient (fun z => signedAverage g z t) y)) ≤ F y := by
  obtain ⟨C,hC,hp⟩ := physical_directional_price
  refine ⟨2*C,by positivity,?_⟩
  intro N r R hr hR hN g hg hh hs hd k p n
  obtain ⟨F,hFm,hFi,hFb⟩ := hp hr hR hN hg hh hs hd k p n.property (Or.inl rfl : (1:ℝ)=1 ∨ (1:ℝ)=-1)
  obtain ⟨G,hGm,hGi,hGb⟩ := hp hr hR hN hg hh hs hd k p n.property (Or.inr rfl : (-1:ℝ)=1 ∨ (-1:ℝ)=-1)
  have hn : 0 ≤ C*(badPrice (gradient g) r k (cellRoots N p) n+cellPrice N r (gradient g) k (cellRoots N p)) :=
    mul_nonneg hC.le (add_nonneg (badPrice_nonneg _ _ _ _ _) (cellPrice_nonneg hr hR hN hh hs k _))
  refine ⟨fun y => F y+G y,hFm.add hGm,?_,?_⟩
  · rw [lintegral_add_left hFm]
    calc
      _ ≤ ENNReal.ofReal (C*(_+_))+ENNReal.ofReal (C*(_+_)) := add_le_add hFi hGi
      _ = _ := by rw [← ENNReal.ofReal_add hn hn]; congr 1; ring
  · intro y hy t ht
    rw [unfavorable,ENNReal.ofReal_add (le_max_left _ _) (le_max_left _ _)]
    exact add_le_add (hFb y hy t ht) (hGb y hy t ht)

end CommonPrices

namespace PhysicalCells
open Finset

lemma real_weighted_patches {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) (F : ι → (ℤ × ℤ) → ℂ → ℝ≥0∞)
    (hFi : ∀ i ∈ s, Integrable (fun x => (patch (r i) (F i) x).toReal))
    (W : ι → ℂ → ℝ) (hW : ∀ i ∈ s, Measurable (W i))
    (hW0 : ∀ i ∈ s, ∀ x, 0 ≤ W i x) (M : ℝ)
    (hWM : ∀ i ∈ s, ∀ x, W i x ≤ M) {C : ℝ} (hC : 0 ≤ C)
    (hf : (∑ i ∈ s, ∫⁻ x, ENNReal.ofReal (W i x)*patch (r i) (F i) x) ≤ ENNReal.ofReal C) :
    (∑ i ∈ s, ∫ x, W i x*(patch (r i) (F i) x).toReal) ≤ C := by
  have hi (i : ι) (hi : i ∈ s) : Integrable (fun x => W i x*(patch (r i) (F i) x).toReal) := by
    apply (hFi i hi).bdd_mul (hW i hi).aestronglyMeasurable
    exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hW0 i hi x)]; exact hWM i hi x)
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => integral_nonneg (fun x => mul_nonneg (hW0 i hi x) ENNReal.toReal_nonneg))]
  apply le_trans _ hf
  apply sum_le_sum
  intro i his
  rw [ofReal_integral_eq_lintegral_ofReal (hi i his) (ae_of_all _ (fun x => mul_nonneg (hW0 i his x) ENNReal.toReal_nonneg))]
  apply lintegral_mono
  intro x
  change ENNReal.ofReal (W i x * (patch (r i) (F i) x).toReal) ≤ ENNReal.ofReal (W i x) * patch (r i) (F i) x
  rw [ENNReal.ofReal_mul (hW0 i his x)]
  exact mul_le_mul' le_rfl ENNReal.ofReal_toReal_le
end PhysicalCells

namespace CommonPrices
open DyadicHats ConeCoordinates Finset DiskMoments PhysicalCells SignedRuns FiniteLabels ActualLabels

lemma bad_total_level_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (j : ℕ) (P : Finset (ℤ × ℤ)) (n : Label) :
    (∑ p ∈ P, (badPrice h base j (cellRoots N p) n+cellPrice N base h j (cellRoots N p))) ≤
      (1681+priceConstant)*(∫ y, ‖h y‖) := by
  apply le_trans _ (total_level_budget hb hR hN hh hsupp j P)
  apply sum_le_sum
  intro p hp
  exact add_le_add (badPrice_le_rootMass h base j (cellRoots N p) n) le_rfl

/-- Actual full-lattice unfavorable prices, with the genuine marginal law. -/
theorem patched_unfavorable_oai : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R) (hN : R/base+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) →
    ∃ H : ℕ → Label → ℂ → ℝ,
      (∀ j n x, 0 ≤ H j n x) ∧ (∀ j n, Integrable (H j n)) ∧
      (∀ᵐ x, ∀ j n t, PhysicalNeighborhoodRadius g (scale base j) x t →
        unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H j n x) ∧
      (∀ m n, (∑ j ∈ range (m+1), ∫ x, marginal (gradient g) (geometricRadii base m) (m-j) x n*H j n x) ≤
        C*(∫ y, ‖gradient g y‖)) := by
  obtain ⟨c,hc,hp⟩ := physical_unfavorable_price
  refine ⟨c*directPriceConstant,mul_pos hc directPriceConstant_pos,?_⟩
  intro N base R hb hR hN g hg hh hs hd
  choose F hFm hFi hFb using fun j n p => hp hb hR hN hg hh hs hd j p n
  let B := fun j p n => badPrice (gradient g) base j (cellRoots N p) n+cellPrice N base (gradient g) j (cellRoots N p)
  have hB (j p n) : 0 ≤ B j p n := add_nonneg (badPrice_nonneg _ _ _ _ _) (cellPrice_nonneg hb hR hN hh hs j _)
  have hpi (j n) : (∫⁻ x, patch (scale base j) (F j n) x) ≤
      ENNReal.ofReal (c*((1681+priceConstant)*(∫ y, ‖gradient g y‖))) := by
    apply lintegral_patch_budget _ _ (hFm j n) (fun p => c*B j p n) (fun p => mul_nonneg hc.le (hB j p n)) _ (hFi j n)
    intro P
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (bad_total_level_budget hb hR hN hh hs j P n) hc.le
  let H := fun j n x => (patch (scale base j) (F j n) x).toReal
  have hHi (j n) : Integrable (H j n) := patch_integrable _ _ (hFm j n) (hpi j n)
  refine ⟨H,fun _ _ _ => ENNReal.toReal_nonneg,hHi,?_,?_⟩
  · have hfin : ∀ᵐ x, ∀ j n, patch (scale base j) (F j n) x ≠ ⊤ :=
      (ae_all_iff).mpr (fun j => (ae_all_iff).mpr (fun n => patch_finite _ _ (hFm j n) (hpi j n)))
    filter_upwards [hfin] with x hx
    intro j n t ht
    exact real_le_patch (F j n) (gridIndex (scale base j) x) (mem_index_cell (scale_pos hb j) x) (hx j n)
      (hFb j n _ x (mem_index_cell (scale_pos hb j) x) t ht)
  · intro m n
    let W := fun j x => marginal (gradient g) (geometricRadii base m) (m-j) x n
    let A := fun j p => localSup (W j) (scale base j) p
    have hA (j) (hj : j ∈ range (m+1)) (p) : 0 ≤ A j p := by
      have hjm : j ≤ m := by have := mem_range.mp hj; omega
      dsimp [A,W]
      rw [← geometricRadii_reverse base hjm]
      exact marginal_localSup_nonneg _ _ _ (geometricRadii_pos hb m (m-j)) p n
    have hwm (j) : Measurable (W j) := (marginal_continuous _ _ (geometricRadii_pos hb m) (m-j) n).measurable
    have hWB (j) (hj : j ∈ range (m+1)) (p x) (hx : x ∈ cell (point (scale base j) p) (scale base j)) :
        ENNReal.ofReal (W j x) ≤ ENNReal.ofReal (A j p) := by
      apply ENNReal.ofReal_le_ofReal
      apply le_localSup p (fun y _ => law_le_one _ _)
      change DyadicHats.boxNorm (x-point (scale base j) p) ≤ 25*scale base j
      have ht := mem_cell_box (scale_pos hb j) hx
      linarith [scale_pos hb j]
    have hwt := integrated_weighted_patches (range (m+1)) (scale base) (fun j => F j n)
      (fun j _ => hFm j n) (fun j x => ENNReal.ofReal (W j x)) (fun j _ => (hwm j).ennreal_ofReal)
      A (fun j p => c*B j p n) hA (fun j _ p => mul_nonneg hc.le (hB j p n))
      (fun j _ => hFi j n) hWB (c*directPriceConstant*(∫ y, ‖gradient g y‖)) (by
        intro P
        have hbgt := mul_le_mul_of_nonneg_left (marginal_total_budget hb hR hN hh hs m (fun _ => P) n) hc.le
        simpa only [A,W,B,mul_sum,mul_assoc,mul_left_comm] using hbgt)
    exact real_weighted_patches (range (m+1)) (scale base) (fun j => F j n) (fun j _ => hHi j n)
      W (fun j _ => hwm j) (fun j _ x => (marginal _ _ _ x).nonneg n) 1 (fun j _ x => law_le_one _ _)
      (mul_nonneg (mul_nonneg hc.le directPriceConstant_pos.le) (integral_nonneg (fun y => norm_nonneg _))) hwt
end CommonPrices

end

end OAI
end

theorem solution : type_of% @OAI.CommonPrices.patched_unfavorable_oai := @OAI.CommonPrices.patched_unfavorable_oai
