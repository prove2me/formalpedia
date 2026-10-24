-- Prove2me | solution 1 for OAI.CommonPrices.physical_joint_price
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T21:40:09.256476+00:00
-- url     : https://prove2.me/submissions/3e1673fa-6474-44e3-ad5c-078e5015c4b7

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

variable {ι : Type*} [Fintype ι]

/-- The decisive corrected active increment, prior to substitution of the dyadic powers.
The zero moment is the exact one furnished by two balanced kernels, not a bound. -/
lemma corrected_increment_bound {Cs α δ ρ : ℝ} (b : ι → ErrorPiece Cs) (hCs : 0 ≤ Cs)
    (hα : α ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hρ : 0 ≤ ρ)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hFD : ∀ y, F y ≠ 0 → y ∈ D) (x z : ℂ)
    (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3)
    (hzero : ∑ d, ∫ y, star (y-x)*F y*(b d).density y = 0) :
    ‖∑ d, ∫ y, F y*(b d).density y‖ ≤
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
  have he (d : ι) : (∫ y, correction x z y*F y*(b d).density y) =
      (∫ y, F y*(b d).density y) - (star (z-x))⁻¹*(∫ y, star (y-x)*F y*(b d).density y) := by
    have hf := integrable_bounded_pairing (b d).integrable hF.continuous.aestronglyMeasurable hFb
    have hm : Integrable (fun y => star (y-x)*F y*(b d).density y) :=
      integrable_bounded_pairing (b d).integrable
        ((by fun_prop : Continuous (fun y : ℂ => star (y-x))).mul hF.continuous).aestronglyMeasurable
        (position_bound hFb x (by norm_num) hnorm)
    have hid : (fun y => correction x z y*F y*(b d).density y) =
        fun y => F y*(b d).density y - (star (z-x))⁻¹*(star (y-x)*F y*(b d).density y) := by
      funext y
      simp only [correction, div_eq_mul_inv]
      ring
    rw [hid, integral_sub hf (hm.const_mul _), integral_const_mul]
  have hall : (∑ d, ∫ y, correction x z y*F y*(b d).density y) =
      ∑ d, ∫ y, F y*(b d).density y := by
    simp_rw [he]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hzero, mul_zero, sub_zero]
  rw [← hall]
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

namespace LocalCancellation
open DiskGeometry

variable {ι : Type*} [Fintype ι]

theorem size_step {Cs α δ ρ U : ℝ} (b : ι → ErrorPiece Cs)
    (hCs : 0 ≤ Cs) (hα : α ≤ 1) (hδ : 0 < δ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδρ : δ ≤ ρ^2/1600) (hU : 0 < U) :
    ∃ E : Set ℂ, MeasurableSet E ∧
      volume E ≤
        (ENNReal.ofReal U)⁻¹ ^ 2 *
          (ENNReal.ofReal (156*δ/ρ)*ENNReal.ofReal (coarseMass b δ univ)*ENNReal.ofReal (coarseMass b δ univ)) +
        (ENNReal.ofReal U)⁻¹ *
          ((ENNReal.ofReal (6*Real.pi)*ENNReal.ofReal (2*(200*δ/ρ^2)))*ENNReal.ofReal (coarseMass b δ univ)) ∧
      ∀ x ∉ E, ∀ r ∈ Icc (1 : ℝ) 2, ∀ (L : ℝ≥0) (F : ℂ → ℂ),
        LipschitzWith L F → (∀ y, ‖F y‖ ≤ 1) →
        (∀ y, F y ≠ 0 → y ∈ thinShell x r δ) →
        (U ≤ coarseMass b δ (thinShell x r δ) →
          (∑ d, ∫ y, star (y-x)*F y*(b d).density y) = 0) →
        ‖∑ d, ∫ y, F y*(b d).density y‖ ≤
          2*ρ*coarseMass b δ univ+14*U+
            ((L : ℝ)+2*(3*(L : ℝ)+1))*Cs*δ^(2*(1-α))*errorPrice b α := by
  obtain ⟨E, hE, hEv, hcap⟩ := shell_concentration (coarseMeasure b δ) (0 : Measure ℂ)
    hρ hρ1 hδ hδρ (le_refl 0) hU
  refine ⟨E, hE, ?_, ?_⟩
  · simpa only [coarseMeasure_apply b δ MeasurableSet.univ, zero_div, add_zero, mul_one] using hEv
  · intro x hx r hr L F hF hFb hFD hzero
    have hδ1 : δ ≤ 1 := by nlinarith [sq_nonneg (ρ-1)]
    have hδq : δ ≤ 1/4 := by nlinarith [sq_nonneg (ρ-1)]
    have hM0 : 0 ≤ coarseMass b δ univ := by
      rw [coarseMass_univ]
      exact Finset.sum_nonneg (fun d _ => (b d).mass_nonneg)
    have hf0 : 0 ≤ Cs*δ^(2*(1-α))*errorPrice b α :=
      mul_nonneg (mul_nonneg hCs (Real.rpow_nonneg hδ.le _)) (errorPrice_nonneg b α)
    by_cases hactive : U ≤ coarseMass b δ (thinShell x r δ)
    · have hact : ENNReal.ofReal U ≤ coarseMeasure b δ (thinShell x r δ) := by
        rw [coarseMeasure_apply b δ (measurableSet_thinShell x r δ)]
        exact ENNReal.ofReal_le_ofReal hactive
      obtain ⟨z, hz, hzc⟩ := hcap x hx r hr hact (by simp)
      have hzc' : coarseMass b δ (thinShell x r δ \ Metric.ball z ρ) ≤ 2*U := by
        rw [zero_add, coarseMeasure_apply b δ ((measurableSet_thinShell x r δ).diff measurableSet_ball)] at hzc
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hzc
      have hzbound : 1/2 ≤ ‖z-x‖ := by
        simpa only [norm_sub_rev] using (shell_center_bounds hr hδq hz).1
      have hD3 : ∀ y ∈ thinShell x r δ, ‖y-x‖ ≤ 3 := by
        intro y hy
        simpa only [norm_sub_rev] using (shell_center_bounds hr hδq hy).2
      have hc := corrected_increment_bound b hCs hα hδ.le hδ1 hρ.le hF
        (measurableSet_thinShell x r δ) hFb hFD x z hzbound hD3 (hzero hactive)
      nlinarith
    · have hi := increment_bound b hCs hα hδ.le hδ1 hF
        (measurableSet_thinShell x r δ) hFb hFD
      have hx0 : 0 ≤ 2*ρ*coarseMass b δ univ := by positivity
      have hL : (L : ℝ) ≤ (L : ℝ)+2*(3*(L : ℝ)+1) := by linarith [L.coe_nonneg]
      have hh := mul_le_mul_of_nonneg_right hL hf0
      nlinarith

end LocalCancellation

namespace DiskGeometry

lemma thinShell_eq_diff {x : ℂ} {r δ : ℝ} :
    thinShell x r δ = Metric.closedBall x (r+δ) \ Metric.ball x (r-δ) := by
  ext y
  simp only [thinShell, mem_ofPred_eq, abs_le, Set.mem_sdiff, Metric.mem_closedBall,
    Metric.mem_ball, dist_eq_norm, not_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- Exact area of an annulus, including the inner and outer circles. -/
lemma volume_thinShell (x : ℂ) {r δ : ℝ} (hδ : 0 ≤ δ) (hr : δ ≤ r) :
    volume (thinShell x r δ) = ENNReal.ofReal (4*Real.pi*r*δ) := by
  have hi : 0 ≤ r-δ := sub_nonneg.mpr hr
  have ho : 0 ≤ r+δ := by linarith
  rw [thinShell_eq_diff, measure_sdiff (fun y hy => Metric.ball_subset_closedBall
    (Metric.ball_subset_ball (by linarith) hy)) measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne,
    Complex.volume_closedBall, Complex.volume_ball]
  rw [← ENNReal.ofReal_pow ho, ← ENNReal.ofReal_pow hi]
  rw [← (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (NNReal.pi : ℝ) = (NNReal.pi : ℝ≥0∞))]
  change ENNReal.ofReal ((r+δ)^2) * ENNReal.ofReal Real.pi -
    ENNReal.ofReal ((r-δ)^2) * ENNReal.ofReal Real.pi = ENNReal.ofReal (4*Real.pi*r*δ)
  rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_sub _ (mul_nonneg (sq_nonneg _) Real.pi_pos.le)]
  congr 1
  ring

lemma measurableSet_shellPairs (r δ : ℝ) :
    MeasurableSet {p : ℂ × ℂ | p.2 ∈ thinShell p.1 r δ} := by
  exact measurableSet_le (by fun_prop : Measurable (fun p : ℂ × ℂ => |‖p.2-p.1‖-r|)) measurable_const

lemma measurable_shellMass (ν : Measure ℂ) [IsFiniteMeasure ν] (r δ : ℝ) :
    Measurable (shellMass ν r δ) :=
  measurable_measure_prodMk_left (measurableSet_shellPairs r δ)

lemma shell_symm (x y : ℂ) (r δ : ℝ) : y ∈ thinShell x r δ ↔ x ∈ thinShell y r δ := by
  simp only [thinShell, mem_ofPred_eq, norm_sub_rev x y]

/-- The integrated shell mass is its exact area times the total input mass. -/
lemma lintegral_shellMass (ν : Measure ℂ) [IsFiniteMeasure ν] {r δ : ℝ}
    (hδ : 0 ≤ δ) (hr : δ ≤ r) :
    (∫⁻ x, shellMass ν r δ x) = ENNReal.ofReal (4*Real.pi*r*δ)*ν univ := by
  let A : Set (ℂ × ℂ) := {p | p.2 ∈ thinShell p.1 r δ}
  have hA : MeasurableSet A := measurableSet_shellPairs r δ
  have he (x : ℂ) : shellMass ν r δ x = ∫⁻ y, A.indicator 1 (x,y) ∂ν := by
    rw [show (fun y : ℂ => A.indicator 1 (x,y)) = (thinShell x r δ).indicator 1 by
      ext y; exact (indicator_comp_right (fun y : ℂ => (x,y))).symm]
    exact (lintegral_indicator_one (measurableSet_thinShell x r δ)).symm
  simp_rw [he]
  rw [lintegral_lintegral_swap (f := fun x y : ℂ => A.indicator 1 (x,y))
    (measurable_const.indicator hA).aemeasurable]
  have hei (y : ℂ) : (fun x : ℂ => A.indicator (1 : ℂ × ℂ → ℝ≥0∞) (x,y)) =
      (thinShell y r δ).indicator 1 := by
    ext x
    by_cases h : y ∈ thinShell x r δ
    · rw [indicator_of_mem (show (x,y) ∈ A from h), indicator_of_mem ((shell_symm x y r δ).mp h)]
      rfl
    · rw [indicator_of_notMem (show (x,y) ∉ A from h), indicator_of_notMem (fun hx => h ((shell_symm x y r δ).mpr hx))]
  simp_rw [hei, lintegral_indicator_one (measurableSet_thinShell _ r δ), volume_thinShell _ hδ hr]
  exact lintegral_const _

lemma shellMass_exception (ν : Measure ℂ) [IsFiniteMeasure ν] {r δ U : ℝ}
    (hδ : 0 ≤ δ) (hr : δ ≤ r) (hU : 0 < U) :
    MeasurableSet {x | ENNReal.ofReal U ≤ shellMass ν r δ x} ∧
    volume {x | ENNReal.ofReal U ≤ shellMass ν r δ x} ≤
      ENNReal.ofReal (4*Real.pi*r*δ)*ν univ / ENNReal.ofReal U := by
  refine ⟨measurableSet_le measurable_const (measurable_shellMass ν r δ), ?_⟩
  have h := meas_ge_le_lintegral_div (μ := (volume : Measure ℂ))
    (measurable_shellMass ν r δ).aemeasurable (ENNReal.ofReal_pos.mpr hU).ne' ENNReal.ofReal_ne_top
  rwa [lintegral_shellMass ν hδ hr] at h

/-- A shell whose radius is sufficiently close to an endpoint is contained
    in the endpoint annulus; this covers forced endpoint radii as well. -/
lemma thinShell_subset_endpoint {x : ℂ} {r a δ : ℝ} (hra : |r-a| ≤ δ) :
    thinShell x r δ ⊆ thinShell x a (2*δ) := by
  intro y hy
  change |‖y-x‖-r| ≤ δ at hy
  change |‖y-x‖-a| ≤ 2*δ
  calc
    _ = |(‖y-x‖-r)+(r-a)| := by congr 1; ring
    _ ≤ |‖y-x‖-r|+|r-a| := abs_add_le _ _
    _ ≤ 2*δ := by linarith

end DiskGeometry

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
open DiskGeometry DiskKernels DiskScales
variable {ι : Type*} [Fintype ι]

/-- Uniform exceptional sets controlling a whole decreasing sequence of disk
mixtures. Only active increments require the exact balanced moment. -/
theorem size_sequence {Cs d t : ℝ} (b : ι → ErrorPiece Cs)
    (hCs : 0 ≤ Cs) (hd : 0 < d) (hdq : d ≤ 1/4)
    (hgeom : ∀ δ : ℝ, 0 < δ → δ ≤ d → δ ≤ (δ^(1/5 : ℝ))^2/1600)
    (ht : 0 < t) (hAt : errorPrice b (1/100) ≤ t) :
    ∃ E : Set ℂ, MeasurableSet E ∧
      volume E ≤ ∑' n : ℕ, (
        (ENNReal.ofReal (t*(width d n)^(1/10 : ℝ)))⁻¹ ^ 2 *
          (ENNReal.ofReal (156*width d n/(width d n)^(1/5 : ℝ))*
            ENNReal.ofReal (coarseMass b (width d n) univ)*ENNReal.ofReal (coarseMass b (width d n) univ)) +
        (ENNReal.ofReal (t*(width d n)^(1/10 : ℝ)))⁻¹ *
          ((ENNReal.ofReal (6*Real.pi)*ENNReal.ofReal (2*(200*width d n/((width d n)^(1/5 : ℝ))^2)))*
            ENNReal.ofReal (coarseMass b (width d n) univ))) ∧
      ∀ x ∉ E, ∀ r ∈ Icc (1 : ℝ) 2,
        ∀ k : ∀ n : ℕ, RadiusDensity (r-width d n) (r+width d n)
          ⟨216/width d n, div_nonneg (by norm_num) (width_pos hd n).le⟩,
        (∀ n, t*(width d n)^(1/10 : ℝ) ≤ coarseMass b (width d n) (thinShell x r (width d n)) →
          (∑ j, ∫ y, star (y-x)*((kernel (k (n+1)) x y : ℂ)-kernel (k n) x y)*(b j).density y) = 0) →
        ‖∑ j, ∫ y in Metric.ball x r, (b j).density y‖ ≤
          (1+216*Cs)/d^(1/100 : ℝ)*errorPrice b (1/100)+
          (16+4538*Cs)*t*d^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) := by
  have hd1 : d ≤ 1 := by linarith
  have hwp (n : ℕ) : 0 < width d n := width_pos hd n
  have hw1 (n : ℕ) : width d n ≤ 1 := (width_le hd.le n).trans hd1
  have hρ (n : ℕ) : 0 < (width d n)^(1/5 : ℝ) := Real.rpow_pos_of_pos (hwp n) _
  have hρ1 (n : ℕ) : (width d n)^(1/5 : ℝ) ≤ 1 :=
    Real.rpow_le_one (hwp n).le (hw1 n) (by norm_num)
  have hs (n : ℕ) := size_step b hCs (by norm_num : (1/100 : ℝ) ≤ 1)
    (hwp n) (hρ n) (hρ1 n) (hgeom _ (hwp n) (width_le hd.le n))
    (mul_pos ht (Real.rpow_pos_of_pos (hwp n) (1/10 : ℝ)))
  choose E hE hEv hEst using hs
  refine ⟨⋃ n, E n, MeasurableSet.iUnion hE,
    (measure_iUnion_le E).trans (ENNReal.tsum_le_tsum hEv), ?_⟩
  intro x hx r hr k hz
  have hxE (n : ℕ) : x ∉ E n := fun hn => hx (mem_iUnion.mpr ⟨n,hn⟩)
  let P (n : ℕ) : ℂ := ∑ j, ∫ y, (kernel (k n) x y : ℂ)*(b j).density y
  let B : ℂ := ∑ j, ∫ y in Metric.ball x r, (b j).density y
  have hPi (n : ℕ) (j : ι) : Integrable (fun y => (kernel (k n) x y : ℂ)*(b j).density y) :=
    integrable_bounded_pairing (b j).integrable (complex_kernel_lipschitz (k n) x).continuous.aestronglyMeasurable (complex_kernel_bound (k n) x)
  have hdist (n : ℕ) : dist (P n) (P (n+1)) ≤
      (16+4538*Cs)*t*(width d n)^(1/10 : ℝ) := by
    let F (y : ℂ) : ℂ := (kernel (k (n+1)) x y : ℂ)-kernel (k n) x y
    have hL : 216/width d (n+1)+216/width d n ≤ 648/width d n := by
      rw [width_succ]
      apply le_of_eq
      ring
    have hF := (complex_kernel_lipschitz (k (n+1)) x).sub (complex_kernel_lipschitz (k n) x)
    have hbnd := hEst n x (hxE n) r hr _ F hF
      (difference_bound (k n) (k (n+1)) x)
      (difference_support (k n) (k (n+1)) (width_antitone hd.le (Nat.le_succ n)) x)
      (hz n)
    have hM : coarseMass b (width d n) univ ≤
        errorPrice b (1/100)*(width d n)^(-(1/50 : ℝ)) := by
      have hh := coarseMass_bound b (by norm_num : (0 : ℝ) ≤ 1/100) (hwp n)
      norm_num at hh
      simpa only [Real.rpow_neg (hwp n).le, div_eq_mul_inv] using hh
    have hstep := scaled_increment hCs (errorPrice_nonneg b (1/100)) hAt (hwp n) (hw1 n) hM hL
    have he : P (n+1)-P n = ∑ j, ∫ y, F y*(b j).density y := by
      change (∑ j, ∫ y, (kernel (k (n+1)) x y : ℂ)*(b j).density y) -
        (∑ j, ∫ y, (kernel (k n) x y : ℂ)*(b j).density y) = _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← integral_sub (hPi (n+1) j) (hPi n j)]
      congr 1
      ext y
      simp only [F, sub_mul]
    rw [dist_eq_norm, norm_sub_rev, he]
    exact hbnd.trans hstep
  have hlim : Tendsto P atTop (𝓝 B) :=
    tendsto_finsetSum Finset.univ (fun j _ => tendsto_kernel_pairing k (tendsto_width d) x (b j).integrable)
  have hsm : Summable (fun n => (16+4538*Cs)*t*(width d n)^(1/10 : ℝ)) :=
    (summable_width_rpow hd.le (by norm_num : (0 : ℝ) < 1/10)).mul_left _
  have htail := dist_le_tsum_of_dist_le_of_tendsto₀ _ hdist hsm hlim
  rw [tsum_mul_left, tsum_width_rpow hd.le (by norm_num : (0 : ℝ) < 1/10)] at htail
  have hstart : ‖P 0‖ ≤ (1+216*Cs)/d^(1/100 : ℝ)*errorPrice b (1/100) := by
    have hh := total_pairing_discount b (by norm_num : (0 : ℝ) ≤ 1/100)
      (by norm_num : (1/100 : ℝ) ≤ 1) (hwp 0) (hw1 0)
      (show 1 ≤ 1+216*Cs by linarith)
      (complex_kernel_lipschitz (k 0) x) (complex_kernel_bound (k 0) x)
      (show (216/width d 0)*Cs ≤ (1+216*Cs)/width d 0 by
        apply (le_div_iff₀ (hwp 0)).mpr
        field_simp [(hwp 0).ne']
        linarith)
    simpa only [P, width, pow_zero, mul_one] using hh
  calc
    ‖B‖ = ‖P 0+(B-P 0)‖ := by congr 1; ring
    _ ≤ ‖P 0‖+‖B-P 0‖ := norm_add_le _ _
    _ = ‖P 0‖+dist (P 0) B := by rw [dist_eq_norm, norm_sub_rev]
    _ ≤ (1+216*Cs)/d^(1/100 : ℝ)*errorPrice b (1/100)+
        (16+4538*Cs)*t*(d^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) :=
      add_le_add hstart htail
    _ = _ := by ring

end LocalCancellation

namespace DiskGeometry

lemma endpoint_failure_bound (ν : Measure ℂ) [IsFiniteMeasure ν]
    {δ U : ℝ} (hδ : 0 ≤ δ) (hδq : δ ≤ 1/4) (hU : 0 < U) :
    MeasurableSet (endpointFailure ν δ U) ∧
    volume (endpointFailure ν δ U) ≤ ENNReal.ofReal (24*Real.pi*δ)*ν univ/ENNReal.ofReal U := by
  obtain ⟨h1,hb1⟩ := shellMass_exception ν (show 0 ≤ 2*δ by positivity)
    (show 2*δ ≤ 1 by linarith) hU
  obtain ⟨h2,hb2⟩ := shellMass_exception ν (show 0 ≤ 2*δ by positivity)
    (show 2*δ ≤ 2 by linarith) hU
  refine ⟨h1.union h2, (measure_union_le _ _).trans ((add_le_add hb1 hb2).trans_eq ?_)⟩
  simp only [div_eq_mul_inv]
  rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 3
  ring

lemma active_away_from_endpoints (ν : Measure ℂ) {x : ℂ} {δ U r : ℝ}
    (hx : x ∉ endpointFailure ν δ U) (hr : r ∈ Icc (1 : ℝ) 2)
    (ha : ENNReal.ofReal U ≤ ν (thinShell x r δ)) :
    1+δ ≤ r ∧ r+δ ≤ 2 := by
  constructor
  · by_contra hh
    have he : |r-1| ≤ δ := by rw [abs_of_nonneg (by linarith [hr.1])]; linarith
    exact hx (Or.inl (ha.trans (measure_mono (thinShell_subset_endpoint he))))
  · by_contra hh
    have he : |r-2| ≤ δ := by rw [abs_of_nonpos (by linarith [hr.2])]; linarith
    exact hx (Or.inr (ha.trans (measure_mono (thinShell_subset_endpoint he))))

end DiskGeometry

namespace DiskMoments
open DiskKernels DiskGeometry

/-- Every band-maximizing or forced-endpoint radius has honest mixtures;
balancing is imposed exactly when its width stays inside the band. -/
lemma endpoint_kernel {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {x : ℂ} {r δ : ℝ}
    (hr : EndpointRadius g x r) (hδ : 0 < δ) (hδq : δ ≤ 1/4) :
    ∃ k : RadiusDensity (r-δ) (r+δ) ⟨216/δ, by positivity⟩,
      (1+δ ≤ r ∧ r+δ ≤ 2 →
        (∫ y, kernel k x y • (star (y-x)*gradient g y)) = 0) := by
  by_cases hi : 1+δ ≤ r ∧ r+δ ≤ 2
  · have hm : ∀ t ∈ Icc (1 : ℝ) 2, signedAverage g x t ≤ signedAverage g x r := by
      rcases hr.2 with h | h | h
      · linarith [hi.1]
      · linarith [hi.2]
      · exact h
    obtain ⟨k,hk⟩ := balanced_kernel hg x hr.1 hδ hδq
      (hm _ ⟨by linarith [hi.1], by linarith [hr.1.2]⟩)
      (hm _ ⟨by linarith [hr.1.1], hi.2⟩)
    exact ⟨k, fun _ => hk⟩
  · have ha : (1 : ℝ)/2 ≤ r-δ := by linarith [hr.1.1]
    have hb : r+δ ≤ (3 : ℝ) := by linarith [hr.1.2]
    have hab : r-δ < r+δ := by linarith
    let k := inverseCubeDensity (r-δ) (r+δ) ha hb hab
    refine ⟨enlarge k le_rfl le_rfl ?_, fun h => (hi h).elim⟩
    change 216/(r+δ-(r-δ)) ≤ 216/δ
    apply div_le_div_of_nonneg_left (by norm_num) hδ
    linarith

end DiskMoments

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

/-- A local equality of genuine densities suffices for all supported moments. -/
lemma moment_pairing_decomposition {Cs r δ : ℝ} (b : ι → ErrorPiece Cs)
    {M : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M) (x : ℂ) {h : ℂ → ℂ}
    (hr : r+δ ≤ 3) (hh : ∀ᵐ y, y ∈ Metric.ball x 3 → ∑ j, (b j).density y = h y) :
    (∑ j, ∫ y, star (y-x)*(kernel k x y : ℂ)*(b j).density y) =
      ∫ y, kernel k x y • (star (y-x)*h y) := by
  rw [← integral_finsetSum _ (fun j _ => moment_pairing_integrable (b j) k x hr)]
  apply integral_congr_ae
  filter_upwards [hh] with y hy
  simp only [← Finset.mul_sum]
  by_cases hmem : y ∈ Metric.ball x 3
  · rw [hy hmem, Complex.real_smul]
    ring
  · have hk : kernel k x y = 0 := kernel_zero k x
      (fun hb => hmem (lt_of_lt_of_le hb hr))
    rw [hk, Complex.ofReal_zero, mul_zero, zero_mul, zero_smul]

lemma moment_difference_decomposition {Cs r δ ε : ℝ} (b : ι → ErrorPiece Cs)
    {M N : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M)
    (l : RadiusDensity (r-ε) (r+ε) N) (x : ℂ) {h : ℂ → ℂ}
    (hrδ : r+δ ≤ 3) (hrε : r+ε ≤ 3)
    (hh : ∀ᵐ y, y ∈ Metric.ball x 3 → ∑ j, (b j).density y = h y)
    (hk : (∫ y, kernel k x y • (star (y-x)*h y)) = 0)
    (hl : (∫ y, kernel l x y • (star (y-x)*h y)) = 0) :
    (∑ j, ∫ y, star (y-x)*((kernel l x y : ℂ)-kernel k x y)*(b j).density y) = 0 := by
  have he : ∀ j, (∫ y, star (y-x)*((kernel l x y : ℂ)-kernel k x y)*(b j).density y) =
      (∫ y, star (y-x)*(kernel l x y : ℂ)*(b j).density y) -
      (∫ y, star (y-x)*(kernel k x y : ℂ)*(b j).density y) := by
    intro j
    rw [← integral_sub (moment_pairing_integrable (b j) l x hrε)
      (moment_pairing_integrable (b j) k x hrδ)]
    congr 1
    ext y
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, moment_pairing_decomposition b l x hrε hh,
    moment_pairing_decomposition b k x hrδ hh, hk, hl, sub_self]

lemma ball_pairing_decomposition {Cs r : ℝ} (b : ι → ErrorPiece Cs)
    (x : ℂ) {h : ℂ → ℂ} (hr : r ≤ 3)
    (hh : ∀ᵐ y, y ∈ Metric.ball x 3 → ∑ j, (b j).density y = h y) :
    (∑ j, ∫ y in Metric.ball x r, (b j).density y) = ∫ y in Metric.ball x r, h y := by
  rw [← integral_finsetSum _ (fun j _ => (b j).integrable.integrableOn)]
  apply setIntegral_congr_ae measurableSet_ball
  filter_upwards [hh] with y hy hyb
  exact hy (lt_of_lt_of_le hyb hr)

/-- The full raw band-endpoint size estimate. All maxima and both forced radii
are simultaneous, with no measurable radius selection required. -/
theorem size_endpoint_raw {Cs d t : ℝ} (b : ι → ErrorPiece Cs)
    (hCs : 0 ≤ Cs) (hd : 0 < d) (hdq : d ≤ 1/4)
    (hgeom : ∀ δ : ℝ, 0 < δ → δ ≤ d → δ ≤ (δ^(1/5 : ℝ))^2/1600)
    (ht : 0 < t) (hAt : errorPrice b (1/100) ≤ t)
    {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) :
    ∃ E : Set ℂ, MeasurableSet E ∧
      volume E ≤ ∑' n : ℕ, (
        (ENNReal.ofReal (t*(width d n)^(1/10 : ℝ)))⁻¹ ^ 2 *
          (ENNReal.ofReal (156*width d n/(width d n)^(1/5 : ℝ))*
            ENNReal.ofReal (coarseMass b (width d n) univ)*ENNReal.ofReal (coarseMass b (width d n) univ)) +
        (ENNReal.ofReal (t*(width d n)^(1/10 : ℝ)))⁻¹ *
          ((ENNReal.ofReal (6*Real.pi)*ENNReal.ofReal (2*(200*width d n/((width d n)^(1/5 : ℝ))^2)))*
            ENNReal.ofReal (coarseMass b (width d n) univ)) +
        ENNReal.ofReal (24*Real.pi*width d n)*ENNReal.ofReal (coarseMass b (width d n) univ)/
          ENNReal.ofReal (t*(width d n)^(1/10 : ℝ))) ∧
      ∀ x ∉ E,
        (∀ᵐ y, y ∈ Metric.ball x 3 → ∑ j, (b j).density y = gradient g y) →
        ∀ r, EndpointRadius g x r →
        ‖∫ y in Metric.ball x r, gradient g y‖ ≤
          (1+216*Cs)/d^(1/100 : ℝ)*errorPrice b (1/100)+
          (16+4538*Cs)*t*d^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) := by
  have hwp (n : ℕ) : 0 < width d n := width_pos hd n
  have hwq (n : ℕ) : width d n ≤ 1/4 := (width_le hd.le n).trans hdq
  let F (n : ℕ) := endpointFailure (coarseMeasure b (width d n)) (width d n)
    (t*(width d n)^(1/10 : ℝ))
  have hF (n : ℕ) := endpoint_failure_bound (coarseMeasure b (width d n))
    (hwp n).le (hwq n) (mul_pos ht (Real.rpow_pos_of_pos (hwp n) (1/10 : ℝ)))
  obtain ⟨E,hE,hEv,hEst⟩ := size_sequence b hCs hd hdq hgeom ht hAt
  refine ⟨E ∪ ⋃ n, F n, hE.union (MeasurableSet.iUnion fun n => (hF n).1), ?_, ?_⟩
  · apply (measure_union_le _ _).trans
    apply (add_le_add hEv ((measure_iUnion_le F).trans (ENNReal.tsum_le_tsum (fun n => (hF n).2)))).trans_eq
    rw [← ENNReal.tsum_add]
    congr 1
    funext n
    rw [coarseMeasure_apply b (width d n) MeasurableSet.univ]
  · intro x hx hh r hr
    have hxE : x ∉ E := fun h => hx (Or.inl h)
    have hxF (n : ℕ) : x ∉ F n := fun h => hx (Or.inr (mem_iUnion.mpr ⟨n,h⟩))
    choose k hk using fun n => endpoint_kernel hg hr (hwp n) (hwq n)
    rw [← ball_pairing_decomposition b x (by linarith [hr.1.2]) hh]
    apply hEst x hxE r hr.1 k
    intro n ha
    have haway : 1+width d n ≤ r ∧ r+width d n ≤ 2 := by
      apply active_away_from_endpoints (coarseMeasure b (width d n)) (hxF n) hr.1
      rw [coarseMeasure_apply b (width d n) (measurableSet_thinShell x r (width d n))]
      exact ENNReal.ofReal_le_ofReal ha
    have haway' : 1+width d (n+1) ≤ r ∧ r+width d (n+1) ≤ 2 := by
      have hw := width_antitone hd.le (Nat.le_succ n)
      constructor <;> linarith [haway.1,haway.2]
    exact moment_difference_decomposition b (k n) (k (n+1)) x
      (by linarith [hr.1.2,hwq n]) (by linarith [hr.1.2,hwq (n+1)]) hh
      (hk n haway) (hk (n+1) haway')

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

lemma endpoint_power_identity {δ : ℝ} (hδ : 0 < δ) :
    δ * δ^(-(1/50 : ℝ)) / δ^(1/10 : ℝ) = δ^(22/25 : ℝ) := by
  have he : δ * δ^(-(1/50 : ℝ)) = δ^(1-(1/50 : ℝ)) := by
    simp only [Real.rpow_sub hδ, Real.rpow_one, Real.rpow_neg hδ.le, div_eq_mul_inv]
  rw [he, ← Real.rpow_sub hδ]
  norm_num

/-- The two geometric failure mechanisms have integrable superlevel powers. -/
lemma shell_tail_scaled {A t δ M : ℝ} (hA : 0 ≤ A) (ht : 0 < t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM0 : 0 ≤ M)
    (hM : M ≤ A*δ^(-(1/50 : ℝ))) :
    (ENNReal.ofReal (t*δ^(1/10 : ℝ)))⁻¹ ^ 2 *
      (ENNReal.ofReal (156*δ/δ^(1/5 : ℝ))*ENNReal.ofReal M*ENNReal.ofReal M) +
    (ENNReal.ofReal (t*δ^(1/10 : ℝ)))⁻¹ *
      ((ENNReal.ofReal (6*Real.pi)*ENNReal.ofReal (2*(200*δ/(δ^(1/5 : ℝ))^2)))*ENNReal.ofReal M) ≤
    ENNReal.ofReal (156*(A/t)^2*δ^(14/25 : ℝ)+2400*Real.pi*(A/t)*δ^(9/25 : ℝ)) := by
  have hU : 0 < t*δ^(1/10 : ℝ) := mul_pos ht (Real.rpow_pos_of_pos hδ _)
  rw [← ENNReal.ofReal_inv_of_pos hU, ← ENNReal.ofReal_pow (inv_nonneg.mpr hU.le)]
  have hp : 0 ≤ 156*δ/δ^(1/5 : ℝ) := by positivity
  have hp' : 0 ≤ 2*(200*δ/(δ^(1/5 : ℝ))^2) := by positivity
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
      _ = 156*(A/t)^2*δ^(14/25 : ℝ) := by
        rw [← first_power_identity hδ]
        simp only [mul_inv_rev]
        ring
  have hsecond : (t*δ^(1/10 : ℝ))⁻¹ *
      (6*Real.pi*(2*(200*δ/(δ^(1/5 : ℝ))^2))*M) ≤
      2400*Real.pi*(A/t)*δ^(9/25 : ℝ) := by
    calc
      _ ≤ (t*δ^(1/10 : ℝ))⁻¹ *
          (6*Real.pi*(2*(200*δ/(δ^(1/5 : ℝ))^2))*(A*δ^(-(1/50 : ℝ)))) := by gcongr
      _ = 2400*Real.pi*(A/t)*δ^(12/25 : ℝ) := by
        rw [← second_power_identity hδ]
        simp only [mul_inv_rev]
        ring
      _ ≤ 2400*Real.pi*(A/t)*δ^(9/25 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)) (by positivity)
  exact add_le_add hfirst hsecond

lemma endpoint_tail_scaled {A t δ M : ℝ} (hA : 0 ≤ A) (ht : 0 < t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : M ≤ A*δ^(-(1/50 : ℝ))) :
    ENNReal.ofReal (24*Real.pi*δ)*ENNReal.ofReal M / ENNReal.ofReal (t*δ^(1/10 : ℝ)) ≤
    ENNReal.ofReal (24*Real.pi*(A/t)*δ^(9/25 : ℝ)) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_div_of_pos (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (24*Real.pi*δ)*(A*δ^(-(1/50 : ℝ)))/(t*δ^(1/10 : ℝ)) := by gcongr
    _ = 24*Real.pi*(A/t)*δ^(22/25 : ℝ) := by
      rw [← endpoint_power_identity hδ]
      ring
    _ ≤ 24*Real.pi*(A/t)*δ^(9/25 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)) (by positivity)

end DiskScales

namespace DiskScales

lemma norm_geometric_rpow_lt {p : ℝ} (hp : 0 < p) : (1/2 : ℝ)^p < 1 :=
  Real.rpow_lt_one (by norm_num) (by norm_num) hp

lemma raw_endpoint_tail_scaled {A t δ M : ℝ} (hA : 0 ≤ A) (ht : 0 < t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM0 : 0 ≤ M)
    (hM : M ≤ A*δ^(-(1/50 : ℝ))) :
    (ENNReal.ofReal (t*δ^(1/10 : ℝ)))⁻¹ ^ 2 *
      (ENNReal.ofReal (156*δ/δ^(1/5 : ℝ))*ENNReal.ofReal M*ENNReal.ofReal M) +
    (ENNReal.ofReal (t*δ^(1/10 : ℝ)))⁻¹ *
      ((ENNReal.ofReal (6*Real.pi)*ENNReal.ofReal (2*(200*δ/(δ^(1/5 : ℝ))^2)))*ENNReal.ofReal M) +
    ENNReal.ofReal (24*Real.pi*δ)*ENNReal.ofReal M/ENNReal.ofReal (t*δ^(1/10 : ℝ)) ≤
    ENNReal.ofReal (156*(A/t)^2*δ^(14/25 : ℝ)+2424*Real.pi*(A/t)*δ^(9/25 : ℝ)) := by
  calc
    _ ≤ ENNReal.ofReal (156*(A/t)^2*δ^(14/25 : ℝ)+2400*Real.pi*(A/t)*δ^(9/25 : ℝ)) +
          ENNReal.ofReal (24*Real.pi*(A/t)*δ^(9/25 : ℝ)) :=
      add_le_add (shell_tail_scaled hA ht hδ hδ1 hM0 hM)
        (endpoint_tail_scaled hA ht hδ hδ1 hM)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

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

lemma size_start_identity {Cs A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    (1+216*Cs)/(A/t)^(1/100 : ℝ)*A+
      (16+4538*Cs)*t*(A/t)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) =
    t*((1+216*Cs)*(A/t)^(99/100 : ℝ)+
      (16+4538*Cs)*(A/t)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) := by
  have hq : 0 < A/t := div_pos hA ht
  have he : (A/t)/(A/t)^(1/100 : ℝ) = (A/t)^(99/100 : ℝ) := by
    have hh := Real.rpow_sub hq (1 : ℝ) (1/100 : ℝ)
    norm_num at hh
    exact hh.symm
  have hAt : t*(A/t) = A := by field_simp
  calc
    _ = t*((1+216*Cs)*((A/t)/(A/t)^(1/100 : ℝ))+
      (16+4538*Cs)*(A/t)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) := by
        rw [mul_add]
        congr 1
        · calc
            _ = (1+216*Cs)/(A/t)^(1/100 : ℝ)*(t*(A/t)) := by rw [hAt]
            _ = _ := by ring
        · ring
    _ = _ := by rw [he]

/-- One fixed small-width cutoff enforces geometry and the strict endpoint
size threshold at every smaller positive width. -/
lemma exists_size_parameters (Cs : ℝ) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1/4 ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ d₀ → δ ≤ (δ^(1/5 : ℝ))^2/1600) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
        (1+216*Cs)*δ^(99/100 : ℝ)+
          (16+4538*Cs)*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) ≤ 1) := by
  obtain ⟨d,hd,hdq,hgeom⟩ := exists_admissible_width
  have ht : Tendsto (fun δ : ℝ => (1+216*Cs)*δ^(99/100 : ℝ)+
      (16+4538*Cs)*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) (𝓝 0) (𝓝 0) := by
    have h1 := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 99/100)).tendsto 0
    have h2 := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1/10)).tendsto 0
    simpa using (h1.const_mul (1+216*Cs)).add ((h2.const_mul (16+4538*Cs)).div_const _)
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

namespace LocalCancellation
open DiskKernels DiskMoments DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

/-- The uniform integrable superlevel tail, with both forced band endpoints.
The only decomposition assumption is equality of the specified densities on
each observation disk. No direction positivity is needed for this size bound. -/
theorem size_tail {Cs : ℝ} (hCs : 0 ≤ Cs) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ {ι : Type*} [Fintype ι] (b : ι → ErrorPiece Cs),
      0 < errorPrice b (1/100) → ∀ t : ℝ, L*errorPrice b (1/100) ≤ t →
      ∀ g : ℂ → ℝ, ContDiff ℝ 1 g →
      ∃ E : Set ℂ, MeasurableSet E ∧
        volume E ≤ ENNReal.ofReal (sizeTailConstant*(errorPrice b (1/100)/t)^(34/25 : ℝ)) ∧
        ∀ x ∉ E,
          (∀ᵐ y, y ∈ Metric.ball x 3 → ∑ j, (b j).density y = gradient g y) →
          ∀ r, EndpointRadius g x r → ‖∫ y in Metric.ball x r, gradient g y‖ ≤ t := by
  obtain ⟨d₀,hd0,hdq,hgeom,hsmall⟩ := exists_size_parameters Cs
  have hL : 1 ≤ (1 : ℝ)/d₀ := (le_div_iff₀ hd0).mpr (by linarith)
  refine ⟨1/d₀,hL,?_⟩
  intro ι _ b hA t ht g hg
  let A := errorPrice b (1/100)
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
  obtain ⟨E,hE,hEv,hEst⟩ := size_endpoint_raw b hCs hq0 hqq
    (fun δ hδ hδq => hgeom δ hδ (hδq.trans hqd)) ht0 hAt hg
  refine ⟨E,hE,?_,?_⟩
  · apply hEv.trans
    calc
      _ ≤ ∑' n : ℕ, ENNReal.ofReal
          (156*(A/t)^2*(width (A/t) n)^(14/25 : ℝ)+
            2424*Real.pi*(A/t)*(width (A/t) n)^(9/25 : ℝ)) := by
        apply ENNReal.tsum_le_tsum
        intro n
        have hw0 : 0 < width (A/t) n := width_pos hq0 n
        have hw1 : width (A/t) n ≤ 1 := (width_le hq0.le n).trans hq1
        apply raw_endpoint_tail_scaled hA.le ht0 hw0 hw1 (coarseMass_nonneg b _ _)
        have hh := coarseMass_bound b (by norm_num : (0 : ℝ) ≤ 1/100) hw0
        norm_num at hh
        rw [Real.rpow_neg hw0.le]
        exact hh
      _ = ENNReal.ofReal
          ((156/(1-(1/2 : ℝ)^(14/25 : ℝ)))*(A/t)^(64/25 : ℝ)+
            (2424*Real.pi/(1-(1/2 : ℝ)^(9/25 : ℝ)))*(A/t)^(34/25 : ℝ)) := by
        rw [geometric_tail_sum hA.le ht0 hq0.le, starting_width_tail hA ht0]
      _ ≤ ENNReal.ofReal (sizeTailConstant*(A/t)^(34/25 : ℝ)) :=
        ENNReal.ofReal_le_ofReal (collapse_size_tail hq0 hq1)
  · intro x hx hh r hr
    apply (hEst x hx hh r hr).trans
    rw [size_start_identity hA ht0]
    exact (mul_le_mul_of_nonneg_left (hsmall _ hq0 hqd) ht0.le).trans_eq (mul_one t)

end LocalCancellation

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

/-- A simultaneous Borel integrable price for every admissible disk gradient.
The constant is independent of the number of pieces. -/
theorem size_majorant {Cs : ℝ} (hCs : 0 ≤ Cs) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] (b : ι → ErrorPiece Cs)
      (g : ℂ → ℝ), ContDiff ℝ 1 g → ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
      ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
        (∫⁻ x in Q, F x) ≤ ENNReal.ofReal (C*errorPrice b (1/100)) ∧
        ∀ x, (∀ᵐ y, y ∈ Metric.ball x 3 → ∑ j, (b j).density y = gradient g y) →
          ∀ r, EndpointRadius g x r →
            ENNReal.ofReal ‖∫ y in Metric.ball x r, gradient g y‖ ≤ F x := by
  obtain ⟨L,hL,hsize⟩ := size_tail hCs
  let c : ℝ := (1/2 : ℝ)^(34/25 : ℝ)
  have hc : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hc1 : 2*c < 1 := by
    have hh := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1/2)
      (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 34/25)
    norm_num at hh
    linarith
  let C := L*(1+2*sizeTailConstant/(1-2*c))
  have hC : 0 < C := mul_pos (by linarith) (by
    have := sizeTailConstant_pos
    have := sub_pos.mpr hc1
    positivity)
  refine ⟨C,hC,?_⟩
  intro ι _ b g hg Q hQ
  let A := errorPrice b (1/100)
  by_cases hAz : A = 0
  · refine ⟨0,measurable_const,?_,?_⟩
    · simp only [Pi.zero_apply, lintegral_zero, A, hAz, mul_zero, ENNReal.ofReal_zero, le_refl]
    · intro x hh r hr
      have hz := errorPrice_zero b hAz
      have hs : (∑ j, ∫ y in Metric.ball x r, (b j).density y) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        exact integral_eq_zero_of_ae ((ae_restrict_of_ae (hz j)))
      have he := ball_pairing_decomposition b x (by linarith [hr.1.2] : r ≤ 3) hh
      rw [← he,hs,norm_zero,ENNReal.ofReal_zero]
      exact le_refl _
  · have hA : 0 < A := lt_of_le_of_ne (errorPrice_nonneg b _) (Ne.symm hAz)
    have ht : 0 < L*A := mul_pos (by linarith) hA
    have hts (n : ℕ) : L*A ≤ L*A*2^n := le_mul_of_one_le_right ht.le (one_le_pow₀ (by norm_num))
    choose E hE hEv hbound using fun n : ℕ => hsize b hA (L*A*2^n) (hts n) g hg
    refine ⟨DyadicMajorant.price (L*A) E, DyadicMajorant.measurable_price _ hE,?_,?_⟩
    · have htail (n : ℕ) : volume (E n) ≤ ENNReal.ofReal (sizeTailConstant*c^n) := by
        apply (hEv n).trans
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ sizeTailConstant_pos.le
        calc
          _ ≤ ((1/2 : ℝ)^n)^(34/25 : ℝ) := Real.rpow_le_rpow (by positivity) (dyadic_ratio hA hL n) (by norm_num)
          _ = c^n := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm (n : ℝ),
              Real.rpow_mul (by norm_num), Real.rpow_natCast]
      have hi := DyadicMajorant.lintegral_price_geometric volume (by norm_num : (0 : ℝ) ≤ 1) hQ ht.le
        sizeTailConstant_pos.le hc hc1 hE htail
      convert hi using 1
      congr 1
      dsimp [C,A]
      ring
    · intro x hh r hr
      apply DyadicMajorant.majorizes ht
      intro n hn
      exact hbound n x hn hh r hr

end LocalCancellation

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.MaximalEstimates
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

noncomputable section

namespace DiskMaximalTools

lemma volume_dilate_five (x : ℂ) (r : ℝ) :
    volume (ball x (5*r)) = 25 * volume (ball x r) := by
  rw [Complex.volume_ball, Complex.volume_ball, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5)]
  norm_num [mul_pow]
  ring

/-- The actual Vitali weak-(1,1) estimate, with no assumed maximal inequality. -/
theorem weak_bound_bounded_family {ι : Type*} (t : Set ι) (x : ι → ℂ) (r : ι → ℝ)
    (ν : Measure ℂ) {R a : ℝ} (ha : 0 < a)
    (hr : ∀ i ∈ t, 0 < r i) (hR : ∀ i ∈ t, r i ≤ R)
    (hav : ∀ i ∈ t, ENNReal.ofReal a * volume (ball (x i) (r i)) ≤ ν (ball (x i) (r i))) :
    volume (⋃ i ∈ t, ball (x i) (r i)) ≤ (25 / ENNReal.ofReal a) * ν univ := by
  obtain ⟨u,hut,hdisj,hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    t x r R hR 5 (by norm_num)
  have huc : u.Countable := hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun i hi => ⟨x i,mem_ball_self (hr i (hut hi))⟩)
  have : Countable u := huc.to_subtype
  have hsub : (⋃ i ∈ t, ball (x i) (r i)) ⊆ ⋃ i : u, ball (x i) (5*r i) := by
    intro y hy
    obtain ⟨i,hi,hy⟩ := mem_iUnion₂.mp hy
    obtain ⟨j,hj,hij⟩ := hcover i hi
    exact mem_iUnion.mpr ⟨⟨j,hj⟩,hij hy⟩
  have hmass : (∑' i : u, ν (ball (x i) (r i))) ≤ ν univ := by
    rw [← measure_iUnion (fun (i j : u) hij => hdisj i.property j.property (fun h => hij (Subtype.ext h)))
      (fun _ => measurableSet_ball)]
    exact measure_mono (subset_univ _)
  calc
    _ ≤ volume (⋃ i : u, ball (x i) (5*r i)) := measure_mono hsub
    _ ≤ ∑' i : u, volume (ball (x i) (5*r i)) := measure_iUnion_le _
    _ = ∑' i : u, 25 * volume (ball (x i) (r i)) := by simp_rw [volume_dilate_five]
    _ ≤ ∑' i : u, (25 / ENNReal.ofReal a) * ν (ball (x i) (r i)) := by
      apply ENNReal.tsum_le_tsum
      intro i
      have hb := hav i (hut i.property)
      calc
        _ = (25 / ENNReal.ofReal a) * (ENNReal.ofReal a * volume (ball (x i) (r i))) := by
          rw [← mul_assoc, ENNReal.div_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr ha)) ENNReal.ofReal_ne_top]
        _ ≤ _ := by gcongr
    _ = (25 / ENNReal.ofReal a) * ∑' i : u, ν (ball (x i) (r i)) := by rw [ENNReal.tsum_mul_left]
    _ ≤ _ := by gcongr

lemma volume_disk_real (x : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume (ball x r) = ENNReal.ofReal (Real.pi*r^2) := by
  rw [Complex.volume_ball,ENNReal.ofReal_mul Real.pi_nonneg,ENNReal.ofReal_pow hr]
  rw [← (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (NNReal.pi : ℝ) = (NNReal.pi : ℝ≥0∞))]
  exact mul_comm _ _

/-- All high-average balls of a finite measure have a common finite radius
bound; the bounded-family Vitali argument therefore controls every radius. -/
theorem weak_bound {ν : Measure ℂ} [IsFiniteMeasure ν] {a : ℝ} (ha : 0 < a) :
    volume {x : ℂ | ∃ r : ℝ, 0 < r ∧
      ENNReal.ofReal a * volume (ball x r) ≤ ν (ball x r)} ≤
      (25 / ENNReal.ofReal a) * ν univ := by
  let t : Set (ℂ × ℝ) := {p | 0 < p.2 ∧
    ENNReal.ofReal a * volume (ball p.1 p.2) ≤ ν (ball p.1 p.2)}
  let B : ℝ := (ν univ).toReal/(a*Real.pi)
  have hB : 0 ≤ B := div_nonneg ENNReal.toReal_nonneg (mul_pos ha Real.pi_pos).le
  have hR : ∀ p ∈ t, p.2 ≤ B+1 := by
    intro p hp
    have hh := hp.2.trans (measure_mono (subset_univ _))
    rw [volume_disk_real _ hp.1.le,← ENNReal.ofReal_mul ha.le] at hh
    have hh' : a*(Real.pi*p.2^2) ≤ (ν univ).toReal := by
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hh
    have hs : p.2^2 ≤ B := (le_div_iff₀ (mul_pos ha Real.pi_pos)).mpr (by nlinarith)
    nlinarith [sq_nonneg (p.2-1)]
  have hweak := weak_bound_bounded_family t Prod.fst Prod.snd ν ha
    (fun _ hp => hp.1) hR (fun _ hp => hp.2)
  apply le_trans (measure_mono ?_) hweak
  intro x hx
  obtain ⟨r,hr,havg⟩ := hx
  exact mem_iUnion₂.mpr ⟨(x,r),⟨hr,havg⟩,mem_ball_self hr⟩

lemma measurable_ball_mass (ν : Measure ℂ) [SFinite ν] (r : ℝ) :
    Measurable (fun x : ℂ => ν (ball x r)) := by
  have hm : MeasurableSet {p : ℂ × ℂ | dist p.2 p.1 < r} :=
    isOpen_lt (continuous_snd.dist continuous_fst) continuous_const |>.measurableSet
  exact measurable_measure_prodMk_left hm

lemma measurable_rationalMaximal (ν : Measure ℂ) [SFinite ν] :
    Measurable (rationalMaximal ν) := by
  unfold rationalMaximal
  apply Measurable.iSup
  intro q
  apply Measurable.iSup
  intro _
  have hd : Measurable (fun x : ℂ => volume (ball x (q:ℝ))) := by
    simp only [Complex.volume_ball]
    exact measurable_const
  exact (measurable_ball_mass ν (q:ℝ)).div hd

/-- Truncating an input below half the testing height sharpens weak type by
charging only its large values. This is the interpolation mechanism. -/
lemma weak_split {ν η : Measure ℂ} [IsFiniteMeasure η] {a : ℝ} (ha : 0 < a)
    (hsplit : ∀ x r, 0 < r → ν (ball x r) ≤ η (ball x r)+
      ENNReal.ofReal (a/2)*volume (ball x r)) :
    volume {x | ENNReal.ofReal a < rationalMaximal ν x} ≤
      (25 / ENNReal.ofReal (a/2)) * η univ := by
  apply le_trans (measure_mono ?_) (weak_bound (by linarith : 0 < a/2))
  intro x hx
  change ENNReal.ofReal a < ⨆ (q : ℚ) (_ : 0 < q), ν (ball x q) / volume (ball x q) at hx
  obtain ⟨q,hh⟩ := lt_iSup_iff.mp hx
  obtain ⟨hq,hh⟩ := lt_iSup_iff.mp hh
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hv0 : volume (ball x (q:ℝ)) ≠ 0 := by
    rw [volume_disk_real _ hq'.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hq')))
  have hh' := (ENNReal.lt_div_iff_mul_lt (Or.inl hv0) (Or.inl measure_ball_lt_top.ne)).mp hh
  refine ⟨q,hq',?_⟩
  by_contra h
  have hη : η (ball x (q:ℝ)) ≤ ENNReal.ofReal (a/2)*volume (ball x (q:ℝ)) := (lt_of_not_ge h).le
  have hfull := (hsplit x q hq').trans (add_le_add hη le_rfl)
  have hsum : ENNReal.ofReal (a/2)+ENNReal.ofReal (a/2) = ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_add (by linarith : 0 ≤ a/2) (by linarith : 0 ≤ a/2)]
    congr 1
    ring
  rw [← add_mul,hsum] at hfull
  exact (not_lt_of_ge hfull) hh'

lemma weak_truncated {f : ℂ → ℝ≥0∞} (hf : Measurable f)
    [IsFiniteMeasure (volume.withDensity f)] {a : ℝ} (ha : 0 < a) :
    volume {x | ENNReal.ofReal a < rationalMaximal (volume.withDensity f) x} ≤
      (25 / ENNReal.ofReal (a/2)) *
        ∫⁻ x, {x | ENNReal.ofReal (a/2) < f x}.indicator f x := by
  let H := {x | ENNReal.ofReal (a/2) < f x}
  let η := volume.withDensity (H.indicator f)
  have hle : η ≤ volume.withDensity f := withDensity_mono (ae_of_all _ (indicator_le_self _ _))
  have : IsFiniteMeasure η := isFiniteMeasure_of_le _ hle
  have hweak := weak_split (ν := volume.withDensity f) (η := η) ha ?_
  · simpa only [η,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ] using hweak
  · intro x r _
    rw [withDensity_apply _ measurableSet_ball,show η = volume.withDensity (H.indicator f) from rfl,
      withDensity_apply _ measurableSet_ball]
    calc
      _ ≤ ∫⁻ y in ball x r, H.indicator f y+ENNReal.ofReal (a/2) := by
        apply lintegral_mono
        intro y
        dsimp only
        by_cases hy : y ∈ H
        · rw [indicator_of_mem hy]
          exact le_add_right le_rfl
        · rw [indicator_of_notMem hy,zero_add]
          exact le_of_not_gt hy
      _ = _ := by
        rw [lintegral_add_left (hf.indicator (measurableSet_lt measurable_const hf))]
        simp only [lintegral_const,Measure.restrict_apply_univ]
        rfl

end DiskMaximalTools

open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace DiskMaximalTools

lemma lintegral_rpow_Ioo {b s : ℝ} (hb : 0 ≤ b) (hs : -1 < s) :
    (∫⁻ t in Ioo 0 b, ENNReal.ofReal (t^s)) = ENNReal.ofReal (b^(s+1)/(s+1)) := by
  rcases eq_or_lt_of_le hb with rfl | hb
  · simp [Real.zero_rpow (by linarith : s+1 ≠ 0)]
  · have hi : IntegrableOn (fun t : ℝ => t^s) (Ioo 0 b) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hb).mpr hs
    rw [← ofReal_integral_eq_lintegral_ofReal hi]
    · rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hb.le,
        integral_rpow (Or.inl hs)]
      simp [Real.zero_rpow (by linarith : s+1 ≠ 0)]
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
      exact Real.rpow_nonneg ht.1.le _

lemma truncation_layer_single {b p : ℝ} (hb : 0 ≤ b) (hp : 1 < p) :
    (∫⁻ t in Ioi 0, (if t < 2*b then ENNReal.ofReal b else 0)*ENNReal.ofReal (t^(p-2))) =
      ENNReal.ofReal (2^(p-1)/(p-1))*ENNReal.ofReal (b^p) := by
  have heq : (fun t : ℝ => (if t < 2*b then ENNReal.ofReal b else 0)*ENNReal.ofReal (t^(p-2))) =
      (Iio (2*b)).indicator (fun t => ENNReal.ofReal b * ENNReal.ofReal (t^(p-2))) := by
    funext t
    by_cases ht : t < 2*b <;> simp [ht]
  rw [heq,lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
  have hi : Iio (2*b) ∩ Ioi (0:ℝ) = Ioo 0 (2*b) := by ext t; simp [and_comm]
  rw [hi,lintegral_const_mul'' _ (by fun_prop)]
  rw [lintegral_rpow_Ioo (by positivity : 0 ≤ 2*b) (by linarith : -1 < p-2)]
  have hpp : p-2+1 = p-1 := by ring
  rw [hpp]
  have h2 : 0 ≤ (2:ℝ)^(p-1)/(p-1) := div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
  rw [← ENNReal.ofReal_mul hb,← ENNReal.ofReal_mul h2]
  congr 1
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hb]
  have hp0 : 0 < p-1 := by linarith
  have hpow : b*b^(p-1) = b^p := by
    rcases eq_or_lt_of_le hb with rfl | hb
    · simp [Real.zero_rpow hp0.ne',Real.zero_rpow (by linarith : p ≠ 0)]
    · calc
        b*b^(p-1) = b^(1:ℝ)*b^(p-1) := by rw [Real.rpow_one]
        _ = b^(1+(p-1)) := (Real.rpow_add hb _ _).symm
        _ = b^p := by congr 1; ring
  calc
    b * (2^(p-1)*b^(p-1)/(p-1)) = (2^(p-1)/(p-1))*(b*b^(p-1)) := by ring
    _ = _ := by rw [hpow]

/-- Exact Tonelli computation behind strong maximal interpolation, for every
p > 1. The singularity at testing height zero is actually integrated. -/
theorem truncation_layer_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SFinite μ] {f : α → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 1 < p) :
    (∫⁻ t in Ioi 0,
      (∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0 ∂μ)*ENNReal.ofReal (t^(p-2))) =
      ENNReal.ofReal (2^(p-1)/(p-1))*(∫⁻ x, ENNReal.ofReal ((f x)^p) ∂μ) := by
  have hm : Measurable (fun z : ℝ × α =>
      (if z.1 < 2*f z.2 then ENNReal.ofReal (f z.2) else 0)*ENNReal.ofReal (z.1^(p-2))) := by
    apply Measurable.mul
    · exact ((hf.comp measurable_snd).ennreal_ofReal).ite
        (measurableSet_lt measurable_fst ((hf.comp measurable_snd).const_mul 2)) measurable_const
    · exact (measurable_fst.pow_const _).ennreal_ofReal
  calc
    _ = ∫⁻ t in Ioi 0, ∫⁻ x,
        (if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2)) ∂μ := by
      apply lintegral_congr
      intro t
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ x, (∫⁻ t in Ioi 0,
        (if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2))) ∂μ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ x, ENNReal.ofReal (2^(p-1)/(p-1))*ENNReal.ofReal ((f x)^p) ∂μ := by
      apply lintegral_congr
      intro x
      exact truncation_layer_single (hf0 x) hp
    _ = _ := lintegral_const_mul'' _ ((hf.pow_const _).ennreal_ofReal.aemeasurable)

end DiskMaximalTools

namespace DiskMaximalTools

lemma maximal_layer_coefficient {t p : ℝ} (ht : 0 < t) :
    (25 / ENNReal.ofReal (t/2))*ENNReal.ofReal (t^(p-1)) =
      ENNReal.ofReal 50*ENNReal.ofReal (t^(p-2)) := by
  rw [← show ENNReal.ofReal (25:ℝ) = 25 by norm_num,
    ← ENNReal.ofReal_div_of_pos (by linarith : 0 < t/2),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (25:ℝ)/(t/2)),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 50)]
  congr 1
  have hpow : t^(p-1) = t*t^(p-2) := by
    calc
      _ = t^(1+(p-2)) := by congr 1; ring
      _ = t^(1:ℝ)*t^(p-2) := Real.rpow_add ht _ _
      _ = _ := by rw [Real.rpow_one]
  rw [hpow]
  field_simp
  ring

/-- A full strong p estimate from Vitali, truncation and Tonelli. No maximal
inequality is supplied as an assumption. The real representative is controlled
even before a separate almost-everywhere finiteness argument. -/
theorem strong_rationalMaximal {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) [IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x)))]
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, ENNReal.ofReal ((rationalMaximal (volume.withDensity (fun x => ENNReal.ofReal (f x))) x).toReal^p)) ≤
      ENNReal.ofReal (50*p*2^(p-1)/(p-1)) * (∫⁻ x, ENNReal.ofReal ((f x)^p)) := by
  let M := rationalMaximal (volume.withDensity (fun x => ENNReal.ofReal (f x)))
  have hM : Measurable M := measurable_rationalMaximal _
  have htail (t : ℝ) (ht : 0 < t) : volume {x | t < (M x).toReal} ≤
      (25/ENNReal.ofReal (t/2)) * ∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0 := by
    have hsub : {x | t < (M x).toReal} ⊆ {x | ENNReal.ofReal t < M x} := by
      intro x hx
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mpr hx |>.trans_le ENNReal.ofReal_toReal_le
    apply le_trans (measure_mono hsub)
    have hweak := weak_truncated hf.ennreal_ofReal ht
    apply hweak.trans_eq
    congr 1
    apply lintegral_congr
    intro x
    have heq : ENNReal.ofReal (t/2) < ENNReal.ofReal (f x) ↔ t < 2*f x := by
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith : 0 ≤ t/2)]
      constructor <;> intro h <;> linarith
    simp only [Set.indicator,Set.mem_ofPred_eq,heq]
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul volume (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))
    hM.ennreal_toReal.aemeasurable (by linarith : 0 < p)]
  have hlayer : (∫⁻ t in Ioi 0, volume {x | t < (M x).toReal}*ENNReal.ofReal (t^(p-1))) ≤
      ENNReal.ofReal 50 * (∫⁻ t in Ioi 0,
        (∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2))) := by
    calc
      _ ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal 50 *
          ((∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2))) := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        calc
          _ ≤ ((25/ENNReal.ofReal (t/2)) * ∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*
              ENNReal.ofReal (t^(p-1)) := by gcongr; exact htail t ht
          _ = _ := by
            rw [mul_right_comm, maximal_layer_coefficient ht]
            ring
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc
    _ ≤ ENNReal.ofReal p*(ENNReal.ofReal 50 * (∫⁻ t in Ioi 0,
        (∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2)))) := by
      gcongr
    _ = _ := by
      rw [truncation_layer_integral hf hf0 hp]
      have hc : ENNReal.ofReal p*(ENNReal.ofReal 50 * ENNReal.ofReal (2^(p-1)/(p-1))) =
          ENNReal.ofReal (50*p*2^(p-1)/(p-1)) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 50),
          ← ENNReal.ofReal_mul (by linarith : 0 ≤ p)]
        congr 1
        ring
      simpa only [mul_assoc] using congrArg
        (fun c => c*(∫⁻ x, ENNReal.ofReal ((f x)^p))) hc

end DiskMaximalTools

namespace DiskMaximalTools

lemma disk_average_le_rationalMaximal_exact (ν : Measure ℂ) (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ν (ball x r) / volume (ball x r) ≤ rationalMaximal ν x := by
  let I := {q : ℚ // 0 < q ∧ (q:ℝ) < r}
  have hdir : Directed (· ⊆ ·) (fun q : I => ball x (q:ℚ)) := by
    intro i j
    refine ⟨⟨max i.val j.val,?_,?_⟩,?_,?_⟩
    · exact lt_max_of_lt_left i.property.1
    · exact_mod_cast max_lt i.property.2 j.property.2
    · exact ball_subset_ball (by exact_mod_cast le_max_left i.val j.val)
    · exact ball_subset_ball (by exact_mod_cast le_max_right i.val j.val)
  have heq : (⋃ q : I, ball x (q:ℚ)) = ball x r := by
    ext y
    constructor
    · intro hy
      obtain ⟨q,hq⟩ := mem_iUnion.mp hy
      exact (ball_subset_ball q.property.2.le) hq
    · intro hy
      have hd : dist y x < r := hy
      obtain ⟨q,hq0,hqr⟩ := exists_rat_btwn (show max 0 (dist y x) < r by exact max_lt hr hd)
      have hq : 0 < (q:ℝ) := lt_of_le_of_lt (le_max_left _ _) hq0
      have hqRat : (0:ℚ) < q := by exact_mod_cast hq
      refine mem_iUnion.mpr ⟨⟨q,hqRat,hqr⟩,?_⟩
      exact lt_of_le_of_lt (le_max_right _ _) hq0
  have hv0 : volume (ball x r) ≠ 0 := by
    rw [volume_disk_real _ hr.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hr)))
  apply (ENNReal.div_le_iff hv0 measure_ball_lt_top.ne).mpr
  rw [← heq,hdir.measure_iUnion]
  apply iSup_le
  intro q
  have hq0 : 0 < (q.val:ℝ) := by exact_mod_cast q.property.1
  have hqv : volume (ball x (q.val:ℝ)) ≠ 0 := by
    rw [volume_disk_real _ hq0.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hq0)))
  have hav : ν (ball x (q.val:ℝ)) / volume (ball x (q.val:ℝ)) ≤ rationalMaximal ν x :=
    le_iSup_of_le q.val (le_iSup_of_le q.property.1 le_rfl)
  calc
    _ ≤ rationalMaximal ν x * volume (ball x (q.val:ℝ)) :=
      (ENNReal.div_le_iff hqv measure_ball_lt_top.ne).mp hav
    _ ≤ _ := by
      gcongr
      exact subset_iUnion (fun q : I => ball x (q:ℚ)) q

lemma rationalMaximal_le_of_density_le {f : ℂ → ℝ≥0∞} {B : ℝ≥0∞} (hf : ∀ x, f x ≤ B) (x : ℂ) :
    rationalMaximal (volume.withDensity f) x ≤ B := by
  unfold rationalMaximal
  apply iSup_le
  intro q
  apply iSup_le
  intro hq
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hv0 : volume (ball x (q:ℝ)) ≠ 0 := by
    rw [volume_disk_real _ hq'.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hq')))
  apply (ENNReal.div_le_iff hv0 measure_ball_lt_top.ne).mpr
  rw [withDensity_apply _ measurableSet_ball]
  calc
    _ ≤ ∫⁻ y in ball x (q:ℝ), B := lintegral_mono hf
    _ = _ := by simp

end DiskMaximalTools

open MeasureTheory Set
open scoped ENNReal NNReal
end
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

open MeasureTheory Set Metric
open scoped ENNReal NNReal
noncomputable section
namespace PlanePotential

lemma dim_complex : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex

lemma volume_real_unit_ball : volume.real (ball (0:ℂ) 1) = Real.pi := by
  rw [measureReal_def,Complex.volume_ball]
  simp

lemma integral_radial (f : ℝ → ℝ) :
    (∫ x : ℂ, f ‖x‖) = 2*Real.pi * ∫ r in Ioi (0:ℝ), r*f r := by
  rw [integral_fun_norm_addHaar volume f]
  simp only [dim_complex,show (2:ℕ)-1=1 by rfl,pow_one,smul_eq_mul,volume_real_unit_ball,
    nsmul_eq_mul,Nat.cast_ofNat]
  ring

lemma integrable_radial_iff (f : ℝ → ℝ) :
    Integrable (fun x : ℂ => f ‖x‖) ↔ IntegrableOn (fun r => r*f r) (Ioi (0:ℝ)) := by
  simpa only [dim_complex,show (2:ℕ)-1=1 by rfl,pow_one,smul_eq_mul] using
    integrable_fun_norm_addHaar (E := ℂ) volume (f := f)

lemma radial_near_identity (a r : ℝ) {t : ℝ} (ht : 0 < t) :
    t * (Iio r).indicator (fun u : ℝ => u^a) t = (Ioo 0 r).indicator (fun u : ℝ => u^(a+1)) t := by
  by_cases htr : t < r
  · simp only [indicator_of_mem (show t ∈ Iio r from htr),indicator_of_mem (show t ∈ Ioo 0 r from ⟨ht,htr⟩)]
    rw [Real.rpow_add ht,Real.rpow_one,mul_comm]
  · simp only [indicator_of_notMem (show t ∉ Iio r from htr),indicator_of_notMem (show t ∉ Ioo 0 r by simp [htr]),mul_zero]

lemma integrable_norm_rpow_near {a r : ℝ} (ha : -2 < a) (hr : 0 < r) :
    IntegrableOn (fun x : ℂ => ‖x‖^a) (ball 0 r) := by
  rw [integrableOn_fun_norm_addHaar volume (f := fun t : ℝ => t^a)]
  simp only [dim_complex,show (2:ℕ)-1=1 by rfl,pow_one,smul_eq_mul]
  have hi : IntegrableOn (fun t : ℝ => t^(a+1)) (Ioo 0 r) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hr).mpr (by linarith)
  apply hi.congr_fun _ measurableSet_Ioo
  intro t ht
  change t^(a+1) = t*t^a
  rw [Real.rpow_add ht.1,Real.rpow_one,mul_comm]

/-- Exact planar singular-kernel integral; the center point is not excluded by
an unproved integrability convention. -/
theorem integral_norm_rpow_near {a r : ℝ} (ha : -2 < a) (hr : 0 < r) :
    (∫ x in ball (0:ℂ) r, ‖x‖^a) = 2*Real.pi * (r^(a+2)/(a+2)) := by
  have heq : (ball (0:ℂ) r).indicator (fun x => ‖x‖^a) =
      fun x : ℂ => (Iio r).indicator (fun t : ℝ => t^a) ‖x‖ := by
    funext x
    by_cases hx : ‖x‖ < r <;> simp [indicator,hx]
  rw [← integral_indicator measurableSet_ball,heq,integral_radial]
  have hinner : (∫ t in Ioi (0:ℝ), t*(Iio r).indicator (fun u : ℝ => u^a) t) =
      ∫ t in Ioo 0 r, t^(a+1) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => radial_near_identity a r ht)]
    rw [integral_indicator measurableSet_Ioo,Measure.restrict_restrict measurableSet_Ioo,
      inter_eq_left.mpr (Ioo_subset_Ioi_self)]
  rw [hinner,← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hr.le,
    integral_rpow (Or.inl (by linarith : -1 < a+1))]
  rw [show a+1+1=a+2 by ring,Real.zero_rpow (by linarith : a+2 ≠ 0),sub_zero]

lemma radial_far_identity (a r : ℝ) {t : ℝ} (ht : 0 < t) :
    t*(Ioi r).indicator (fun u : ℝ => u^a) t = (Ioi r).indicator (fun u : ℝ => u^(a+1)) t := by
  by_cases htr : r < t
  · simp only [indicator_of_mem (show t ∈ Ioi r from htr)]
    rw [Real.rpow_add ht,Real.rpow_one,mul_comm]
  · simp only [indicator_of_notMem (show t ∉ Ioi r from htr),mul_zero]

lemma integrable_norm_rpow_far {a r : ℝ} (ha : a < -2) (hr : 0 < r) :
    IntegrableOn (fun x : ℂ => ‖x‖^a) {x | r < ‖x‖} := by
  rw [← integrable_indicator_iff (measurableSet_lt measurable_const measurable_norm)]
  have heq : ({x : ℂ | r < ‖x‖}).indicator (fun x => ‖x‖^a) =
      fun x : ℂ => (Ioi r).indicator (fun t : ℝ => t^a) ‖x‖ := by rfl
  rw [heq,integrable_radial_iff]
  have hi : IntegrableOn (fun t : ℝ => t^(a+1)) (Ioi r) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hr
  have hi' : Integrable ((Ioi r).indicator (fun t : ℝ => t^(a+1))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hi
  apply hi'.integrableOn.congr_fun _ measurableSet_Ioi
  intro t ht
  exact (radial_far_identity a r ht).symm

theorem integral_norm_rpow_far {a r : ℝ} (ha : a < -2) (hr : 0 < r) :
    (∫ x : ℂ in {x | r < ‖x‖}, ‖x‖^a) = 2*Real.pi * (-r^(a+2)/(a+2)) := by
  have heq : ({x : ℂ | r < ‖x‖}).indicator (fun x => ‖x‖^a) =
      fun x : ℂ => (Ioi r).indicator (fun t : ℝ => t^a) ‖x‖ := by rfl
  rw [← integral_indicator (measurableSet_lt measurable_const measurable_norm),heq,integral_radial]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => radial_far_identity a r ht)]
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi hr.le),integral_Ioi_rpow_of_lt (by linarith : a+1 < -1) hr]
  congr 2
  rw [show a+1+1 = a+2 by ring]
  ring

end PlanePotential

open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section

open Finset
open scoped RealInnerProductSpace
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace PlanePotential

lemma segment_support {ψ : ℂ → ℝ} {R X : ℝ}
    (hψ : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) {x y : ℂ} (hx : ‖x‖ ≤ X)
    {t : ℝ} (ht : 0 < t) (hn : ψ (x+t⁻¹ • (y-x)) ≠ 0) :
    ‖y-x‖ ≤ t*(R+X) := by
  have heq : y-x = t • ((x+t⁻¹ • (y-x))-x) := by
    simp [ht.ne']
  calc
    ‖y-x‖ = t*‖(x+t⁻¹ • (y-x))-x‖ := by
      conv_lhs => rw [heq]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    _ ≤ t*(‖x+t⁻¹ • (y-x)‖+‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) ht.le
    _ ≤ t*(R+X) := mul_le_mul_of_nonneg_left (add_le_add (hψ _ hn) hx) ht.le

lemma integrable_power_cutoff {q δ B : ℝ} (hq : q < -1) (hδ : 0 < δ) :
    Integrable ((Ioi δ).indicator (fun t : ℝ => B*t^q)) := by
  apply (integrable_indicator_iff measurableSet_Ioi).mpr
  exact (integrableOn_Ioi_rpow_of_lt hq hδ).const_mul B

lemma integral_power_cutoff {q δ B : ℝ} (hq : q < -1) (hδ : 0 < δ) :
    (∫ t : ℝ, (Ioi δ).indicator (fun t : ℝ => B*t^q) t) = B*(-δ^(q+1)/(q+1)) := by
  rw [integral_indicator measurableSet_Ioi,integral_const_mul,integral_Ioi_rpow_of_lt hq hδ]

/-- A singular segment integral is genuinely integrable because of its geometric
lower cutoff. The bound retains the exact power, rather than a supremum times 1. -/
lemma singular_integral_bound {F : ℝ → ℝ} (hFm : Measurable F)
    {q δ B : ℝ} (hq : q < -1) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hzero : ∀ t ∈ Ioc (0:ℝ) 1, t < δ → F t = 0)
    (hbound : ∀ t ∈ Ioc (0:ℝ) 1, |F t| ≤ B*t^q) :
    IntegrableOn F (Ioc (0:ℝ) 1) ∧
      |∫ t in Ioc (0:ℝ) 1, F t| ≤ B*(-(δ/2)^(q+1)/(q+1)) := by
  let H := (Ioi (δ/2)).indicator (fun t : ℝ => B*t^q)
  have hH : Integrable H := integrable_power_cutoff hq (by linarith)
  have hH0 (t : ℝ) : 0 ≤ H t := by
    unfold H
    apply indicator_nonneg
    intro t ht
    exact mul_nonneg hB (Real.rpow_nonneg (by change δ/2 < t at ht; linarith) _)
  have hle : ∀ t ∈ Ioc (0:ℝ) 1, |F t| ≤ H t := by
    intro t ht
    by_cases hd : t < δ
    · rw [hzero t ht hd]
      simpa only [abs_zero] using hH0 t
    · have htδ : t ∈ Ioi (δ/2) := by change δ/2 < t; linarith
      change |F t| ≤ (Ioi (δ/2)).indicator (fun t : ℝ => B*t^q) t
      rw [indicator_of_mem htδ]
      exact hbound t ht
  have hFi : IntegrableOn F (Ioc (0:ℝ) 1) := by
    apply hH.integrableOn.mono' hFm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_eq_abs] using hle t ht
  refine ⟨hFi,?_⟩
  calc
    _ ≤ ∫ t in Ioc (0:ℝ) 1, |F t| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioc (0:ℝ) 1, H t := integral_mono_ae hFi.abs hH.integrableOn (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using hle t ht)
    _ ≤ ∫ t, H t := integral_mono_measure Measure.restrict_le_self (ae_of_all _ hH0) hH
    _ = _ := integral_power_cutoff hq (by linarith)

lemma greenScalar_measurable (ψ : ℂ → ℝ) (hψ : Measurable ψ) :
    Measurable (fun p : ℂ × ℂ => greenScalar ψ p.1 p.2) := by
  unfold greenScalar
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  have harg : Measurable (fun p : (ℂ × ℂ) × ℝ => p.1.1+p.2⁻¹ • (p.1.2-p.1.1)) := by measurability
  exact ((hψ.comp harg).mul (measurable_snd.pow_const _)).stronglyMeasurable

lemma green_measurable (ψ : ℂ → ℝ) (hψ : Measurable ψ) :
    Measurable (fun p : ℂ × ℂ => green ψ p.1 p.2) := by
  exact (greenScalar_measurable ψ hψ).neg.smul (measurable_snd.sub measurable_fst)

/-- Quantitative kernel size on every observation ball, with an explicit constant. -/
theorem green_norm_bound {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) {x y : ℂ} (hx : ‖x‖ ≤ X) (hxy : y ≠ x) :
    ‖green ψ x y‖ ≤ 2*B*(R+X)^2/‖y-x‖ := by
  have hd : 0 < ‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let δ := ‖y-x‖/(R+X)
  have hδ : 0 < δ := div_pos hd hM
  have hFm : Measurable (fun t : ℝ => ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)) := by
    apply Measurable.mul
    · apply hψm.comp
      measurability
    · exact measurable_id.pow_const _
  have hzero : ∀ t ∈ Ioc (0:ℝ) 1, t < δ → ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ) = 0 := by
    intro t ht hlt
    have hψ0 : ψ (x+t⁻¹ • (y-x)) = 0 := by
      by_contra hn
      have hs := segment_support hψs hx ht.1 hn
      have : t*(R+X) < ‖y-x‖ := (lt_div_iff₀ hM).mp hlt
      linarith
    rw [hψ0,zero_mul]
  have hb : ∀ t ∈ Ioc (0:ℝ) 1,
      |ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)| ≤ B*t^(-3:ℝ) := by
    intro t ht
    rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    exact mul_le_mul_of_nonneg_right (hψB _) (Real.rpow_nonneg ht.1.le _)
  have h := (singular_integral_bound hFm (by norm_num : (-3:ℝ) < -1) hδ hB hzero hb).2
  change |greenScalar ψ x y| ≤ _ at h
  have hrpow : (δ/2)^((-3:ℝ)+1) = (δ/2)^(-2:ℤ) := by norm_num [Real.rpow_intCast]
  rw [hrpow,zpow_neg,zpow_ofNat] at h
  have hs : |greenScalar ψ x y| ≤ 2*B*(R+X)^2/‖y-x‖^2 := by
    convert h using 1
    dsimp [δ]
    field_simp
    ring
  rw [green,norm_smul,Real.norm_eq_abs,abs_neg]
  calc
    _ ≤ (2*B*(R+X)^2/‖y-x‖^2)*‖y-x‖ := mul_le_mul_of_nonneg_right hs hd.le
    _ = _ := by field_simp

lemma segment_integrand_measurable {ψ : ℂ → ℝ} (hψ : Measurable ψ) (x y : ℂ) :
    Measurable (fun t : ℝ => ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)) := by
  apply Measurable.mul
  · apply hψ.comp
    measurability
  · exact measurable_id.pow_const _

lemma scalar_data {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B δ : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hδ : 0 < δ)
    {x y : ℂ} (hx : ‖x‖ ≤ X) (hd : δ*(R+X) ≤ ‖y-x‖) :
    IntegrableOn (fun t : ℝ => ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)) (Ioc (0:ℝ) 1) ∧
      |greenScalar ψ x y| ≤ 2*B/δ^2 := by
  have hz : ∀ t ∈ Ioc (0:ℝ) 1, t < δ → ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ) = 0 := by
    intro t ht hlt
    have : ψ (x+t⁻¹ • (y-x)) = 0 := by
      by_contra hn
      have hs := segment_support hψs hx ht.1 hn
      have := mul_lt_mul_of_pos_right hlt hM
      linarith
    rw [this,zero_mul]
  have hb : ∀ t ∈ Ioc (0:ℝ) 1,
      |ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)| ≤ B*t^(-3:ℝ) := by
    intro t ht
    rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    exact mul_le_mul_of_nonneg_right (hψB _) (Real.rpow_nonneg ht.1.le _)
  obtain ⟨hi,h⟩ := singular_integral_bound (segment_integrand_measurable hψm x y)
    (by norm_num : (-3:ℝ) < -1) hδ hB hz hb
  refine ⟨hi, h.trans_eq ?_⟩
  rw [show (-3:ℝ)+1 = -2 by norm_num, show (δ/2)^(-2:ℝ) = (δ/2)^(-2:ℤ) by norm_num [Real.rpow_intCast],zpow_neg,zpow_ofNat]
  norm_num
  field_simp

/-- A difference bound proves the needed cancellation estimate without hiding
any differentiation under the singular integral. -/
theorem green_difference_bound {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B L : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L)
    {x y z : ℂ} (hx : ‖x‖ ≤ X) (hzx : z ≠ x) (hyz : ‖y-z‖ ≤ ‖z-x‖/2) :
    ‖green ψ x y-green ψ x z‖ ≤
      (8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*‖y-z‖/‖z-x‖^2 := by
  let d := ‖z-x‖
  let a := ‖y-z‖
  let M := R+X
  let δ := d/(2*M)
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hzx)
  have ha : 0 ≤ a := norm_nonneg _
  have hδ : 0 < δ := div_pos hd (mul_pos (by norm_num) hM)
  have hnear : d/2 ≤ ‖y-x‖ := by
    have ht := norm_sub_le_norm_sub_add_norm_sub z y x
    rw [norm_sub_rev z y] at ht
    dsimp [d] at *
    linarith
  have hcut : δ*M = d/2 := by dsimp [δ]; field_simp [show M ≠ 0 from hM.ne']
  have hdy : δ*(R+X) ≤ ‖y-x‖ := by change δ*M ≤ _; rw [hcut]; exact hnear
  have hdz : δ*(R+X) ≤ ‖z-x‖ := by change δ*M ≤ d; rw [hcut]; linarith
  obtain ⟨hIy,hKy⟩ := scalar_data hψm hψs hψB hM hB hδ hx hdy
  obtain ⟨hIz,_⟩ := scalar_data hψm hψs hψB hM hB hδ hx hdz
  let F := fun t : ℝ => (ψ (x+t⁻¹ • (y-x))-ψ (x+t⁻¹ • (z-x)))*t^(-3:ℝ)
  have hFm : Measurable F := by
    change Measurable (fun t : ℝ => _)
    have hm (v : ℂ) : Measurable (fun t : ℝ => ψ (x+t⁻¹ • (v-x))) := by
      apply hψm.comp
      measurability
    exact ((hm y).sub (hm z)).mul (measurable_id.pow_const _)
  have hzero : ∀ t ∈ Ioc (0:ℝ) 1, t < δ → F t = 0 := by
    intro t ht htδ
    have h0 (v : ℂ) (hv : δ*M ≤ ‖v-x‖) : ψ (x+t⁻¹ • (v-x)) = 0 := by
      by_contra hn
      have hs := segment_support hψs hx ht.1 hn
      have := mul_lt_mul_of_pos_right htδ hM
      dsimp [M] at hv
      linarith
    change (ψ (x+t⁻¹ • (y-x))-ψ (x+t⁻¹ • (z-x)))*t^(-3:ℝ) = 0
    rw [h0 y hdy,h0 z hdz,sub_self,zero_mul]
  have hbound : ∀ t ∈ Ioc (0:ℝ) 1, |F t| ≤ (L*a)*t^(-4:ℝ) := by
    intro t ht
    have harg : (x+t⁻¹ • (y-x))-(x+t⁻¹ • (z-x)) = t⁻¹ • (y-z) := by module
    have hLip := hψL (x+t⁻¹ • (y-x)) (x+t⁻¹ • (z-x))
    rw [harg,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht.1)] at hLip
    calc
      |F t| = |ψ (x+t⁻¹ • (y-x))-ψ (x+t⁻¹ • (z-x))| *t^(-3:ℝ) := by
        change |(ψ (x+t⁻¹ • (y-x))-ψ (x+t⁻¹ • (z-x)))*t^(-3:ℝ)| = _
        rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
      _ ≤ (L*(t⁻¹*a))*t^(-3:ℝ) := mul_le_mul_of_nonneg_right hLip (Real.rpow_nonneg ht.1.le _)
      _ = (L*a)*t^(-4:ℝ) := by
        rw [← Real.rpow_neg_one t]
        calc
          _ = (L*a)*(t^(-1:ℝ)*t^(-3:ℝ)) := by ring
          _ = _ := by rw [← Real.rpow_add ht.1]; norm_num
  have hdiff := (singular_integral_bound hFm (by norm_num : (-4:ℝ) < -1)
    hδ (mul_nonneg hL ha) hzero hbound).2
  have hIF : (∫ t in Ioc (0:ℝ) 1, F t) = greenScalar ψ x y-greenScalar ψ x z := by
    simp only [F,sub_mul,greenScalar]
    exact integral_sub hIy hIz
  rw [hIF] at hdiff
  have hKd : |greenScalar ψ x y-greenScalar ψ x z| ≤ (64/3:ℝ)*L*a*M^3/d^3 := by
    refine hdiff.trans_eq ?_
    rw [show (-4:ℝ)+1 = -3 by norm_num, show (δ/2)^(-3:ℝ) = (δ/2)^(-3:ℤ) by norm_num [Real.rpow_intCast],zpow_neg,zpow_ofNat]
    dsimp [δ]
    field_simp
    ring
  have hKy' : |greenScalar ψ x y| ≤ 8*B*M^2/d^2 := by
    refine hKy.trans_eq ?_
    dsimp [δ]
    field_simp
    ring
  have heq : green ψ x y-green ψ x z =
      (-greenScalar ψ x y) • (y-z) - (greenScalar ψ x y-greenScalar ψ x z) • (z-x) := by
    unfold green
    module
  rw [heq]
  calc
    _ ≤ ‖(-greenScalar ψ x y) • (y-z)‖ +
        ‖(greenScalar ψ x y-greenScalar ψ x z) • (z-x)‖ := norm_sub_le _ _
    _ = |greenScalar ψ x y| *a + |greenScalar ψ x y-greenScalar ψ x z| *d := by
      simp only [norm_smul,Real.norm_eq_abs,abs_neg,a,d]
    _ ≤ (8*B*M^2/d^2)*a + ((64/3:ℝ)*L*a*M^3/d^3)*d :=
      add_le_add (mul_le_mul_of_nonneg_right hKy' ha) (mul_le_mul_of_nonneg_right hKd hd.le)
    _ = _ := by change _ = (8*B*M^2+(64/3:ℝ)*L*M^3)*a/d^2; field_simp

end PlanePotential

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.GreenBounds
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

noncomputable section

namespace PlanePotential

lemma integral_affine (F : ℂ → ℝ) (x : ℂ) (t : ℝ) :
    (∫ z : ℂ, F (x+t • (z-x))) = (t^2)⁻¹ * ∫ y : ℂ, F y := by
  calc
    _ = ∫ w : ℂ, F (x+t • w) := by
      simpa only [sub_eq_add_neg] using
        integral_add_right_eq_self (fun w : ℂ => F (x+t • w)) (-x)
    _ = |(t^2)⁻¹| * ∫ y, F (x+y) := by
      simpa only [Complex.finrank_real_complex,smul_eq_mul] using
        Measure.integral_comp_smul volume (fun y : ℂ => F (x+y)) t
    _ = _ := by rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t)),integral_add_left_eq_self]

lemma integrable_affine_iff (F : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : t ≠ 0) :
    Integrable (fun z : ℂ => F (x+t • (z-x))) ↔ Integrable F := by
  constructor
  · intro h
    have h1 : Integrable (fun z : ℂ => F (x+t • z)) := by
      simpa only [add_sub_cancel_right] using h.comp_add_right x
    have h2 := (integrable_comp_smul_iff volume (fun z : ℂ => F (x+z)) ht).mp h1
    simpa only [add_neg_cancel_left] using h2.comp_add_left (-x)
  · intro h
    simpa only [sub_eq_add_neg] using ((h.comp_add_left x).comp_smul ht).comp_add_right (-x)

lemma integral_affine_reverse (F : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : t ≠ 0) :
    (∫ y : ℂ, F y) = t^2 * ∫ z : ℂ, F (x+t • (z-x)) := by
  rw [integral_affine]
  field_simp

lemma segment_ftc {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x z : ℂ) :
    (∫ t in Ioc (0:ℝ) 1, fderiv ℝ g (x+t • (z-x)) (z-x)) = g z-g x := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => g (x+s • (z-x)))
      (fderiv ℝ g (x+t • (z-x)) (z-x)) t := by
    have hline : HasDerivAt (fun s : ℝ => x+s • (z-x)) (z-x) t := by
      simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const (z-x)).const_add x
    exact ((hg.differentiable (by norm_num) _).hasFDerivAt).comp_hasDerivAt t hline
  have hc : Continuous (fun t : ℝ => fderiv ℝ g (x+t • (z-x)) (z-x)) := by
    exact ((hg.continuous_fderiv (by norm_num)).comp (by fun_prop)).clm_apply continuous_const
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),one_smul,
    add_sub_cancel,zero_smul,add_zero] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hc.intervalIntegrable 0 1)

lemma pullback_identity (ψ g : ℂ → ℝ) (x z : ℂ) {t : ℝ} (ht : 0 < t) :
    pullbackForm ψ g x t (x+t • (z-x)) = (t^2)⁻¹*segmentForm ψ g x t z := by
  have ha : x+t⁻¹ • (x+t • (z-x)-x) = z := by simp [ht.ne']
  unfold pullbackForm segmentForm
  rw [ha,add_sub_cancel_left,map_smul,smul_eq_mul]
  have hp : t^(-3:ℝ) = (t^3)⁻¹ := by
    rw [show (-3:ℝ) = ((-3:ℤ):ℝ) by norm_num,Real.rpow_intCast,zpow_neg,zpow_ofNat]
  rw [hp]
  field_simp

lemma segmentForm_continuous {ψ g : ℂ → ℝ} (hψ : Continuous ψ) (hg : ContDiff ℝ 1 g) (x : ℂ) :
    Continuous (fun p : ℝ × ℂ => segmentForm ψ g x p.1 p.2) := by
  unfold segmentForm
  exact (hψ.comp continuous_snd).mul
    (((hg.continuous_fderiv (by norm_num)).comp (by fun_prop)).clm_apply (by fun_prop))

lemma segmentForm_integrable_column {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) (x : ℂ) (t : ℝ) :
    Integrable (segmentForm ψ g x t) := by
  apply ((segmentForm_continuous hψ hg x).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
  exact hψc.mul_right

lemma pullbackForm_measurable {ψ g : ℂ → ℝ} (hψ : Continuous ψ) (hg : ContDiff ℝ 1 g) (x : ℂ) :
    Measurable (fun p : ℝ × ℂ => pullbackForm ψ g x p.1 p.2) := by
  unfold pullbackForm
  have ha : Measurable (fun p : ℝ × ℂ => x+p.1⁻¹ • (p.2-x)) := by measurability
  exact ((hψ.measurable.comp ha).mul (measurable_fst.pow_const _)).mul
    ((((hg.continuous_fderiv (by norm_num)).comp continuous_snd).clm_apply (by fun_prop)).measurable)

lemma pullbackForm_integrable_column {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    Integrable (pullbackForm ψ g x t) := by
  apply (integrable_affine_iff _ x ht.ne').mp
  simpa only [pullback_identity ψ g x _ ht] using
    (segmentForm_integrable_column hψ hψc hg x t).const_mul ((t^2)⁻¹)

lemma pullback_column_integral (ψ g : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    (∫ y, pullbackForm ψ g x t y) = ∫ z, segmentForm ψ g x t z := by
  rw [integral_affine_reverse _ x ht.ne']
  simp_rw [pullback_identity ψ g x _ ht]
  rw [integral_const_mul]
  field_simp

lemma pullback_column_norm (ψ g : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    (∫ y, ‖pullbackForm ψ g x t y‖) = ∫ z, ‖segmentForm ψ g x t z‖ := by
  rw [integral_affine_reverse _ x ht.ne']
  simp_rw [pullback_identity ψ g x _ ht,norm_mul,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t))]
  rw [integral_const_mul]
  field_simp

lemma segmentForm_bound {ψ g : ℂ → ℝ} {D : ℝ} (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D)
    (x : ℂ) (t : ℝ) (z : ℂ) :
    ‖segmentForm ψ g x t z‖ ≤ |ψ z| *D*‖z-x‖ := by
  rw [segmentForm,norm_mul,Real.norm_eq_abs]
  calc
    _ ≤ |ψ z| *(‖fderiv ℝ g (x+t • (z-x))‖*‖z-x‖) :=
      mul_le_mul_of_nonneg_left ((fderiv ℝ g _).le_opNorm _) (abs_nonneg _)
    _ ≤ |ψ z| *(D*‖z-x‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _)) (abs_nonneg _)
    _ = _ := by ring

lemma segment_weight_integrable {ψ : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (x : ℂ) (D : ℝ) :
    Integrable (fun z : ℂ => |ψ z| *D*‖z-x‖) := by
  apply (show Continuous (fun z : ℂ => |ψ z| *D*‖z-x‖) by fun_prop).integrable_of_hasCompactSupport
  exact (hψc.norm.mul_right).mul_right

/-- Absolute integrability justifies the double integral even at t approaching zero. -/
theorem pullbackForm_integrable {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) :
    Integrable (fun p : ℝ × ℂ => pullbackForm ψ g x p.1 p.2)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod volume) := by
  have hm := (pullbackForm_measurable hψ hg x).stronglyMeasurable
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact pullbackForm_integrable_column hψ hψc hg x ht.1
  · have hweight := segment_weight_integrable hψ hψc x D
    let C := ∫ z : ℂ, |ψ z| *D*‖z-x‖
    apply (integrable_const C).mono' hm.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [pullback_column_norm ψ g x ht.1,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact integral_mono (segmentForm_integrable_column hψ hψc hg x t).norm hweight
      (segmentForm_bound hD x t)

lemma segmentForm_integrable {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) :
    Integrable (fun p : ℝ × ℂ => segmentForm ψ g x p.1 p.2)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod volume) := by
  have hm := (segmentForm_continuous hψ hg x).stronglyMeasurable
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  constructor
  · exact ae_of_all _ (fun t => segmentForm_integrable_column hψ hψc hg x t)
  · have hweight := segment_weight_integrable hψ hψc x D
    let C := ∫ z : ℂ, |ψ z| * D*‖z-x‖
    apply (integrable_const C).mono' hm.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards with t
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact integral_mono (segmentForm_integrable_column hψ hψc hg x t).norm hweight
      (segmentForm_bound hD x t)

lemma green_pullback (ψ g : ℂ → ℝ) (x y : ℂ) :
    fderiv ℝ g y (green ψ x y) = -∫ t in Ioc (0:ℝ) 1, pullbackForm ψ g x t y := by
  simp only [green,map_smul,smul_eq_mul,greenScalar,pullbackForm,integral_mul_const,neg_mul]

/-- The true segment-kernel representation, with Fubini justified absolutely. -/
theorem green_representation {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (hψ1 : ∫ z, ψ z = 1) (x : ℂ) :
    (∫ y, fderiv ℝ g y (green ψ x y)) = g x-∫ z, ψ z*g z := by
  have hseg := segmentForm_integrable hψ hψc hg hD x
  have hpull := pullbackForm_integrable hψ hψc hg hD x
  have hψi : Integrable ψ := hψ.integrable_of_hasCompactSupport hψc
  have hψgi : Integrable (fun z => ψ z*g z) :=
    (hψ.mul hg.continuous).integrable_of_hasCompactSupport hψc.mul_right
  calc
    _ = -(∫ y, ∫ t in Ioc (0:ℝ) 1, pullbackForm ψ g x t y) := by
      simp_rw [green_pullback]; rw [integral_neg]
    _ = -(∫ t in Ioc (0:ℝ) 1, ∫ y, pullbackForm ψ g x t y) := by
      rw [← integral_integral_swap hpull]
    _ = -(∫ t in Ioc (0:ℝ) 1, ∫ z, segmentForm ψ g x t z) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact pullback_column_integral ψ g x ht.1
    _ = -(∫ z, ∫ t in Ioc (0:ℝ) 1, segmentForm ψ g x t z) := by
      rw [integral_integral_swap hseg]
    _ = -(∫ z, ψ z*(g z-g x)) := by
      simp_rw [segmentForm,integral_const_mul,segment_ftc hg]
    _ = _ := by
      simp_rw [mul_sub]
      rw [integral_sub hψgi (hψi.mul_const _),integral_mul_const,hψ1]
      ring

end PlanePotential

open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace PlanePotential
lemma lintegral_norm_rpow_near {a r : ℝ} (ha : -2 < a) (hr : 0 < r) :
    (∫⁻ x in ball (0:ℂ) r, ENNReal.ofReal (‖x‖^a)) =
      ENNReal.ofReal (2*Real.pi*(r^(a+2)/(a+2))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_norm_rpow_near ha hr)
    (ae_of_all _ (fun x => Real.rpow_nonneg (norm_nonneg x) a)),integral_norm_rpow_near ha hr]

lemma lintegral_norm_rpow_far {a r : ℝ} (ha : a < -2) (hr : 0 < r) :
    (∫⁻ x : ℂ in {x | r < ‖x‖}, ENNReal.ofReal (‖x‖^a)) =
      ENNReal.ofReal (2*Real.pi*(-r^(a+2)/(a+2))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_norm_rpow_far ha hr)
    (ae_of_all _ (fun x => Real.rpow_nonneg (norm_nonneg x) a)),integral_norm_rpow_far ha hr]

lemma lintegral_translated_near {a r : ℝ} (ha : -2 < a) (hr : 0 < r) (y : ℂ) :
    (∫⁻ x in ball y r, ENNReal.ofReal (‖x-y‖^a)) =
      ENNReal.ofReal (2*Real.pi*(r^(a+2)/(a+2))) := by
  rw [← lintegral_norm_rpow_near ha hr,← lintegral_indicator measurableSet_ball,
    ← lintegral_indicator measurableSet_ball]
  have heq : (ball y r).indicator (fun x => ENNReal.ofReal (‖x-y‖^a)) =
      fun x => (ball (0:ℂ) r).indicator (fun w => ENNReal.ofReal (‖w‖^a)) (x-y) := by
    funext x
    simp only [indicator,mem_ball,dist_eq_norm,sub_zero]
  rw [heq]
  exact lintegral_add_right_eq_self (fun x : ℂ => (ball 0 r).indicator
    (fun w => ENNReal.ofReal (‖w‖^a)) x) (-y)

lemma lintegral_translated_far {a r : ℝ} (ha : a < -2) (hr : 0 < r) (y : ℂ) :
    (∫⁻ x : ℂ in {x | r < ‖x-y‖}, ENNReal.ofReal (‖x-y‖^a)) =
      ENNReal.ofReal (2*Real.pi*(-r^(a+2)/(a+2))) := by
  rw [← lintegral_norm_rpow_far ha hr,
    ← lintegral_indicator (show MeasurableSet {x : ℂ | r < ‖x-y‖} from measurableSet_lt measurable_const (by fun_prop)),
    ← lintegral_indicator (measurableSet_lt measurable_const measurable_norm)]
  exact lintegral_add_right_eq_self (fun x : ℂ => ({x | r < ‖x‖}).indicator
    (fun w => ENNReal.ofReal (‖w‖^a)) x) (-y)

lemma norm_power_bound {F : ℂ → ℂ} {C q : ℝ} (hC : 0 ≤ C) (x y : ℂ)
    (hF : ‖F x‖ ≤ C*‖x-y‖^q) :
    (ENNReal.ofReal ‖F x‖)^(3/2:ℝ) ≤
      ENNReal.ofReal (C^(3/2:ℝ))*ENNReal.ofReal (‖x-y‖^(q*(3/2:ℝ))) := by
  calc
    _ = ENNReal.ofReal (‖F x‖^(3/2:ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)
    _ ≤ ENNReal.ofReal ((C*‖x-y‖^q)^(3/2:ℝ)) :=
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) hF (by norm_num))
    _ = _ := by
      rw [Real.mul_rpow hC (Real.rpow_nonneg (norm_nonneg _) _),← Real.rpow_mul (norm_nonneg _),
        ENNReal.ofReal_mul (Real.rpow_nonneg hC _)]

lemma kernel_near_three_halves {F : ℂ → ℂ} {E : Set ℂ} {C r : ℝ} (hC : 0 ≤ C)
    (hr : 0 < r) (y : ℂ) (hE : E ⊆ ball y r)
    (hF : ∀ x ∈ E, ‖F x‖ ≤ C*‖x-y‖^(-1:ℝ)) :
    (∫⁻ x in E, (ENNReal.ofReal ‖F x‖)^(3/2:ℝ)) ≤
      ENNReal.ofReal (C^(3/2:ℝ)*(4*Real.pi*r^(1/2:ℝ))) := by
  calc
    _ ≤ ∫⁻ x in E, ENNReal.ofReal (C^(3/2:ℝ))*ENNReal.ofReal (‖x-y‖^(-3/2:ℝ)) := by
      apply setLIntegral_mono (by fun_prop)
      intro x hx
      convert norm_power_bound hC x y (hF x hx) using 1
      norm_num
    _ ≤ ∫⁻ x in ball y r, ENNReal.ofReal (C^(3/2:ℝ))*ENNReal.ofReal (‖x-y‖^(-3/2:ℝ)) :=
      lintegral_mono_set hE
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop),lintegral_translated_near (by norm_num : (-2:ℝ) < -3/2) hr y,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hC _)]
      congr 1
      norm_num
      exact Or.inl (by ring)

lemma kernel_far_three_halves {F : ℂ → ℂ} {E : Set ℂ} {C r : ℝ} (hC : 0 ≤ C)
    (hr : 0 < r) (y : ℂ) (hE : E ⊆ {x | r < ‖x-y‖})
    (hF : ∀ x ∈ E, ‖F x‖ ≤ C*‖x-y‖^(-2:ℝ)) :
    (∫⁻ x in E, (ENNReal.ofReal ‖F x‖)^(3/2:ℝ)) ≤
      ENNReal.ofReal (C^(3/2:ℝ)*(2*Real.pi/r)) := by
  calc
    _ ≤ ∫⁻ x in E, ENNReal.ofReal (C^(3/2:ℝ))*ENNReal.ofReal (‖x-y‖^(-3:ℝ)) := by
      apply setLIntegral_mono (by fun_prop)
      intro x hx
      convert norm_power_bound hC x y (hF x hx) using 1
      norm_num
    _ ≤ ∫⁻ x : ℂ in {x | r < ‖x-y‖}, ENNReal.ofReal (C^(3/2:ℝ))*ENNReal.ofReal (‖x-y‖^(-3:ℝ)) :=
      lintegral_mono_set hE
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop),lintegral_translated_far (by norm_num : (-3:ℝ) < -2) hr y,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hC _)]
      congr 1
      norm_num [Real.rpow_neg_one]
      exact Or.inl (by ring)

end PlanePotential

open scoped RealInnerProductSpace
namespace PlanePotential

lemma green_diagonal (ψ : ℂ → ℝ) (x : ℂ) : green ψ x x = 0 := by
  simp [green]

lemma green_size_all {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) {x y : ℂ} (hx : ‖x‖ ≤ X) :
    ‖green ψ x y‖ ≤ (2*B*(R+X)^2)*‖x-y‖^(-1:ℝ) := by
  by_cases hxy : y = x
  · subst y
    simp [green_diagonal]
  · simpa only [Real.rpow_neg_one,div_eq_mul_inv,norm_sub_rev] using
      green_norm_bound hψm hψs hψB hM hB hx hxy

lemma green_near_column {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (ha : 0 < a) (z y : ℂ) (hy : ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X ∧ ‖x-z‖ ≤ 2*a},
      (ENNReal.ofReal ‖green ψ x y‖)^(3/2:ℝ)) ≤
      ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(4*a)^(1/2:ℝ))) := by
  apply kernel_near_three_halves (by positivity) (by positivity : 0 < 4*a) y
  · intro x hx
    rw [mem_ball,dist_eq_norm]
    have ht := norm_sub_le (x-z) (y-z)
    rw [sub_sub_sub_cancel_right] at ht
    linarith [hx.2]
  · intro x hx
    exact green_size_all hψm hψs hψB hM hB hx.1

lemma green_far_column {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B L a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L) (ha : 0 < a)
    (z y : ℂ) (hy : ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X ∧ 2*a < ‖x-z‖},
      (ENNReal.ofReal ‖green ψ x y-green ψ x z‖)^(3/2:ℝ)) ≤
      ENNReal.ofReal (((8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*a)^(3/2:ℝ) *
        (2*Real.pi/(2*a))) := by
  apply kernel_far_three_halves (by positivity) (by positivity : 0 < 2*a) z
  · exact fun _ hx => hx.2
  · intro x hx
    have hzx : z ≠ x := by
      intro h
      have hh := hx.2
      rw [← h,sub_self,norm_zero] at hh
      linarith
    have hn : ‖z-x‖ = ‖x-z‖ := norm_sub_rev z x
    have h := green_difference_bound (x := x) (y := y) (z := z) hψm hψs hψB hψL hM hB hL hx.1 hzx (by
      rw [hn]
      linarith [hx.2])
    rw [hn] at h
    calc
      _ ≤ (8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*a/‖x-z‖^2 :=
        h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hy (by positivity)) (sq_nonneg _))
      _ = _ := by
        rw [show ‖x-z‖^(-2:ℝ) = ‖x-z‖^(-2:ℤ) by norm_num [Real.rpow_intCast],zpow_neg,zpow_ofNat]
        rfl

lemma cancelledGreen_measurable {ψ : ℂ → ℝ} (hψ : Measurable ψ) (z : ℂ) (a : ℝ) :
    Measurable (fun p : ℂ × ℂ => cancelledGreen ψ z a p.1 p.2) := by
  apply Measurable.ite
  · exact measurableSet_le (by fun_prop) measurable_const
  · exact green_measurable ψ hψ
  · exact (green_measurable ψ hψ).sub
      ((green_measurable ψ hψ).comp (measurable_fst.prodMk measurable_const))

lemma green_piece_column {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B L a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L) (ha : 0 < a)
    (z y : ℂ) (hy : ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X},
      (ENNReal.ofReal ‖cancelledGreen ψ z a x y‖)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(4*a)^(1/2:ℝ))) +
    ENNReal.ofReal (((8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*a)^(3/2:ℝ) *
        (2*Real.pi/(2*a))) := by
  let E := {x : ℂ | ‖x‖ ≤ X}
  let N := {x : ℂ | ‖x-z‖ ≤ 2*a}
  have hN : MeasurableSet N := measurableSet_le (by fun_prop) measurable_const
  have hE : MeasurableSet E := measurableSet_le measurable_norm measurable_const
  have hsplit := lintegral_add_compl (μ := volume.restrict E)
    (fun x => (ENNReal.ofReal ‖cancelledGreen ψ z a x y‖)^(3/2:ℝ)) hN
  rw [← hsplit]
  have hn : (∫⁻ x in N, (ENNReal.ofReal ‖cancelledGreen ψ z a x y‖)^(3/2:ℝ) ∂volume.restrict E) =
      ∫⁻ x in {x : ℂ | ‖x‖ ≤ X ∧ ‖x-z‖ ≤ 2*a}, (ENNReal.ofReal ‖green ψ x y‖)^(3/2:ℝ) := by
    rw [Measure.restrict_restrict hN,inter_comm]
    apply setLIntegral_congr_fun (hE.inter hN)
    intro x hx
    have hxN : ‖x-z‖ ≤ 2*a := hx.2
    simp only [cancelledGreen,ite_eq_left hxN]
  have hf : (∫⁻ x in Nᶜ, (ENNReal.ofReal ‖cancelledGreen ψ z a x y‖)^(3/2:ℝ) ∂volume.restrict E) =
      ∫⁻ x in {x : ℂ | ‖x‖ ≤ X ∧ 2*a < ‖x-z‖}, (ENNReal.ofReal ‖green ψ x y-green ψ x z‖)^(3/2:ℝ) := by
    rw [Measure.restrict_restrict hN.compl,inter_comm]
    have he : E ∩ Nᶜ = {x : ℂ | ‖x‖ ≤ X ∧ 2*a < ‖x-z‖} := by ext x; simp [E,N]
    rw [he]
    apply setLIntegral_congr_fun ((measurableSet_le measurable_norm measurable_const).inter
      (measurableSet_lt measurable_const ((measurable_id.sub_const z).norm)))
    intro x hx
    have hxF : 2*a < ‖x-z‖ := hx.2
    simp only [cancelledGreen,ite_eq_right (not_le.mpr hxF)]
  rw [hn,hf]
  exact add_le_add (green_near_column hψm hψs hψB hM hB ha z y hy)
    (green_far_column hψm hψs hψB hψL hM hB hL ha z y hy)

end PlanePotential

namespace PlanePotential

theorem kernel_column_lp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {K : α × β → ℝ≥0∞} (hK : Measurable K) {C : ℝ≥0∞}
    (hC : ∀ᵐ y ∂ν, (∫⁻ x, (K (x,y))^(3/2:ℝ) ∂μ) ≤ C) :
    (∫⁻ x, (∫⁻ y, K (x,y) ∂ν)^(3/2:ℝ) ∂μ) ≤ C*(ν univ)^(3/2:ℝ) := by
  have hpq : Real.HolderConjugate (3/2) 3 := by rw [Real.holderConjugate_iff]; norm_num
  have hpoint (x : α) : (∫⁻ y, K (x,y) ∂ν)^(3/2:ℝ) ≤
      (∫⁻ y, K (x,y)^(3/2:ℝ) ∂ν)*(ν univ)^(1/2:ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq (f := fun y => K (x,y)) (g := fun _ => 1)
      ((hK.comp (measurable_const.prodMk measurable_id)).aemeasurable)
      (aemeasurable_const (b := (1:ℝ≥0∞)))
    simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_const,one_mul] at h
    have h' := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 3/2)
    simpa only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 3/2),← ENNReal.rpow_mul,
      show (1/(3/2:ℝ))*(3/2)=1 by norm_num,
      show (1/(3:ℝ))*(3/2)=1/2 by norm_num,ENNReal.rpow_one,one_mul] using h'
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, K (x,y)^(3/2:ℝ) ∂ν)*(ν univ)^(1/2:ℝ) ∂μ :=
      lintegral_mono hpoint
    _ = (∫⁻ y, ∫⁻ x, K (x,y)^(3/2:ℝ) ∂μ ∂ν)*(ν univ)^(1/2:ℝ) := by
      rw [lintegral_mul_const _ (hK.pow_const _).lintegral_prod_right,
        lintegral_lintegral_swap (hK.pow_const _).aemeasurable]
    _ ≤ (C*ν univ)*(ν univ)^(1/2:ℝ) :=
      mul_le_mul_left ((lintegral_mono_ae hC).trans_eq (lintegral_const _)) _
    _ = _ := by
      rw [mul_assoc]
      congr 1
      calc
        _ = (ν univ)^(1:ℝ)*(ν univ)^(1/2:ℝ) := by rw [ENNReal.rpow_one]
        _ = (ν univ)^((1:ℝ)+1/2) :=
          (ENNReal.rpow_add_of_nonneg 1 (1/2) (by norm_num) (by norm_num)).symm
        _ = _ := by norm_num

/-- No pointwise integrability assertion for the singular kernel is needed
in this domination: the Bochner integral is bounded by the nonnegative integral. -/
lemma potential_domination {L : ℂ → ℂ} (hL : Measurable L) {b : ℂ → ℂ}
    (hb : Integrable b) :
    ENNReal.ofReal |∫ y, ⟪L y,b y⟫| ≤
      ∫⁻ y, ENNReal.ofReal ‖L y‖ ∂volume.withDensity (fun y => ENNReal.ofReal ‖b y‖) := by
  rw [lintegral_withDensity_eq_lintegral_mul₀' hb.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
    hL.norm.ennreal_ofReal.aemeasurable]
  calc
    _ = ‖∫ y, ⟪L y,b y⟫‖ₑ := by rw [← ofReal_norm,Real.norm_eq_abs]
    _ ≤ ∫⁻ y, ‖⟪L y,b y⟫‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ _ := by
      apply lintegral_mono
      intro y
      dsimp only [Pi.mul_apply]
      rw [← ofReal_norm]
      change ENNReal.ofReal ‖⟪L y,b y⟫‖ ≤ ENNReal.ofReal ‖b y‖ * ENNReal.ofReal ‖L y‖
      rw [← ENNReal.ofReal_mul (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans_eq (mul_comm _ _))

theorem cancelled_potential_lp {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X B L a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L) (ha : 0 < a)
    (z : ℂ) (hβ : Integrable β) (hβs : ∀ y, β y ≠ 0 → ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X},
      (ENNReal.ofReal |∫ y, ⟪cancelledGreen ψ z a x y,β y⟫|)^(3/2:ℝ)) ≤
    (ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(4*a)^(1/2:ℝ))) +
    ENNReal.ofReal (((8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*a)^(3/2:ℝ) *
        (2*Real.pi/(2*a)))) * (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  let ν := volume.withDensity (fun y => ENNReal.ofReal ‖β y‖)
  have hν : ν univ = ENNReal.ofReal (∫ y, ‖β y‖) := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hβ.norm
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))).symm
  have : IsFiniteMeasure ν := ⟨by rw [hν]; exact ENNReal.ofReal_lt_top⟩
  have hm := cancelledGreen_measurable hψm z a
  have hcol := kernel_column_lp (volume.restrict {x : ℂ | ‖x‖ ≤ X}) ν hm.norm.ennreal_ofReal
    (C := ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(4*a)^(1/2:ℝ))) +
      ENNReal.ofReal (((8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*a)^(3/2:ℝ)*(2*Real.pi/(2*a))))
    (by
      rw [ae_withDensity_iff' hβ.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal]
      filter_upwards with y hy
      apply green_piece_column hψm hψs hψB hψL hM hB hL ha z y
      apply hβs y
      intro hy0
      simp [hy0] at hy)
  rw [hν] at hcol
  apply le_trans _ hcol
  apply lintegral_mono
  intro x
  exact ENNReal.rpow_le_rpow (potential_domination
    (hm.comp (measurable_const.prodMk measurable_id)) hβ) (by norm_num)

lemma zero_mass_kernel_shift {L : ℂ → ℂ} {β : ℂ → ℂ} (hβ : Integrable β)
    (hzero : ∫ y, β y = 0) (c : ℂ) :
    (∫ y, ⟪L y,β y⟫) = ∫ y, ⟪L y-c,β y⟫ := by
  have hc : Integrable (fun y => ⟪c,β y⟫) := hβ.const_inner c
  have hci : (∫ y, ⟪c,β y⟫) = 0 := by rw [integral_inner hβ,hzero,inner_zero_right]
  simp only [inner_sub_left]
  by_cases hi : Integrable (fun y => ⟪L y,β y⟫)
  · rw [integral_sub hi hc,hci,sub_zero]
  · rw [integral_undef hi,integral_undef]
    intro hs
    have hh := hs.add hc
    change Integrable (fun y => (⟪L y,β y⟫-⟪c,β y⟫)+⟪c,β y⟫) at hh
    simp only [sub_add_cancel] at hh
    exact hi hh

lemma cancelled_potential_eq {ψ : ℂ → ℝ} {β : ℂ → ℂ} (hβ : Integrable β)
    (hzero : ∫ y, β y = 0) (z : ℂ) (a : ℝ) (x : ℂ) :
    (∫ y, ⟪green ψ x y,β y⟫) = ∫ y, ⟪cancelledGreen ψ z a x y,β y⟫ := by
  by_cases hx : ‖x-z‖ ≤ 2*a
  · simp only [cancelledGreen,ite_eq_left hx]
  · simp only [cancelledGreen,ite_eq_right hx]
    exact zero_mass_kernel_shift hβ hzero _

/-- Uniform scaling of the exact p-th power column constant: in dimension two
and at p=3/2 its radius dependence is precisely a^(1/2). -/
lemma column_scaling {K D a : ℝ} (hD : 0 ≤ D) (ha : 0 < a) :
    K^(3/2:ℝ)*(4*Real.pi*(4*a)^(1/2:ℝ)) +
      (D*a)^(3/2:ℝ)*(2*Real.pi/(2*a)) =
      (8*Real.pi*K^(3/2:ℝ)+Real.pi*D^(3/2:ℝ))*a^(1/2:ℝ) := by
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) ha.le,Real.mul_rpow hD ha.le]
  have hfour : (4:ℝ)^(1/2:ℝ) = 2 := by norm_num [← Real.sqrt_eq_rpow]
  have hpow : a^(3/2:ℝ)/a = a^(1/2:ℝ) := by
    rw [← Real.rpow_sub_one ha.ne']
    norm_num
  rw [hfour]
  calc
    _ = 8*Real.pi*K^(3/2:ℝ)*a^(1/2:ℝ)+Real.pi*D^(3/2:ℝ)*(a^(3/2:ℝ)/a) := by ring
    _ = _ := by rw [hpow]; ring

theorem green_zero_piece_lp {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X B L a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L) (ha : 0 < a)
    (z : ℂ) (hβ : Integrable β) (hzero : ∫ y, β y = 0)
    (hβs : ∀ y, β y ≠ 0 → ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X},
      (ENNReal.ofReal |∫ y, ⟪green ψ x y,β y⟫|)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((8*Real.pi*(2*B*(R+X)^2)^(3/2:ℝ)+
      Real.pi*(8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)^(3/2:ℝ))*a^(1/2:ℝ)) *
      (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  simp_rw [cancelled_potential_eq hβ hzero z a]
  have h := cancelled_potential_lp hψm hψs hψB hψL hM hB hL ha z hβ hβs
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    column_scaling (by positivity) ha] at h
  exact h

end PlanePotential

open scoped RealInnerProductSpace
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Marks
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

noncomputable section

open scoped ContDiff
namespace PlanePotential
lemma potential_norm_lintegral {L : ℂ → ℂ} (hL : Measurable L) {b : ℂ → ℂ}
    (hb : Integrable b) :
    (∫⁻ y, ‖⟪L y,b y⟫‖ₑ) ≤
      ∫⁻ y, ENNReal.ofReal ‖L y‖ ∂volume.withDensity (fun y => ENNReal.ofReal ‖b y‖) := by
  rw [lintegral_withDensity_eq_lintegral_mul₀' hb.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
    hL.norm.ennreal_ofReal.aemeasurable]
  apply lintegral_mono
  intro y
  dsimp only [Pi.mul_apply]
  rw [← ofReal_norm]
  change ENNReal.ofReal ‖⟪L y,b y⟫‖ ≤ ENNReal.ofReal ‖b y‖ * ENNReal.ofReal ‖L y‖
  rw [← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans_eq (mul_comm _ _))

lemma potential_integrable_of_density {L : ℂ → ℂ} (hL : Measurable L) {b : ℂ → ℂ}
    (hb : Integrable b)
    (hfinite : (∫⁻ y, ENNReal.ofReal ‖L y‖ ∂volume.withDensity (fun y => ENNReal.ofReal ‖b y‖)) < ⊤) :
    Integrable (fun y => ⟪L y,b y⟫) := by
  refine ⟨hL.aestronglyMeasurable.inner hb.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact (potential_norm_lintegral hL hb).trans_lt hfinite

/-- Finiteness of the genuine singular integrals, obtained from the column
estimate itself. This justifies insertion of the finite vector decomposition. -/
theorem kernel_potential_ae_integrable (μ : Measure ℂ) [SFinite μ]
    {K : ℂ × ℂ → ℂ} (hK : Measurable K) {b : ℂ → ℂ} (hb : Integrable b)
    {C : ℝ≥0∞} (hC : C < ⊤)
    (hcol : ∀ᵐ y ∂volume.withDensity (fun y => ENNReal.ofReal ‖b y‖),
      (∫⁻ x, (ENNReal.ofReal ‖K (x,y)‖)^(3/2:ℝ) ∂μ) ≤ C) :
    ∀ᵐ x ∂μ, Integrable (fun y => ⟪K (x,y),b y⟫) := by
  let ν := volume.withDensity (fun y => ENNReal.ofReal ‖b y‖)
  have hm : ν univ = ENNReal.ofReal (∫ y, ‖b y‖) := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hb.norm
      (ae_of_all _ (fun _ => norm_nonneg _))).symm
  have hν : ν univ < ⊤ := by rw [hm]; exact ENNReal.ofReal_lt_top
  have : IsFiniteMeasure ν := ⟨hν⟩
  have hlp := kernel_column_lp μ ν hK.norm.ennreal_ofReal hcol
  have hfinite : (∫⁻ x, (∫⁻ y, ENNReal.ofReal ‖K (x,y)‖ ∂ν)^(3/2:ℝ) ∂μ) ≠ ⊤ :=
    ne_of_lt (hlp.trans_lt (ENNReal.mul_lt_top hC (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hν.ne)))
  have hae := ae_lt_top (hK.norm.ennreal_ofReal.lintegral_prod_right.pow_const _) hfinite
  filter_upwards [hae] with x hx
  apply potential_integrable_of_density (hK.comp (measurable_const.prodMk measurable_id)) hb
  apply lt_top_iff_ne_top.mpr
  intro htop
  change (∫⁻ y, ENNReal.ofReal ‖K (x,y)‖ ∂ν) = ⊤ at htop
  rw [htop,ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 3/2)] at hx
  exact (lt_irrefl _ hx)

lemma green_root_column {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X Y B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y) {y : ℂ} (hy : ‖y‖ ≤ Y) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X}, (ENNReal.ofReal ‖green ψ x y‖)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(2*(X+Y))^(1/2:ℝ))) := by
  apply kernel_near_three_halves (by positivity) (by positivity : 0 < 2*(X+Y)) y
  · intro x hx
    rw [mem_ball,dist_eq_norm]
    have hn := norm_sub_le x y
    change ‖x‖ ≤ X at hx
    linarith
  · intro x hx
    exact green_size_all hψm hψs hψB hM hB hx

lemma green_ae_integrable {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X Y B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y)
    (hβ : Integrable β) (hβs : ∀ y, β y ≠ 0 → ‖y‖ ≤ Y) :
    ∀ᵐ x ∂volume.restrict {x : ℂ | ‖x‖ ≤ X}, Integrable (fun y => ⟪green ψ x y,β y⟫) := by
  apply kernel_potential_ae_integrable _ (green_measurable ψ hψm) hβ ENNReal.ofReal_lt_top
  rw [ae_withDensity_iff' hβ.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal]
  filter_upwards with y hy
  apply green_root_column hψm hψs hψB hM hB hXY
  apply hβs y
  intro hy0
  simp [hy0] at hy

lemma green_root_lp {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X Y B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y)
    (hβ : Integrable β) (hβs : ∀ y, β y ≠ 0 → ‖y‖ ≤ Y) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X}, (ENNReal.ofReal |∫ y, ⟪green ψ x y,β y⟫|)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(2*(X+Y))^(1/2:ℝ))) *
      (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  let ν := volume.withDensity (fun y => ENNReal.ofReal ‖β y‖)
  have hν : ν univ = ENNReal.ofReal (∫ y, ‖β y‖) := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hβ.norm
      (ae_of_all _ (fun _ => norm_nonneg _))).symm
  have : IsFiniteMeasure ν := ⟨by rw [hν]; exact ENNReal.ofReal_lt_top⟩
  have hm := green_measurable ψ hψm
  have hcol := kernel_column_lp (volume.restrict {x : ℂ | ‖x‖ ≤ X}) ν hm.norm.ennreal_ofReal
    (C := ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(2*(X+Y))^(1/2:ℝ)))) (by
      rw [ae_withDensity_iff' hβ.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal]
      filter_upwards with y hy
      apply green_root_column hψm hψs hψB hM hB hXY
      apply hβs y
      intro hy0
      simp [hy0] at hy)
  rw [hν] at hcol
  apply le_trans _ hcol
  apply lintegral_mono
  intro x
  exact ENNReal.rpow_le_rpow (potential_domination
    (hm.comp (measurable_const.prodMk measurable_id)) hβ) (by norm_num)

end PlanePotential

namespace PlanePotential
lemma eLpNorm_three_halves_bound (μ : Measure ℂ) {F : ℂ → ℝ} {K m : ℝ≥0∞}
    (h : (∫⁻ x, (ENNReal.ofReal |F x|)^(3/2:ℝ) ∂μ) ≤ K*m^(3/2:ℝ)) :
    eLpNorm' F (3/2) μ ≤ K^(2/3:ℝ)*m := by
  rw [eLpNorm'_eq_lintegral_enorm]
  norm_num only [one_div_div]
  have hpow := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 2/3)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2/3),← ENNReal.rpow_mul] at hpow
  norm_num only [show (3/2:ℝ)*(2/3)=1 by norm_num,ENNReal.rpow_one] at hpow
  simpa only [← ofReal_norm,Real.norm_eq_abs] using hpow

lemma potential_aestronglyMeasurable (μ : Measure ℂ) {K : ℂ × ℂ → ℂ}
    (hK : Measurable K) {β : ℂ → ℂ} (hβ : Integrable β) :
    AEStronglyMeasurable (fun x => ∫ y, ⟪K (x,y),β y⟫) μ := by
  have h : AEStronglyMeasurable (fun z : ℂ × ℂ => @inner ℝ ℂ _ (K z) (β z.2)) (μ.prod volume) :=
    hK.aestronglyMeasurable.inner hβ.aestronglyMeasurable.comp_snd
  exact h.integral_prod_right'

/-- A genuine fixed smooth probability cutoff. Its finite size and Lipschitz
constants depend on no input, no dyadic level and no number of scales. -/
theorem exists_kernel_cutoff : ∃ (ψ : ℂ → ℝ) (B L : ℝ),
    0 ≤ B ∧ 0 ≤ L ∧ ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
    (∫ x, ψ x) = 1 ∧ (∀ x, ψ x ≠ 0 → ‖x‖ ≤ 1) ∧
    (∀ x, |ψ x| ≤ B) ∧ (∀ x y, |ψ x-ψ y| ≤ L*‖x-y‖) := by
  let φ : ContDiffBump (0:ℂ) := ⟨1/2,1,by norm_num,by norm_num⟩
  let ψ := φ.normed volume
  have hc : HasCompactSupport ψ := φ.hasCompactSupport_normed
  have hd : ContDiff ℝ ∞ ψ := φ.contDiff_normed
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hd.continuous
  obtain ⟨L,hL⟩ := hd.lipschitzWith_of_hasCompactSupport hc (by simp)
  refine ⟨ψ,B,L,le_trans (norm_nonneg (ψ 0)) (hB 0),L.coe_nonneg,hd,hc,
    φ.integral_normed,?_,?_,?_⟩
  · intro x hx
    have hs : x ∈ Function.support ψ := hx
    rw [φ.support_normed_eq] at hs
    exact (show ‖x‖ < 1 by simpa only [mem_ball,dist_zero_right] using hs).le
  · intro x
    simpa only [Real.norm_eq_abs] using hB x
  · intro x y
    simpa only [Real.norm_eq_abs] using hL.norm_sub_le x y

end PlanePotential

open Finset
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

namespace PlanePotential

/-- The global segment kernel vanishes off the region on which the actual
finite density decomposition is valid. -/
lemma green_eq_zero_of_outside {ψ : ℂ → ℝ} {R X : ℝ}
    (hs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hRX : R ≤ X) {x y : ℂ}
    (hx : ‖x‖ ≤ X) (hy : X < ‖y‖) : green ψ x y = 0 := by
  have hz (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) : ψ (x+t⁻¹ • (y-x)) = 0 := by
    by_contra hh
    have hw := hs _ hh
    have heq : y = (1-t) • x+t • (x+t⁻¹ • (y-x)) := by
      rw [smul_add,smul_smul,mul_inv_cancel₀ ht.1.ne',one_smul]
      module
    have hn := norm_add_le ((1-t) • x) (t • (x+t⁻¹ • (y-x)))
    rw [← heq,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht.2),abs_of_pos ht.1] at hn
    have hle := add_le_add (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left (hw.trans hRX) ht.1.le)
    nlinarith
  have hi : greenScalar ψ x y = 0 := by
    unfold greenScalar
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    simp only [hz t ht,zero_mul]
  simp only [green,hi,neg_zero,zero_smul]

lemma green_gradient_representation {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (hψ1 : ∫ z, ψ z = 1) (x : ℂ) :
    (∫ y, ⟪green ψ x y,gradient g y⟫) = g x-∫ z, ψ z*g z := by
  simpa only [inner_gradient_right,RCLike.conj_to_real] using
    green_representation hψ hψc hg hD hψ1 x

theorem green_finite_decomposition {ι : Type*} [Fintype ι]
    {ψ g : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hg : ContDiff ℝ 1 g) {D R X Y B : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (hψ1 : ∫ z, ψ z = 1)
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hRX : R ≤ X) (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y)
    (β : ι → ℂ → ℂ) (hβ : ∀ i, Integrable (β i))
    (hβs : ∀ i y, β i y ≠ 0 → ‖y‖ ≤ Y)
    (hdecomp : ∀ᵐ y, ‖y‖ ≤ X → gradient g y = ∑ i, β i y) :
    ∀ᵐ x ∂volume.restrict {x : ℂ | ‖x‖ ≤ X},
      g x-∫ z, ψ z*g z = ∑ i, ∫ y, ⟪green ψ x y,β i y⟫ := by
  have hall := ae_all_iff.mpr (fun i => green_ae_integrable hψ.measurable hψs hψB hM hB hXY
    (hβ i) (hβs i))
  filter_upwards [hall,ae_restrict_mem (measurableSet_le measurable_norm measurable_const)] with x hi hx
  rw [← green_gradient_representation hψ hψc hg hD hψ1 x,← integral_finsetSum _ (fun i _ => hi i)]
  apply integral_congr_ae
  filter_upwards [hdecomp] with y hy
  by_cases hyX : ‖y‖ ≤ X
  · rw [hy hyX,inner_sum]
  · rw [green_eq_zero_of_outside hψs hRX hx (lt_of_not_ge hyX)]
    simp

/-- The complete finite Minkowski step, after genuine kernel insertion. -/
theorem green_decomposition_norm {ι : Type*} [Fintype ι]
    {ψ g : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hg : ContDiff ℝ 1 g) {D R X Y B : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (hψ1 : ∫ z, ψ z = 1)
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hRX : R ≤ X) (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y)
    (β : ι → ℂ → ℂ) (hβ : ∀ i, Integrable (β i))
    (hβs : ∀ i y, β i y ≠ 0 → ‖y‖ ≤ Y)
    (hdecomp : ∀ᵐ y, ‖y‖ ≤ X → gradient g y = ∑ i, β i y) :
    eLpNorm (fun x => g x-∫ z, ψ z*g z) (3/2) (volume.restrict {x : ℂ | ‖x‖ ≤ X}) ≤
      ∑ i, eLpNorm (fun x => ∫ y, ⟪green ψ x y,β i y⟫) (3/2)
        (volume.restrict {x : ℂ | ‖x‖ ≤ X}) := by
  let μ := volume.restrict {x : ℂ | ‖x‖ ≤ X}
  let F : ι → ℂ → ℝ := fun i x => ∫ y, ⟪green ψ x y,β i y⟫
  have hmeas : ∀ i, AEStronglyMeasurable (F i) μ := fun i =>
    potential_aestronglyMeasurable _ (green_measurable ψ hψ.measurable) (hβ i)
  have heq : (fun x => g x-∫ z, ψ z*g z) =ᵐ[μ] fun x => ∑ i, F i x :=
    green_finite_decomposition hψ hψc hg hD hψ1 hψs hψB hRX hM hB hXY β hβ hβs hdecomp
  have hsum : eLpNorm (∑ i, F i) (3/2) μ ≤ ∑ i, eLpNorm (F i) (3/2) μ :=
    eLpNorm_sum_le (fun i _ => hmeas i) (by
      rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
      norm_num)
  rw [eLpNorm_congr_ae heq]
  have hfun : (∑ i, F i) = fun x => ∑ i, F i x := by ext x; simp
  rw [hfun] at hsum
  exact hsum

end PlanePotential

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

end DyadicHats

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
noncomputable section

open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

namespace DyadicHats

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

lemma densityDefect_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    0 ≤ densityDefect N r h k q := by
  have he := densityError_cost hr hR hN hh hs k q
  have hn : 0 ≤ ∫ x, |densityError N r h k q x| := integral_nonneg (fun x => abs_nonneg _)
  linarith

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

end CommonPrices

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

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments PricePieces

lemma rootMass_nonneg {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) :
    0 ≤ rootMass h r k S := sum_nonneg (fun _ _ => norm_nonneg _)

lemma sizeErrors_price {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : n ∈ fixedPalette.labels) :
    errorPrice (sizeErrors hr hh k p S n) (1/100) ≤
      (scale r k)⁻¹*(4*rootMass h r k S+2*cellPrice N r h k S) := by
  have hb : (sizeErrors hr hh k p S n none).mass ≤ (scale r k)⁻¹*4*rootMass h r k S := by
    change (∫ X, ‖rescale p (scale r k) (rootSum h r k S n) X‖) ≤ _
    rw [mass_rescale _ _ (scale_pos hr k)]
    simpa only [mul_assoc,rootMass] using mul_le_mul_of_nonneg_left
      (rootSum_mass hr hR hN hh hsupp k S (fixedPalette.unit n hn)) (inv_nonneg.mpr (scale_pos hr k).le)
  have hs := smallPiece_common_price hr hR hN hh hsupp k p S hn
  change (∑ i, (smallPiece hh hr k p S n i).size^(1/100:ℝ)*
    (smallPiece hh hr k p S n i).mass) ≤ _ at hs
  simp only [errorPrice,Fintype.sum_option,show (sizeErrors hr hh k p S n none).size = 1 from rfl,
    Real.one_rpow,one_mul]
  change (sizeErrors hr hh k p S n none).mass + (∑ i, (smallPiece hh hr k p S n i).size^(1/100:ℝ)*(smallPiece hh hr k p S n i).mass) ≤ _
  linarith

lemma sizeErrors_gradient {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {g : ℂ → ℝ} (hg : Differentiable ℝ g)
    (hh : Integrable (gradient g)) (hsupp : ∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R)
    (k : ℕ) (p : ℤ × ℤ) {n : ℂ} (hn : ‖n‖ = 1) (X : ℂ) (hX : ‖X‖ ≤ 12) :
    (∑ i, (sizeErrors hr hh k (point (scale r k) p) (cellRoots N p) n i).density X) =
      gradient (fun Y => g (point (scale r k) p+scale r k • Y)) X := by
  rw [Fintype.sum_option]
  change rescale _ _ (rootSum _ _ _ _ _) X+
    (∑ i : ErrorIndex N k, (smallPiece hh hr k _ _ n i).density X) = _
  rw [smallPiece_sum,gradient_affine hg]
  simp only [rescale,← smul_add,rootSum,← sum_add_distrib]
  have he := sum_congr rfl (fun q (_ : q ∈ cellRoots N p) =>
    (vector_decomposition hr hR hN hsupp k q hn (point (scale r k) p+scale r k • X)).symm)
  rw [he,← sum_smul,cell_partition (scale_pos hr k) (scale_index_bound hr hR hN k) hsupp p X hX]

/-- The endpoint-bin gradient price, with all root terms retained rather than
silently using the cone estimate at one-sided maximizing radii. -/
theorem size_cell_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) → ∀ (k : ℕ) (p : ℤ × ℤ)
    {n : ℂ}, n ∈ fixedPalette.labels → ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ X in Q, F X) ≤ ENNReal.ofReal (C*(scale r k)⁻¹*
        (rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ X, ‖X‖ ≤ 2 → ∀ t,
        EndpointRadius (fun Y => g (point (scale r k) p+scale r k • Y)) X t →
        ENNReal.ofReal ‖∫ Y in Metric.ball X t,
          gradient (fun Z => g (point (scale r k) p+scale r k • Z)) Y‖ ≤ F X := by
  obtain ⟨C,hC,hmajor⟩ := size_majorant (by norm_num : (0:ℝ) ≤ 2)
  refine ⟨4*C,by positivity,?_⟩
  intro N r R hr hR hN g hg hh hsupp k p n hn Q hQ
  let b := sizeErrors hr hh k (point (scale r k) p) (cellRoots N p) n
  have hg' : ContDiff ℝ 1 (fun Y => g (point (scale r k) p+scale r k • Y)) := hg.comp (by fun_prop)
  obtain ⟨F,hFm,hFi,hFb⟩ := hmajor b _ hg' Q hQ
  refine ⟨F,hFm,?_,?_⟩
  · apply hFi.trans
    apply ENNReal.ofReal_le_ofReal
    have hb := sizeErrors_price hr hR hN hh hsupp k (point (scale r k) p) (cellRoots N p) hn
    have hD : 0 ≤ cellPrice N r (gradient g) k (cellRoots N p) :=
      sum_nonneg (fun q _ => rootPrice_nonneg hr hR hN hh hsupp k q)
    change errorPrice b (1/100) ≤ _ at hb
    have hrk := scale_pos hr k
    nlinarith [mul_le_mul_of_nonneg_left hb hC.le,inv_nonneg.mpr hrk.le,
      mul_nonneg (inv_nonneg.mpr hrk.le) hD]
  · intro X hX t ht
    apply hFb X _ t ht
    filter_upwards with Y hY
    apply sizeErrors_gradient hr hR hN (hg.differentiable one_ne_zero) hh hsupp k p (fixedPalette.unit n hn)
    have hy : ‖Y-X‖ < 3 := by simpa only [Metric.mem_ball,dist_eq_norm] using hY
    have htri := norm_add_le (Y-X) X
    rw [sub_add_cancel] at htri
    linarith
end CommonPrices

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

namespace PlanePotential
open LocalCancellation

lemma green_restrict_density {ψ : ℂ → ℝ} {R X : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hRX : R ≤ X)
    (β : ℂ → ℂ) {x : ℂ} (hx : ‖x‖ ≤ X) (y : ℂ) :
    ⟪green ψ x y, ({y : ℂ | ‖y‖ ≤ X}.indicator β) y⟫ = ⟪green ψ x y,β y⟫ := by
  by_cases hy : ‖y‖ ≤ X
  · simp [hy]
  · rw [green_eq_zero_of_outside hψs hRX hx (lt_of_not_ge hy)]
    simp

lemma green_root_lp_local {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hRX : R ≤ X) (hM : 0 < R+X) (hB : 0 ≤ B) (hX : 0 < X)
    (hβ : Integrable β) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X}, (ENNReal.ofReal |∫ y, ⟪green ψ x y,β y⟫|)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(4*X)^(1/2:ℝ))) *
      (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  let β' := {y : ℂ | ‖y‖ ≤ X}.indicator β
  have hi : Integrable β' := hβ.indicator (measurableSet_le measurable_norm measurable_const)
  have hs : ∀ y, β' y ≠ 0 → ‖y‖ ≤ X := by
    intro y hy
    by_contra hn
    exact hy (by simp [β',hn])
  have h := green_root_lp hψm hψs hψB hM hB (show 0 < X+X by linarith) hi hs
  have he : (fun x => (ENNReal.ofReal |∫ y, ⟪green ψ x y,β' y⟫|)^(3/2:ℝ)) =ᵐ[volume.restrict {x : ℂ | ‖x‖ ≤ X}]
      (fun x => (ENNReal.ofReal |∫ y, ⟪green ψ x y,β y⟫|)^(3/2:ℝ)) := by
    filter_upwards [ae_restrict_mem (measurableSet_le measurable_norm measurable_const)] with x hx
    congr 3
    exact integral_congr_ae (ae_of_all _ (green_restrict_density hψs hRX β hx))
  rw [lintegral_congr_ae he] at h
  have hm : (∫ y, ‖β' y‖) ≤ ∫ y, ‖β y‖ :=
    integral_mono hi.norm hβ.norm (fun y => norm_indicator_le_norm_self β y)
  have hm' := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hm) (by norm_num : (0:ℝ) ≤ 3/2)
  have h' := h.trans (mul_le_mul_right hm' _)
  simpa only [show 2*(X+X)=4*X by ring] using h'

lemma green_zero_piece_lp_ae {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X B L a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L) (ha : 0 < a)
    (z : ℂ) (hβ : Integrable β) (hzero : ∫ y, β y = 0)
    (hβs : ∀ᵐ y, β y ≠ 0 → ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X},
      (ENNReal.ofReal |∫ y, ⟪green ψ x y,β y⟫|)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((8*Real.pi*(2*B*(R+X)^2)^(3/2:ℝ)+
      Real.pi*(8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)^(3/2:ℝ))*a^(1/2:ℝ)) *
      (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  let β' := {y : ℂ | ‖y-z‖ ≤ a}.indicator β
  have he : β' =ᵐ[volume] β := by
    filter_upwards [hβs] with y hy
    by_cases hs : ‖y-z‖ ≤ a
    · simp [β',hs]
    · have hz : β y = 0 := by by_contra hn; exact hs (hy hn)
      simp [β',hs,hz]
  have hi : Integrable β' := hβ.congr he.symm
  have hz : ∫ y, β' y = 0 := (integral_congr_ae he).trans hzero
  have hs : ∀ y, β' y ≠ 0 → ‖y-z‖ ≤ a := by
    intro y hy
    by_contra hn
    exact hy (by simp [β',hn])
  have hp (x : ℂ) : (∫ y, ⟪green ψ x y,β' y⟫) = ∫ y, ⟪green ψ x y,β y⟫ :=
    integral_congr_ae (he.mono (fun y hy => by simpa only using congrArg (fun z => ⟪green ψ x y,z⟫) hy))
  have hm : (∫ y, ‖β' y‖) = ∫ y, ‖β y‖ := integral_congr_ae (he.mono (fun y hy => by simpa only using congrArg norm hy))
  simpa only [hp,hm] using green_zero_piece_lp hψm hψs hψB hψL hM hB hL ha z hi hz hs

/-- The local decomposition theorem does not demand artificial bounded support
of the original densities: the actual Green kernel vanishes outside the
observation ball. -/
theorem green_decomposition_norm_local {ι : Type*} [Fintype ι]
    {ψ g : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hg : ContDiff ℝ 1 g) {D R X B : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (hψ1 : ∫ z, ψ z = 1)
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hRX : R ≤ X) (hM : 0 < R+X) (hB : 0 ≤ B) (hX : 0 < X)
    (β : ι → ℂ → ℂ) (hβ : ∀ i, Integrable (β i))
    (hdecomp : ∀ᵐ y, ‖y‖ ≤ X → gradient g y = ∑ i, β i y) :
    eLpNorm (fun x => g x-∫ z, ψ z*g z) (3/2) (volume.restrict {x : ℂ | ‖x‖ ≤ X}) ≤
      ∑ i, eLpNorm (fun x => ∫ y, ⟪green ψ x y,β i y⟫) (3/2)
        (volume.restrict {x : ℂ | ‖x‖ ≤ X}) := by
  let β' := fun i => {y : ℂ | ‖y‖ ≤ X}.indicator (β i)
  have hi (i : ι) : Integrable (β' i) := (hβ i).indicator (measurableSet_le measurable_norm measurable_const)
  have hs (i : ι) (y : ℂ) (hy : β' i y ≠ 0) : ‖y‖ ≤ X := by
    by_contra hn
    exact hy (by simp [β',hn])
  have hd : ∀ᵐ y, ‖y‖ ≤ X → gradient g y = ∑ i, β' i y := by
    filter_upwards [hdecomp] with y hy hY
    simpa [β',hY] using hy hY
  have h := green_decomposition_norm hψ hψc hg hD hψ1 hψs hψB hRX hM hB
    (show 0 < X+X by linarith) β' hi hs hd
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro i _
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_le measurable_norm measurable_const)] with x hx
  exact integral_congr_ae (ae_of_all _ (green_restrict_density hψs hRX (β i) hx))

/-- Uniform fractional small-support gain expressed in the common price
exponent 1/100, including the unrestricted unit-size terms. -/
theorem exists_green_price : ∃ (ψ : ℂ → ℝ) (C : ℝ), 0 < C ∧
    ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (∫ z, ψ z) = 1 ∧
    (∀ z, ψ z ≠ 0 → ‖z‖ ≤ 1) ∧
    ∀ b : ErrorPiece 2,
      eLpNorm (fun x => ∫ y, ⟪green ψ x y,b.density y⟫) (3/2)
        (volume.restrict {x : ℂ | ‖x‖ ≤ 8}) ≤
        ENNReal.ofReal (C*b.size^(1/100:ℝ)*b.mass) := by
  obtain ⟨ψ,B,L,hB,hL,hψ,hψc,hψ1,hψs,hψB,hψL⟩ := exists_kernel_cutoff
  let A : ℝ := (2*B*(1+8)^2)^(3/2:ℝ)*(4*Real.pi*(4*8)^(1/2:ℝ))
  let Z : ℝ := 8*Real.pi*(2*B*(1+8)^2)^(3/2:ℝ)+
    Real.pi*(8*B*(1+8)^2+(64/3:ℝ)*L*(1+8)^3)^(3/2:ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  let C : ℝ := A^(2/3:ℝ)+Z^(2/3:ℝ)*2^(1/3:ℝ)+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ψ,C,hC,hψ,hψc,hψ1,hψs,?_⟩
  intro b
  have hb0 := b.size_pos.le
  have hm0 := b.mass_nonneg
  rw [eLpNorm_eq_eLpNorm' (by norm_num : (3/2:ℝ≥0∞) ≠ 0)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
  by_cases hb : b.size < 1
  · have ha : 0 < 2*b.size := mul_pos (by norm_num) b.size_pos
    have hp := green_zero_piece_lp_ae hψ.continuous.measurable hψs hψB hψL (by norm_num : (0:ℝ) < 1+8)
      hB hL ha b.center b.integrable (b.zero_mass hb) (b.support hb)
    have hn := eLpNorm_three_halves_bound _ hp
    change _ ≤ (ENNReal.ofReal (Z*(2*b.size)^(1/2:ℝ)))^(2/3:ℝ)*ENNReal.ofReal b.mass at hn
    have he : (ENNReal.ofReal (Z*(2*b.size)^(1/2:ℝ)))^(2/3:ℝ)*ENNReal.ofReal b.mass =
        ENNReal.ofReal (Z^(2/3:ℝ)*2^(1/3:ℝ)*b.size^(1/3:ℝ)*b.mass) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.mul_rpow hZ (by positivity),← Real.rpow_mul (by positivity),show (1/2:ℝ)*(2/3)=1/3 by norm_num,
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) b.size_pos.le]
      ring
    rw [he] at hn
    apply hn.trans (ENNReal.ofReal_le_ofReal _)
    have hbpow : b.size^(1/3:ℝ) ≤ b.size^(1/100:ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge b.size_pos b.size_le_one (by norm_num)
    have hZC : Z^(2/3:ℝ)*2^(1/3:ℝ) ≤ C := by dsimp [C]; linarith [Real.rpow_nonneg hA (2/3)]
    exact mul_le_mul_of_nonneg_right
      (le_trans (mul_le_mul_of_nonneg_left hbpow (by positivity))
        (mul_le_mul_of_nonneg_right hZC (by positivity))) b.mass_nonneg
  · have hb1 : b.size = 1 := le_antisymm b.size_le_one (le_of_not_gt hb)
    have hp := green_root_lp_local hψ.continuous.measurable hψs hψB (by norm_num : (1:ℝ) ≤ 8)
      (by norm_num : (0:ℝ) < 1+8) hB (by norm_num : (0:ℝ) < 8) b.integrable
    have hn := eLpNorm_three_halves_bound _ hp
    change _ ≤ (ENNReal.ofReal A)^(2/3:ℝ)*ENNReal.ofReal b.mass at hn
    rw [ENNReal.ofReal_rpow_of_nonneg hA (by norm_num),← ENNReal.ofReal_mul (by positivity)] at hn
    simp only [hb1,Real.one_rpow,mul_one]
    apply hn.trans (ENNReal.ofReal_le_ofReal _)
    apply mul_le_mul_of_nonneg_right _ b.mass_nonneg
    dsimp [C]
    linarith [mul_nonneg (Real.rpow_nonneg hZ (2/3)) (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (1/3))]
end PlanePotential

namespace DiskMaximalTools

lemma strong_three_halves_norm {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) [IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x)))] :
    eLpNorm (fun x => (rationalMaximal (volume.withDensity (fun x => ENNReal.ofReal (f x))) x).toReal)
      (3/2) volume ≤ ENNReal.ofReal ((150*2^(1/2:ℝ))^(2/3:ℝ))*eLpNorm f (3/2) volume := by
  have h := strong_rationalMaximal hf hf0 (by norm_num : (1:ℝ) < 3/2)
  have hs := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 2/3)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2/3)] at hs
  have hp : (50*(3/2:ℝ)*2^((3/2:ℝ)-1)/((3/2:ℝ)-1)) = 150*2^(1/2:ℝ) := by
    norm_num
    ring
  rw [hp,ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)] at hs
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (3/2:ℝ≥0∞) ≠ 0)
    (ENNReal.div_ne_top (by norm_num) (by norm_num)),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (3/2:ℝ≥0∞) ≠ 0)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))]
  norm_num only [ENNReal.toReal_div,ENNReal.toReal_ofNat,one_div_div]
  simp only [← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,
    abs_of_nonneg (hf0 _),ENNReal.ofReal_rpow_of_nonneg (hf0 _) (by norm_num : (0:ℝ) ≤ 3/2),
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num : (0:ℝ) ≤ 3/2)] at hs ⊢
  exact hs

lemma lintegral_le_three_halves_norm {f : ℂ → ℝ} (hf : AEStronglyMeasurable f volume)
    (hf0 : ∀ x, 0 ≤ f x) {Q : Set ℂ} (hQ : volume Q ≤ 1) :
    (∫⁻ x in Q, ENNReal.ofReal (f x)) ≤ eLpNorm f (3/2) volume := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (show (1:ℝ≥0∞) ≤ 3/2 by rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]; norm_num) hf.restrict (μ := volume.restrict Q)
  have he : (1 / ENNReal.toReal 1 - 1 / ENNReal.toReal (3/2)) = (1/3:ℝ) := by norm_num
  rw [he,Measure.restrict_apply_univ] at h
  have hpow : (volume Q)^(1/3:ℝ) ≤ 1 := by
    simpa using ENNReal.rpow_le_rpow hQ (by norm_num : (0:ℝ) ≤ 1/3)
  calc
    _ = eLpNorm f 1 (volume.restrict Q) := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      simp only [← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (hf0 _)]
    _ ≤ eLpNorm f (3/2) (volume.restrict Q)*(volume Q)^(1/3:ℝ) := h
    _ ≤ eLpNorm f (3/2) (volume.restrict Q) := by simpa using mul_le_mul_right hpow _
    _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self
end DiskMaximalTools

namespace PlanePotential
open LocalCancellation

/-- The complete local L^(3/2) value estimate for a genuine finite vector
cancellation decomposition, with the common 1/100 price. -/
theorem local_value_lp : ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type} [Fintype ι] (b : ι → ErrorPiece 2) {g : ℂ → ℝ},
    ContDiff ℝ 1 g → (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) →
    (∀ᵐ y, ‖y‖ ≤ 8 → gradient g y = ∑ i, (b i).density y) →
    ∃ c : ℝ, eLpNorm (fun x => g x-c) (3/2) (volume.restrict {x : ℂ | ‖x‖ ≤ 8}) ≤
      ENNReal.ofReal (C * errorPrice b (1/100)) := by
  obtain ⟨ψ,C,hC,hψ,hψc,hψ1,hψs,hprice⟩ := exists_green_price
  obtain ⟨B,hB⟩ := hψc.exists_bound_of_continuous hψ.continuous
  have hB0 : 0 ≤ B := (norm_nonneg (ψ 0)).trans (hB 0)
  have hψB (z : ℂ) : |ψ z| ≤ B := by simpa only [Real.norm_eq_abs] using hB z
  refine ⟨C,hC,?_⟩
  intro ι _ b g hg hD hdecomp
  obtain ⟨D,hD⟩ := hD
  refine ⟨∫ z, ψ z*g z,?_⟩
  apply (green_decomposition_norm_local hψ.continuous hψc hg hD hψ1 hψs hψB
    (by norm_num : (1:ℝ) ≤ 8) (by norm_num : (0:ℝ) < 1+8) hB0 (by norm_num : (0:ℝ) < 8)
    (fun i => (b i).density) (fun i => (b i).integrable) hdecomp).trans
  apply (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hprice (b i))).trans_eq
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (b i).size_pos.le _)) (b i).mass_nonneg)]
  congr 1
  rw [errorPrice,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end PlanePotential

namespace DiskMoments
open DiskMaximalTools

lemma signedAverage_sub_const {g : ℂ → ℝ} (hg : Continuous g) (c : ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    signedAverage (fun y => g y-c) x t = signedAverage g x t-c := by
  have hi : IntegrableOn g (Metric.ball x t) :=
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall x t)).mono_set Metric.ball_subset_closedBall
  have hc : IntegrableOn (fun _ : ℂ => c) (Metric.ball x t) := integrableOn_const measure_ball_lt_top.ne
  unfold signedAverage
  rw [integral_sub hi hc,integral_const]
  have hv : (volume (Metric.ball x t)).toReal = Real.pi*t^2 := by
    rw [volume_disk_real x ht.le,ENNReal.toReal_ofReal (by positivity)]
  simp only [Measure.real,Measure.restrict_apply_univ,hv,smul_eq_mul]
  field_simp

/-- A true disk average of a continuous function is controlled by the local
absolute-density maximal function. No maximizing-radius selection is used. -/
lemma local_average_le {g : ℂ → ℝ} (hg : Continuous g) (c : ℝ)
    {x : ℂ} (hx : ‖x‖ ≤ 2) {t : ℝ} (ht : 0 < t) (ht4 : t ≤ 4) :
    ENNReal.ofReal |signedAverage g x t-c| ≤
      rationalMaximal (volume.withDensity (fun y => ENNReal.ofReal
        (({y : ℂ | ‖y‖ ≤ 8}.indicator (fun y => |g y-c|)) y))) x := by
  let f : ℂ → ℝ := {y : ℂ | ‖y‖ ≤ 8}.indicator (fun y => |g y-c|)
  have hf : Measurable f := ((hg.measurable.sub measurable_const).abs).indicator
    (measurableSet_le measurable_norm measurable_const)
  have hfi : Integrable f := by
    apply IntegrableOn.integrable_indicator _ (measurableSet_le measurable_norm measurable_const)
    apply ContinuousOn.integrableOn_compact
      (show IsCompact {y : ℂ | ‖y‖ ≤ 8} by simpa only [Metric.closedBall,dist_zero_right] using isCompact_closedBall (0:ℂ) 8)
    exact (hg.sub continuous_const).abs.continuousOn
  have hsub (y : ℂ) (hy : y ∈ Metric.ball x t) : ‖y‖ ≤ 8 := by
    have hy' : ‖y-x‖ < t := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
    have hh := norm_add_le (y-x) x
    rw [sub_add_cancel] at hh
    linarith
  have he : (∫ y in Metric.ball x t, f y) = ∫ y in Metric.ball x t, |g y-c| := by
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    simp [f,hsub y hy]
  have hav : |signedAverage g x t-c| ≤ (∫ y in Metric.ball x t, f y)/(Real.pi*t^2) := by
    rw [← signedAverage_sub_const hg c x ht,signedAverage,abs_div,abs_of_pos (by positivity : 0 < Real.pi*t^2),he]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => g y-c) (μ := volume.restrict (Metric.ball x t))
  have hν : (volume.withDensity (fun y => ENNReal.ofReal (f y))) (Metric.ball x t) =
      ENNReal.ofReal (∫ y in Metric.ball x t, f y) := by
    rw [withDensity_apply _ measurableSet_ball]
    exact (ofReal_integral_eq_lintegral_ofReal hfi.integrableOn
      (ae_of_all _ (fun y => by dsimp [f]; exact Set.indicator_nonneg (fun _ _ => abs_nonneg _ ) y))).symm
  apply (ENNReal.ofReal_le_ofReal hav).trans
  rw [ENNReal.ofReal_div_of_pos (by positivity : 0 < Real.pi*t^2),← hν,← volume_disk_real x ht.le]
  exact disk_average_le_rationalMaximal_exact _ x ht
end DiskMoments

namespace PlanePotential
open LocalCancellation DiskMaximalTools DiskMoments

/-- Full local value-oscillation price, for every pair of positive radii at
most four. The measurable majorant is an actual centered Euclidean disk
maximal function, not an assumed analytic input. -/
theorem local_value_majorant : ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type} [Fintype ι] (b : ι → ErrorPiece 2) {g : ℂ → ℝ},
    ContDiff ℝ 1 g → (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) →
    (∀ᵐ y, ‖y‖ ≤ 8 → gradient g y = ∑ i, (b i).density y) →
    ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ x in Q, F x) ≤ ENNReal.ofReal (C*errorPrice b (1/100)) ∧
      ∀ x, ‖x‖ ≤ 2 → ∀ t t', 0 < t → t ≤ 4 → 0 < t' → t' ≤ 4 →
        ENNReal.ofReal |signedAverage g x t-signedAverage g x t'| ≤ F x := by
  obtain ⟨C,hC,hlocal⟩ := local_value_lp
  let K : ℝ := (150*2^(1/2:ℝ))^(2/3:ℝ)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨2*K*C,by positivity,?_⟩
  intro ι _ b g hg hD hdecomp Q hQ
  obtain ⟨c,hc⟩ := hlocal b hg hD hdecomp
  let f : ℂ → ℝ := {y : ℂ | ‖y‖ ≤ 8}.indicator (fun y => |g y-c|)
  have hf : Measurable f := ((hg.continuous.measurable.sub measurable_const).abs).indicator
    (measurableSet_le measurable_norm measurable_const)
  have hf0 (y : ℂ) : 0 ≤ f y := Set.indicator_nonneg (fun _ _ => abs_nonneg _) y
  have hfi : Integrable f := by
    apply IntegrableOn.integrable_indicator _ (measurableSet_le measurable_norm measurable_const)
    apply ContinuousOn.integrableOn_compact
      (show IsCompact {y : ℂ | ‖y‖ ≤ 8} by simpa only [Metric.closedBall,dist_zero_right] using isCompact_closedBall (0:ℂ) 8)
    exact (hg.continuous.sub continuous_const).abs.continuousOn
  let ν := volume.withDensity (fun y => ENNReal.ofReal (f y))
  have hν : ν univ = ENNReal.ofReal (∫ y, f y) := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0)).symm
  have : IsFiniteMeasure ν := ⟨by rw [hν]; exact ENNReal.ofReal_lt_top⟩
  let M : ℂ → ℝ := fun x => (rationalMaximal ν x).toReal
  have hM : Measurable M := (measurable_rationalMaximal ν).ennreal_toReal
  have hMf : ∀ x, rationalMaximal ν x ≠ ⊤ := by
    obtain ⟨B,hB⟩ := (isCompact_closedBall (0:ℂ) 8).exists_bound_of_continuousOn
      (hg.continuous.sub (continuous_const (y := c))).continuousOn
    have hbnd (y : ℂ) : f y ≤ max B 0 := by
      by_cases hy : ‖y‖ ≤ 8
      · have hby := hB y (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy)
        simpa [f, hy, Real.norm_eq_abs] using hby.trans (le_max_left B 0)
      · simp [f, hy]
    intro x
    exact ne_of_lt ((rationalMaximal_le_of_density_le (fun y => ENNReal.ofReal_le_ofReal (hbnd y)) x).trans_lt ENNReal.ofReal_lt_top)
  have hfnorm : eLpNorm f (3/2) volume = eLpNorm (fun x => g x-c) (3/2) (volume.restrict {x : ℂ | ‖x‖ ≤ 8}) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_le measurable_norm measurable_const)]
    simpa only [Real.norm_eq_abs] using eLpNorm_norm (fun x => g x-c) (p := (3/2:ℝ≥0∞)) (μ := volume.restrict {x : ℂ | ‖x‖ ≤ 8})
  have hn : eLpNorm M (3/2) volume ≤ ENNReal.ofReal K*ENNReal.ofReal (C*errorPrice b (1/100)) := by
    apply (strong_three_halves_norm hf hf0).trans
    apply mul_le_mul_right _ _
    simpa only [hfnorm] using hc
  refine ⟨fun x => ENNReal.ofReal 2*ENNReal.ofReal (M x),measurable_const.mul hM.ennreal_ofReal,?_,?_⟩
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply (mul_le_mul_right (lintegral_le_three_halves_norm hM.aestronglyMeasurable
      (fun _ => ENNReal.toReal_nonneg) (by simpa using hQ)) _).trans
    apply (mul_le_mul_right hn _).trans_eq
    rw [← ENNReal.ofReal_mul hK.le,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  · intro x hx t t' ht ht4 ht' ht4'
    have ha : |signedAverage g x t-c| ≤ M x :=
      (ENNReal.ofReal_le_iff_le_toReal (hMf x)).mp (local_average_le hg.continuous c hx ht ht4)
    have hb : |signedAverage g x t'-c| ≤ M x :=
      (ENNReal.ofReal_le_iff_le_toReal (hMf x)).mp (local_average_le hg.continuous c hx ht' ht4')
    change ENNReal.ofReal _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (M x)
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply ENNReal.ofReal_le_ofReal
    have hh := abs_sub_le (signedAverage g x t) c (signedAverage g x t')
    rw [abs_sub_comm c] at hh
    linarith
end PlanePotential

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

namespace CommonPrices
open DyadicHats ConeCoordinates LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments PricePieces

/-- The actual common-price value estimate, including every terminal error and
all roots. This is the third local analytic input to signed run assembly. -/
theorem value_cell_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ)
    {n : ℂ}, n ∈ fixedPalette.labels → ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ X in Q, F X) ≤ ENNReal.ofReal (C*(scale r k)⁻¹*
        (rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ X, ‖X‖ ≤ 2 → ∀ t t', 0 < t → t ≤ 4 → 0 < t' → t' ≤ 4 →
        ENNReal.ofReal |signedAverage (fun Y => g (point (scale r k) p+scale r k • Y)) X t-
          signedAverage (fun Y => g (point (scale r k) p+scale r k • Y)) X t'| ≤ F X := by
  obtain ⟨C,hC,hmajor⟩ := PlanePotential.local_value_majorant
  refine ⟨4*C,by positivity,?_⟩
  intro N r R hr hR hN g hg hh hsupp hD k p n hn Q hQ
  let b := sizeErrors hr hh k (point (scale r k) p) (cellRoots N p) n
  have hg' : ContDiff ℝ 1 (fun Y => g (point (scale r k) p+scale r k • Y)) := hg.comp (by fun_prop)
  obtain ⟨D,hD⟩ := hD
  have hD' := fderiv_affine_bound (hg.differentiable one_ne_zero) (point (scale r k) p) (scale r k) hD
  have hd : ∀ᵐ X, ‖X‖ ≤ 8 →
      gradient (fun Y => g (point (scale r k) p+scale r k • Y)) X = ∑ i, (b i).density X := by
    filter_upwards with X hX
    exact (sizeErrors_gradient hr hR hN (hg.differentiable one_ne_zero) hh hsupp k p
      (fixedPalette.unit n hn) X (by linarith)).symm
  obtain ⟨F,hFm,hFi,hFb⟩ := hmajor b hg' hD' hd Q hQ
  refine ⟨F,hFm,?_,hFb⟩
  apply hFi.trans
  apply ENNReal.ofReal_le_ofReal
  have hb := sizeErrors_price hr hR hN hh hsupp k (point (scale r k) p) (cellRoots N p) hn
  have hDp : 0 ≤ cellPrice N r (gradient g) k (cellRoots N p) :=
    sum_nonneg (fun q _ => rootPrice_nonneg hr hR hN hh hsupp k q)
  change errorPrice b (1/100) ≤ _ at hb
  have hrk := scale_pos hr k
  nlinarith [mul_le_mul_of_nonneg_left hb hC.le,inv_nonneg.mpr hrk.le,
    mul_nonneg (inv_nonneg.mpr hrk.le) hDp]
end CommonPrices

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

lemma endpointRadius_affine {g : ℂ → ℝ} (p X : ℂ) {r t : ℝ} (hr : 0 < r)
    (ht : PhysicalEndpointRadius g r (p+r • X) (r*t)) :
    EndpointRadius (fun Y => g (p+r • Y)) X t := by
  have ht1 : 1 ≤ t := (le_of_mul_le_mul_left (by simpa only [mul_one] using ht.1.1) hr)
  have ht2 : t ≤ 2 := (le_of_mul_le_mul_left (by simpa only [mul_comm 2 r] using ht.1.2) hr)
  refine ⟨⟨ht1,ht2⟩,?_⟩
  rcases ht.2 with he | he | he
  · left
    nlinarith
  · right; left
    nlinarith
  · right; right
    intro s hs
    rw [signedAverage_affine _ _ _ hr (by linarith [hs.1]),signedAverage_affine _ _ _ hr (by linarith)]
    exact he (r*s) ⟨by nlinarith [hs.1],by nlinarith [hs.2]⟩
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

lemma value_majorant_integral {F : ℂ → ℝ≥0∞} {C P : ℝ} (p : ℂ) {r : ℝ}
    (hr : 0 < r) (hF : (∫⁻ X in unitCell, F X) ≤ ENNReal.ofReal (C*r⁻¹*P)) :
    (∫⁻ y in cell p r, F (toUnit p r y)) ≤ ENNReal.ofReal (C*r*P) := by
  rw [cell_majorant p hr.ne']
  apply (mul_le_mul' le_rfl hF).trans_eq
  rw [← ENNReal.ofReal_mul (sq_nonneg r)]
  congr 1
  field_simp
end PhysicalCells

namespace DiskMoments
lemma average_gradient_norm_le {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) {t : ℝ} (ht : 1 ≤ t) :
    ‖gradient (fun y => signedAverage g y t) x‖ ≤ ‖∫ y in Metric.ball x t, gradient g y‖ := by
  have hp : 0 < Real.pi*t^2 := mul_pos Real.pi_pos (sq_pos_of_pos (by linarith))
  have h1 : 1 ≤ Real.pi*t^2 := by nlinarith [Real.pi_gt_three,sq_nonneg (t-1)]
  rw [gradient_signedAverage hg hD x (by linarith),norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
  exact mul_le_of_le_one_left (norm_nonneg _) ((inv_le_one₀ hp).mpr h1)

lemma physical_gradient_norm_majorant {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (p X : ℂ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    {F : ℝ≥0∞}
    (hF : ENNReal.ofReal ‖gradient (fun Y => signedAverage (fun Z => g (p+r • Z)) Y t) X‖ ≤ F) :
    ENNReal.ofReal ‖gradient (fun y => signedAverage g y (r*t)) (p+r • X)‖ ≤
      ENNReal.ofReal r⁻¹*F := by
  have h : ENNReal.ofReal r⁻¹*_ ≤ ENNReal.ofReal r⁻¹*F := mul_le_mul' le_rfl hF
  rw [gradient_average_affine hg hD p X hr ht,norm_smul,Real.norm_eq_abs,abs_of_pos hr,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le),inv_mul_cancel_left₀ hr.ne'] at h
  exact h

end DiskMoments

namespace CommonPrices
open DyadicHats ConeCoordinates LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments PricePieces PhysicalCells

theorem physical_size_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ)
    {n : ℂ}, n ∈ fixedPalette.labels →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ y in cell (point (scale r k) p) (scale r k), F y) ≤ ENNReal.ofReal
        (C*(rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t,
        PhysicalEndpointRadius g (scale r k) y t →
        ENNReal.ofReal ‖gradient (fun z => signedAverage g z t) y‖ ≤ F y := by
  obtain ⟨C,hC,hmajor⟩ := size_cell_price
  refine ⟨C,hC,?_⟩
  intro N r R hr hR hN g hg hh hsupp hD k p n hn
  obtain ⟨D,hD⟩ := hD
  obtain ⟨D',hD'⟩ := fderiv_affine_bound (hg.differentiable one_ne_zero) (point (scale r k) p) (scale r k) hD
  obtain ⟨F,hFm,hFi,hFb⟩ := hmajor hr hR hN hg hh hsupp k p hn unitCell (by rw [volume_unitCell]; norm_num)
  refine ⟨fun y => ENNReal.ofReal (scale r k)⁻¹*F (toUnit (point (scale r k) p) (scale r k) y),
    measurable_const.mul (hFm.comp (toUnit_continuous _ _).measurable),
    derivative_majorant_integral _ (scale_pos hr k) hFi,?_⟩
  intro y hy t ht
  let X := toUnit (point (scale r k) p) (scale r k) y
  have hX : ‖X‖ ≤ 2 := norm_unitCell hy
  have he : point (scale r k) p+scale r k • X = y := affine_toUnit _ (scale_pos hr k).ne' y
  have ht' : PhysicalEndpointRadius g (scale r k)
      (point (scale r k) p+scale r k • X) (scale r k*(t/scale r k)) := by
    simpa only [he,mul_div_cancel₀ _ (scale_pos hr k).ne'] using ht
  have htn := endpointRadius_affine _ X (scale_pos hr k) ht'
  have hg' : ContDiff ℝ 1 (fun Z => g (point (scale r k) p+scale r k • Z)) := hg.comp (by fun_prop)
  have hb := (ENNReal.ofReal_le_ofReal (average_gradient_norm_le hg' hD' X htn.1.1)).trans
    (hFb X hX _ htn)
  have hf := physical_gradient_norm_majorant hg hD (point (scale r k) p) X
    (scale_pos hr k) (by linarith [htn.1.1]) hb
  simpa only [he,mul_div_cancel₀ _ (scale_pos hr k).ne'] using hf

theorem physical_value_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ)
    {n : ℂ}, n ∈ fixedPalette.labels →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ y in cell (point (scale r k) p) (scale r k), F y) ≤ ENNReal.ofReal
        (C*scale r k*(rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t t',
        0 < t → t ≤ 4*scale r k → 0 < t' → t' ≤ 4*scale r k →
        ENNReal.ofReal |signedAverage g y t-signedAverage g y t'| ≤ F y := by
  obtain ⟨C,hC,hmajor⟩ := value_cell_price
  refine ⟨C,hC,?_⟩
  intro N r R hr hR hN g hg hh hsupp hD k p n hn
  obtain ⟨F,hFm,hFi,hFb⟩ := hmajor hr hR hN hg hh hsupp hD k p hn unitCell (by rw [volume_unitCell]; norm_num)
  refine ⟨fun y => F (toUnit (point (scale r k) p) (scale r k) y),
    hFm.comp (toUnit_continuous _ _).measurable,
    value_majorant_integral _ (scale_pos hr k) hFi,?_⟩
  intro y hy t t' ht hb ht' hb'
  let X := toUnit (point (scale r k) p) (scale r k) y
  have he : point (scale r k) p+scale r k • X = y := affine_toUnit _ (scale_pos hr k).ne' y
  have hrk := scale_pos hr k
  have hf := hFb X (norm_unitCell hy) (t/scale r k) (t'/scale r k)
    (div_pos ht hrk) ((div_le_iff₀ hrk).mpr hb) (div_pos ht' hrk) ((div_le_iff₀ hrk).mpr hb')
  simpa only [signedAverage_affine _ _ _ hrk (div_pos ht hrk),
    signedAverage_affine _ _ _ hrk (div_pos ht' hrk),he,mul_div_cancel₀ _ hrk.ne'] using hf
end CommonPrices

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

namespace CommonPrices
open DyadicHats ConeCoordinates Finset

lemma cellPrice_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (S : Finset (Grid N)) :
    0 ≤ cellPrice N r h k S := sum_nonneg (fun q _ => rootPrice_nonneg hr hR hN hh hsupp k q)
end CommonPrices

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

namespace CommonPrices
open DyadicHats ConeCoordinates Finset DiskMoments PhysicalCells SignedRuns FiniteLabels ActualLabels

/-- A single actual endpoint price pays both the gradient and the normalized
oscillation. It is introduced before any spatial supremum is taken. -/
theorem physical_joint_price_oai : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ) (n : Label),
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ y in cell (point (scale r k) p) (scale r k), F y) ≤ ENNReal.ofReal
        (C*(rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      (∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t,
        PhysicalEndpointRadius g (scale r k) y t →
        ENNReal.ofReal ‖gradient (fun z => signedAverage g z t) y‖ ≤ F y) ∧
      (∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t t',
        0 < t → t ≤ 4*scale r k → 0 < t' → t' ≤ 4*scale r k →
        ENNReal.ofReal (|signedAverage g y t-signedAverage g y t'|/scale r k) ≤ F y) := by
  obtain ⟨Cs,hCs,hp⟩ := physical_size_price
  obtain ⟨Cv,hCv,hq⟩ := physical_value_price
  refine ⟨Cs+Cv,add_pos hCs hCv,?_⟩
  intro N r R hr hR hN g hg hh hs hd k p n
  obtain ⟨F,hFm,hFi,hFb⟩ := hp hr hR hN hg hh hs hd k p n.property
  obtain ⟨G,hGm,hGi,hGb⟩ := hq hr hR hN hg hh hs hd k p n.property
  have hrk := scale_pos hr k
  let B := rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p)
  have hB : 0 ≤ B := add_nonneg (rootMass_nonneg _ _ _ _) (cellPrice_nonneg hr hR hN hh hs k _)
  have hG : (∫⁻ y in cell (point (scale r k) p) (scale r k), ENNReal.ofReal (scale r k)⁻¹*G y) ≤ ENNReal.ofReal (Cv*B) := by
    rw [lintegral_const_mul _ hGm]
    calc
      _ ≤ ENNReal.ofReal (scale r k)⁻¹*ENNReal.ofReal (Cv*scale r k*B) := mul_le_mul' le_rfl hGi
      _ = _ := by rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hrk.le)]; congr 1; field_simp
  refine ⟨fun y => F y+ENNReal.ofReal (scale r k)⁻¹*G y,
    hFm.add (measurable_const.mul hGm),?_,?_,?_⟩
  · rw [lintegral_add_left hFm]
    calc
      _ ≤ ENNReal.ofReal (Cs*B)+ENNReal.ofReal (Cv*B) := add_le_add hFi hG
      _ = _ := by rw [← ENNReal.ofReal_add (mul_nonneg hCs.le hB) (mul_nonneg hCv.le hB),← add_mul]
  · intro y hy t ht
    exact (hFb y hy t ht).trans le_self_add
  · intro y hy t t' ht hb ht' hb'
    have hgg := mul_le_mul' (le_refl (ENNReal.ofReal (scale r k)⁻¹)) (hGb y hy t t' ht hb ht' hb')
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hrk.le),inv_mul_eq_div] at hgg
    exact hgg.trans le_add_self
end CommonPrices

end

end OAI
end

theorem solution : type_of% @OAI.CommonPrices.physical_joint_price_oai := @OAI.CommonPrices.physical_joint_price_oai
