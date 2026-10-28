-- Prove2me | solution 1 for OAI.SignedDisk.LocalCancellation.direction_majorant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:36:16.33589+00:00
-- url     : https://prove2.me/submissions/56b2cffb-b159-47a0-aa62-050faeace34f

import Mathlib
import Definitions.Def_OAIW2SD000

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SignedDisk

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff

open scoped RealInnerProductSpace

open MeasureTheory Set Filter
open scoped Topology ENNReal

open scoped Real RealInnerProductSpace

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

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskGeometry1
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

namespace SignedDisk

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

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskGeometry2
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

namespace SignedDisk

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

namespace DiskMoments

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

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskKernels1
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
open scoped Topology RealInnerProductSpace ContDiff

noncomputable section

namespace SignedDisk

open MeasureTheory Set Filter
open scoped Topology Interval NNReal

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

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_LocalCancellation1
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
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal

noncomputable section

namespace SignedDisk

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

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_LocalCancellation2
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
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

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

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_LocalCancellation3
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
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

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

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskScales1
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
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

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

namespace DyadicMajorant

section
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

end

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

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_LocalCancellation4
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
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

namespace LocalCancellation

section
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

end

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

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_LocalCancellation5
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
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

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

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskScales2
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
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

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

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskScales3
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
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

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
theorem direction_majorant_oai {Cs κ : ℝ} (hCs : 0 ≤ Cs) (hκ : 0 < κ) :
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

open MeasureTheory Set
open scoped ENNReal NNReal

end SignedDisk

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SignedDisk.LocalCancellation.direction_majorant_oai.{u_1} := @OAI.SignedDisk.LocalCancellation.direction_majorant_oai.{u_1}
