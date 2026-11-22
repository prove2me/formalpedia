-- Prove2me | solution 1 for NemytskiiLebesgue.memLp_nemytskii_of_growth_of_aestronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:34:09.728284+00:00
-- url     : https://prove2.me/submissions/fd85cd8f-3250-493d-ab2e-013b827c4348

module
public import Mathlib.MeasureTheory.Function.UnifTight
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Theorems.Thm_NemytskiiLebesgue_ne_zero_of_ge_one


set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal Topology
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F}
    {p : ℝ≥0∞} (h0p : 0 < p) (hp : p ≠ ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q ≠ ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {u : Ω → D} (hup : MemLp u p μ)
    (hfu : AEStronglyMeasurable (fun ω : Ω => f ω (u ω)) μ) :
    MemLp (fun ω : Ω => f ω (u ω)) q μ := by
  have hfuaCpq : ∀ᵐ ω : Ω ∂μ, ‖f ω (u ω)‖ ≤ |a ω| + C * ‖u ω‖ ^ (p / q).toReal := by
    filter_upwards [hfaCpq] with ω hω using hω (u ω)
  have integrabl : Integrable (fun ω : Ω => (|a ω| + C * ‖u ω‖ ^ (p / q).toReal) ^ q.toReal) μ := by
    have integrab :
        Integrable (fun ω : Ω => |a ω| ^ q.toReal) μ ∧
        Integrable (fun ω : Ω => (C * ‖u ω‖ ^ (p / q).toReal) ^ q.toReal) μ := by
      constructor
      · have := haq.integrable_norm_rpow
        aesop
      · have integra : Integrable (‖u ·‖ ^ p.toReal) μ := by
          convert hup.integrable_norm_rpow _ using 1 <;> aesop
        convert integra.const_mul (C ^ q.toReal) using 2
        rw [Real.mul_rpow hC (Real.rpow_nonneg (norm_nonneg (u _)) (p / q).toReal),
            ←Real.rpow_mul (norm_nonneg _),
            ENNReal.toReal_div,
            div_mul_cancel₀ _ (ne_of_gt (ENNReal.toReal_pos (ne_zero_of_ge_one h1q) hq))]
    apply ((integrab.left.add integrab.right).const_mul (2 ^ q.toReal)).mono'
    · exact ((haq.aestronglyMeasurable.norm.add
      ((hup.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable.const_mul
      C)).aemeasurable.pow_const _).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_of_nonneg (by positivity)]
      have ineq : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (x + y) ^ q.toReal ≤ 2 ^ q.toReal * (x ^ q.toReal + y
        ^ q.toReal) := by
        intro x y hx hy
        have ineq : (x + y) ^ q.toReal ≤ (2 * max x y) ^ q.toReal :=
          Real.rpow_le_rpow (add_nonneg hx hy) (by linarith [le_max_left x y, le_max_right x y])
            ENNReal.toReal_nonneg
        rw [Real.mul_rpow zero_le_two (le_sup_of_le_right hy)] at ineq
        apply ineq.trans
        apply mul_le_mul_of_nonneg_left
        · rw [max_def_lt]
          split_ifs <;> linarith [Real.rpow_nonneg hx q.toReal, Real.rpow_nonneg hy q.toReal]
        · positivity
      exact ineq |a ω| _ (abs_nonneg _) (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _))
  have integrble : Integrable (fun ω : Ω => ‖f ω (u ω)‖ ^ q.toReal) μ := by
    refine integrabl.mono' ?_ ?_
    · exact (hfu.norm.aemeasurable.pow_const q.toReal).aestronglyMeasurable
    · filter_upwards [hfuaCpq] with ω hω
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg (f ω (u ω))) q.toReal)]
      exact Real.rpow_le_rpow (norm_nonneg (f ω (u ω))) hω ENNReal.toReal_nonneg
  refine ⟨hfu, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_zero_of_ge_one h1q) hq]
  · apply ENNReal.rpow_lt_top_of_nonneg
    · positivity
    · convert integrble.right.ne using 1
      simp [Real.enorm_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg]
end NemytskiiLebesgue
