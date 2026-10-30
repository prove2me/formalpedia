-- Prove2me | solution 1 for OAI.LipschitzHilbert.SourceLabeledLattice.eventually_selector_error_family_concentration_of_supported
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:29:26.008947+00:00
-- url     : https://prove2.me/submissions/13961b7e-4c3c-478d-a217-170eecdb5482

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_IntervalPoincare
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The interval energy estimate needed for the low-frequency part of
the smooth-convolution versus cell-average comparison. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem integral_square_le_mass_mul_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (g : Ω → ℝ)
    (hg : MemLp g 2 μ) (hgn : 0 ≤ᵐ[μ] g) :
    (∫ x, g x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, g x ^ 2 ∂μ := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ)) (g := g) (by filter_upwards; norm_num) hgn
    (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ))
    (by simpa using hg)
  simp only [one_mul, integral_const, smul_eq_mul, mul_one, Real.rpow_two,
    one_pow] at h
  have hsq := pow_le_pow_left₀ (integral_nonneg_of_ae hgn) h 2
  have heq (a : ℝ) (ha : 0 ≤ a) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  rwa [mul_pow, heq _ measureReal_nonneg, heq _ (integral_nonneg fun _ => sq_nonneg _)] at hsq

theorem interval_pair_energy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b)))
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖f x - f y‖ ^ 2 ≤ (b - a) * ∫ t in Icc a b, ‖deriv f t‖ ^ 2 := by
  have hd1 : IntegrableOn (fun t => ‖deriv f t‖) (Icc a b) := hd.norm.integrable (by norm_num)
  have htotal : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v →
      ‖f v - f u‖ ≤ ∫ t in Icc a b, ‖deriv f t‖ := by
    intro u hu v hv huv
    have hsub : Icc u v ⊆ Icc a b := fun t ht => ⟨hu.1.trans ht.1, ht.2.trans hv.2⟩
    have hraw := norm_sub_le_integral_of_norm_deriv_le_of_le huv
      (fun t ht => (hf t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hf t (hsub ⟨ht.1.le,ht.2.le⟩)).differentiableWithinAt)
      (B := fun t => ‖deriv f t‖) (by filter_upwards; intros; rfl)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le huv).mpr (hd1.mono_set hsub))
    refine hraw.trans ?_
    rw [intervalIntegral.integral_of_le huv]
    exact setIntegral_mono_set hd1 (by filter_upwards with t; exact norm_nonneg _)
      (Filter.Eventually.of_forall fun t ht => hsub ⟨ht.1.le,ht.2⟩)
  have hnorm : ‖f x - f y‖ ≤ ∫ t in Icc a b, ‖deriv f t‖ := by
    rcases le_total x y with hxy | hyx
    · rw [norm_sub_rev]
      exact htotal x hx y hy hxy
    · exact htotal y hy x hx hyx
  have hcauchy := integral_square_le_mass_mul_square (volume.restrict (Icc a b))
    (fun t => ‖deriv f t‖) hd.norm (by filter_upwards with t; exact norm_nonneg _)
  have hmass : (volume.restrict (Icc a b)).real univ = b - a := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [hmass] at hcauchy
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcauchy

theorem norm_sub_mean_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E) (hf : Integrable f μ)
    (hm : 0 < μ.real univ) (v : E) (B : ℝ)
    (hbound : ∀ᵐ y ∂μ, ‖v - f y‖ ≤ B) :
    ‖v - (μ.real univ)⁻¹ • ∫ y, f y ∂μ‖ ≤ B := by
  have heq : v - (μ.real univ)⁻¹ • ∫ y, f y ∂μ =
      (μ.real univ)⁻¹ • ∫ y, (v - f y) ∂μ := by
    rw [integral_sub (integrable_const v) hf, integral_const,
      smul_sub, smul_smul, inv_mul_cancel₀ hm.ne', one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
  calc
    _ ≤ (μ.real univ)⁻¹ * (B * μ.real univ) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le_const hbound) (inv_nonneg.mpr hm.le)
    _ = B := by rw [mul_comm B, ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalNeighborhood
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-independent vertical neighborhood control from the actual
function and its vertical derivative. The moment application only needs
this fixed interval Sobolev estimate. -/

noncomputable section
open MeasureTheory Set

namespace LipschitzHilbert

theorem interval_pointwise_square {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b))) {x : ℝ} (hx : x ∈ Icc a b) :
    ‖f x‖^2 ≤ (2/(b-a)) * (∫ t in Icc a b, ‖f t‖^2) +
      2*(b-a)*(∫ t in Icc a b, ‖deriv f t‖^2) := by
  have hm : 0 < b-a := sub_pos.mpr hab
  have hcont : ContinuousOn f (Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hi : IntegrableOn (fun t => ‖f t‖^2) (Icc a b) volume :=
    (hcont.norm.pow 2).integrableOn_Icc
  let D := (b-a) * ∫ t in Icc a b, ‖deriv f t‖^2
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) : ‖f x‖^2 ≤ 2*‖f t‖^2+2*D := by
    have hp := interval_pair_energy f hab.le hf hd hx ht
    have hn : ‖f x‖ ≤ ‖f t‖ + ‖f x-f t‖ := by
      simpa only [add_sub_cancel] using norm_add_le (f t) (f x-f t)
    have hs := pow_le_pow_left₀ (norm_nonneg (f x)) hn 2
    dsimp [D]
    nlinarith [sq_nonneg (‖f t‖-‖f x-f t‖)]
  have hint := integral_mono_ae
    (integrable_const (‖f x‖^2) : Integrable (fun _ : ℝ => ‖f x‖^2) (volume.restrict (Icc a b)))
    ((hi.const_mul 2).add (integrable_const (2*D)))
    ((ae_restrict_mem measurableSet_Icc).mono (fun t ht => hpoint t ht))
  have hmass : (volume.restrict (Icc a b)).real univ = b-a := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal hm.le]
  dsimp only [Pi.add_apply] at hint
  rw [integral_add (hi.const_mul 2) (integrable_const (2*D)), integral_const_mul,
    integral_const, integral_const, hmass] at hint
  simp only [smul_eq_mul] at hint
  have heq : (2/(b-a)) * (∫ t in Icc a b, ‖f t‖^2) * (b-a) =
      2 * ∫ t in Icc a b, ‖f t‖^2 := by field_simp [hm.ne']
  dsimp [D] at hint
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AveragedSquareMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Even moments of the vertical Sobolev majorant. The constants are
independent of the number of packet sums and of their Hilbert dimension. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem average_natPow_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [NeZero μ] (f : Ω → ℝ) (n : ℕ)
    (hf : Integrable f μ) (hfn : Integrable (fun t => f t ^ n) μ)
    (hf0 : ∀ᵐ t ∂μ, 0 ≤ f t) :
    (⨍ t, f t ∂μ)^n ≤ ⨍ t, f t^n ∂μ := by
  exact (convexOn_pow n).map_average_le (continuous_id.pow n).continuousOn
    isClosed_Ici hf0 hf hfn

theorem averaged_square_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [NeZero μ] (V D : Ω → ℝ) (n : ℕ)
    (hV : Integrable (fun t => V t^2) μ) (hD : Integrable (fun t => D t^2) μ)
    (hn : Integrable (fun t => (V t^2 + D t^2)^n) μ)
    (hVn : Integrable (fun t => V t^(2*n)) μ)
    (hDn : Integrable (fun t => D t^(2*n)) μ) :
    (2 * ⨍ t, V t^2 + D t^2 ∂μ)^n ≤
      4^n * ⨍ t, V t^(2*n) + D t^(2*n) ∂μ := by
  have hj := average_natPow_le μ (fun t => V t^2 + D t^2) n (hV.add hD) hn
    (Filter.Eventually.of_forall fun t => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hp (t : Ω) : (V t^2 + D t^2)^n ≤
      2^n * (V t^(2*n) + D t^(2*n)) := by
    calc
      _ ≤ 2^(n-1) * ((V t^2)^n + (D t^2)^n) := add_pow_le (sq_nonneg _) (sq_nonneg _) n
      _ ≤ 2^n * ((V t^2)^n + (D t^2)^n) := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)) (by positivity)
      _ = _ := by simp only [pow_mul]
  have ha := integral_mono_ae hn ((hVn.add hDn).const_mul (2^n))
    (Filter.Eventually.of_forall hp)
  dsimp only [Pi.add_apply] at ha
  rw [integral_const_mul] at ha
  have hav : (⨍ t, (V t^2 + D t^2)^n ∂μ) ≤
      2^n * ⨍ t, V t^(2*n) + D t^(2*n) ∂μ := by
    simp only [average_eq, smul_eq_mul]
    calc
      _ ≤ (μ.real univ)⁻¹ * (2^n * ∫ t, V t^(2*n) + D t^(2*n) ∂μ) :=
        mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr measureReal_nonneg)
      _ = _ := by ring
  calc
    _ = 2^n * (⨍ t, V t^2 + D t^2 ∂μ)^n := mul_pow _ _ _
    _ ≤ 2^n * (2^n * ⨍ t, V t^(2*n) + D t^(2*n) ∂μ) := by
      exact mul_le_mul_of_nonneg_left (hj.trans hav) (by positivity)
    _ = _ := by rw [← mul_assoc, ← mul_pow]; norm_num

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_CoordinateFourierSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplication by the line coordinate preserves Fourier support for
Schwartz functions. This is the first step in polynomial localization of
the annular packet variation estimate. -/

noncomputable section

open MeasureTheory Function FourierTransform
open scoped FourierTransform

namespace LipschitzHilbert

theorem coordinateProduct_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    coordinateProduct f x = (x : ℂ) * f x := by
  simpa only [coordinateProduct, smul_eq_mul] using
    SchwartzMap.smulLeftCLM_apply_apply Function.Complex.hasTemperateGrowth_ofReal f x

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PolynomialLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive polynomial weights used to localize annular packets on a
reference line. Their construction and Fourier support preservation are
proved here for the actual Schwartz functions. -/

noncomputable section

open Function FourierTransform
open scoped FourierTransform

namespace LipschitzHilbert

theorem centeredCoordinateProduct_apply (a : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    centeredCoordinateProduct a f x = ((x - a : ℝ) : ℂ) * f x := by
  simp only [centeredCoordinateProduct, add_apply, smul_apply, coordinateProduct_apply,
    smul_eq_mul, Complex.ofReal_sub]
  ring

theorem quadraticLocalization_apply (a r : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    quadraticLocalization a r f x = ((1 + (x - a) ^ 2 / r ^ 2 : ℝ) : ℂ) * f x := by
  simp only [quadraticLocalization, add_apply, smul_apply, smul_eq_mul,
    centeredCoordinateProduct_apply, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_inv]
  ring

theorem polynomialLocalization_apply (a r : ℝ) (q : ℕ)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    polynomialLocalization a r q f x = (polynomialWeight a r q x : ℂ) * f x := by
  induction q with
  | zero => simp [polynomialLocalization, polynomialWeight]
  | succ q ih =>
    rw [polynomialLocalization, quadraticLocalization_apply, ih]
    simp only [polynomialWeight, pow_succ, Complex.ofReal_mul]
    ring

theorem polynomialWeight_one_le (a r : ℝ) (q : ℕ) (x : ℝ) :
    1 ≤ polynomialWeight a r q x := by
  have hbase : 1 ≤ 1 + (x - a) ^ 2 / r ^ 2 := by
    have h := div_nonneg (sq_nonneg (x - a)) (sq_nonneg r)
    linarith
  exact one_le_pow₀ hbase

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_FiniteLineGrid
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite line partitions, nested at an integer branching ratio. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert

namespace FiniteLineGrid

attribute [local instance] Classical.propDecidable

/-- Two points of one finer cell differ by at most its mesh width. -/
theorem same_index_distance (g : FiniteLineGrid) {level : ℕ} (hlevel : level ≤ g.depth)
    {x y : ℝ} (hx : x ∈ g.root) (hy : y ∈ g.root)
    (hxy : g.index level x = g.index level y) :
    |x - y| ≤ g.width / (g.branching : ℝ) ^ level := by
  have hG : 0 < (g.branching : ℝ) := by exact_mod_cast g.branching_pos
  have hp : 0 < (g.branching : ℝ) ^ level := pow_pos hG _
  have hxn : 0 ≤ ((x - g.origin) / g.width) * (g.branching : ℝ) ^ level :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hx.1) g.width_pos.le) hp.le
  have hyn : 0 ≤ ((y - g.origin) / g.width) * (g.branching : ℝ) ^ level :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hy.1) g.width_pos.le) hp.le
  have hf : ⌊((x - g.origin) / g.width) * (g.branching : ℝ) ^ level⌋₊ =
      ⌊((y - g.origin) / g.width) * (g.branching : ℝ) ^ level⌋₊ := by
    have h := congrArg Fin.val hxy
    simpa only [index, Nat.min_eq_left hlevel, rawIndex, ite_eq_left hx, ite_eq_left hy] using h
  have hxlo := Nat.floor_le hxn
  have hylo := Nat.floor_le hyn
  have hxhi := Nat.lt_floor_add_one (((x - g.origin) / g.width) * (g.branching : ℝ) ^ level)
  have hyhi := Nat.lt_floor_add_one (((y - g.origin) / g.width) * (g.branching : ℝ) ^ level)
  rw [hf] at hxlo hxhi
  have hnorm : |((x - g.origin) / g.width) * (g.branching : ℝ) ^ level -
      ((y - g.origin) / g.width) * (g.branching : ℝ) ^ level| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have heq : ((x - g.origin) / g.width) * (g.branching : ℝ) ^ level -
      ((y - g.origin) / g.width) * (g.branching : ℝ) ^ level =
      (x - y) * ((g.branching : ℝ) ^ level / g.width) := by ring
  rw [heq, abs_mul, abs_of_pos (div_pos hp g.width_pos)] at hnorm
  apply (le_div_iff₀ hp).mpr
  have h := mul_le_mul_of_nonneg_right hnorm g.width_pos.le
  calc
    |x - y| * (g.branching : ℝ) ^ level =
        (|x - y| * ((g.branching : ℝ) ^ level / g.width)) * g.width := by
          field_simp [g.width_pos.ne']
    _ ≤ 1 * g.width := h
    _ = g.width := one_mul _

end FiniteLineGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteLineCells
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact intervals underlying the finite line-mesh index maps. -/

noncomputable section

open Set

namespace LipschitzHilbert.FiniteLineGrid

theorem index_eq_iff_mem_cell (g : FiniteLineGrid) {level : ℕ}
    (hl : level ≤ g.depth) {x : ℝ} (hx : x ∈ g.root) (i : ℕ) :
    (g.index level x).val = i ↔ x ∈ g.cell level i := by
  have hG : (0 : ℝ) < g.branching := by exact_mod_cast g.branching_pos
  have hrep : (x - g.origin) / g.width * (g.branching : ℝ) ^ level =
      (x - g.origin) / g.meshWidth level := by
    unfold meshWidth
    field_simp
  have hn : 0 ≤ (x - g.origin) / g.meshWidth level :=
    div_nonneg (sub_nonneg.mpr hx.1) (g.meshWidth_pos level).le
  simp only [index, rawIndex, Nat.min_eq_left hl, ite_eq_left hx, hrep]
  rw [Nat.floor_eq_iff hn]
  change (i : ℝ) ≤ (x - g.origin) / g.meshWidth level ∧
      (x - g.origin) / g.meshWidth level < i + 1 ↔
    g.origin + g.meshWidth level * i ≤ x ∧ x < g.origin + g.meshWidth level * (i + 1)
  rw [le_div_iff₀ (g.meshWidth_pos level), div_lt_iff₀ (g.meshWidth_pos level)]
  constructor <;> rintro ⟨hleft, hright⟩ <;> constructor <;> nlinarith

theorem cell_subset_root (g : FiniteLineGrid) (level : ℕ) {i : ℕ}
    (hi : i < g.branching ^ level) : g.cell level i ⊆ g.root := by
  have hwidth := g.meshWidth_pos level
  have hG : (0 : ℝ) < g.branching := by exact_mod_cast g.branching_pos
  have hupper : (i : ℝ) + 1 ≤ (g.branching : ℝ) ^ level := by
    exact_mod_cast (show i + 1 ≤ g.branching ^ level by omega)
  have hmul := mul_le_mul_of_nonneg_left hupper hwidth.le
  have hrestore : g.meshWidth level * (g.branching : ℝ) ^ level = g.width := by
    exact div_mul_cancel₀ _ (pow_pos hG _).ne'
  rw [hrestore] at hmul
  intro x hx
  change g.origin + g.meshWidth level * i ≤ x ∧
    x < g.origin + g.meshWidth level * (i + 1) at hx
  change g.origin ≤ x ∧ x < g.origin + g.width
  have hzero : 0 ≤ g.meshWidth level * i := mul_nonneg hwidth.le (Nat.cast_nonneg _)
  constructor <;> linarith [hx.1, hx.2]

/-- Restricting the coarse-index fiber to the root gives exactly its
half-open mesh interval. -/
theorem index_fiber_inter_root (g : FiniteLineGrid) {level : ℕ}
    (hl : level ≤ g.depth) {i : ℕ} (hi : i < g.branching ^ level) :
    {x ∈ g.root | (g.index level x).val = i} = g.cell level i := by
  ext x
  constructor
  · intro hx
    exact (g.index_eq_iff_mem_cell hl hx.1 i).mp hx.2
  · intro hx
    have hr := g.cell_subset_root level hi hx
    exact ⟨hr, (g.index_eq_iff_mem_cell hl hr i).mpr hx⟩

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridMartingale
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The martingale of actual nested line-cell averages. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.FiniteLineGrid

theorem average_martingale (g : FiniteLineGrid) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) : Martingale (g.average μ f) g.filtration μ :=
  martingale_condExp f g.filtration μ

theorem average_constant (g : FiniteLineGrid) (μ : Measure ℝ) (f : ℝ → ℝ)
    (n : ℕ) {x y : ℝ} (hxy : g.index n x = g.index n y) :
    g.average μ f n x = g.average μ f n y := by
  exact (show StronglyMeasurable[g.filtration n] (g.average μ f n) from
    stronglyMeasurable_condExp).factorsThrough hxy

/-- Conditional expectation is the actual integral average on every
positive-measure index fiber, pointwise for its canonical representative. -/
theorem average_eq_fiber_mean (g : FiniteLineGrid) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Integrable f μ) (n : ℕ) (x : ℝ)
    (hpos : μ.real {y | g.index n y = g.index n x} ≠ 0) :
    g.average μ f n x =
      (∫ y in {y | g.index n y = g.index n x}, f y ∂μ) /
        μ.real {y | g.index n y = g.index n x} := by
  let s := {y | g.index n y = g.index n x}
  have hs : MeasurableSet[g.filtration n] s :=
    (comap_measurable (g.index n)) (measurableSet_singleton _)
  have hsambient : MeasurableSet s := (g.filtration.le n) _ hs
  apply (eq_div_iff hpos).mpr
  calc
    g.average μ f n x * μ.real s = ∫ y in s, g.average μ f n x ∂μ := by
      rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ = ∫ y in s, g.average μ f n y ∂μ := by
      apply setIntegral_congr_fun hsambient
      intro y hy
      exact g.average_constant μ f n hy.symm
    _ = ∫ y in s, f y ∂μ := setIntegral_condExp (g.filtration.le n) hf hs

theorem lineMeasure_fiber (g : FiniteLineGrid) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level) :
    g.lineMeasure {x | (g.index level x).val = i} = ENNReal.ofReal (g.meshWidth level) := by
  rw [lineMeasure, Measure.restrict_apply]
  · have heq : {x | (g.index level x).val = i} ∩ g.root = g.cell level i := by
      rw [inter_comm]
      exact g.index_fiber_inter_root hl hi
    rw [heq, cell, Real.volume_Ico]
    congr 1
    ring
  · exact ((measurable_of_countable (fun j : Fin (g.branching ^ g.depth) => j.val)).comp
      (g.measurable_index level)) (measurableSet_singleton i)

/-- On a nonempty mesh interval, the canonical dyadic conditional
expectation is exactly the usual Lebesgue average over that interval. -/
theorem average_eq_cell_mean (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level)
    {x : ℝ} (hx : x ∈ g.cell level i) :
    g.average g.lineMeasure f level x =
      (∫ y in g.cell level i, f y) / g.meshWidth level := by
  have hix : (g.index level x).val = i :=
    (g.index_eq_iff_mem_cell hl (g.cell_subset_root level hi hx) i).mpr hx
  have hfiber : {y | g.index level y = g.index level x} =
      {y | (g.index level y).val = i} := by
    ext y
    simp only [Fin.ext_iff, hix, Set.mem_ofPred_eq]
  have hmass : g.lineMeasure.real {y | g.index level y = g.index level x} =
      g.meshWidth level := by
    rw [measureReal_def, hfiber, g.lineMeasure_fiber hl hi,
      ENNReal.toReal_ofReal (g.meshWidth_pos level).le]
  rw [g.average_eq_fiber_mean g.lineMeasure f hf level x
    (by rw [hmass]; exact (g.meshWidth_pos level).ne'), hmass]
  congr 1
  rw [lineMeasure, Measure.restrict_restrict (g.measurable_index_fiber level _)]
  congr 1
  rw [hfiber, inter_comm]
  congr 1
  exact g.index_fiber_inter_root hl hi

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridPoincare
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low-frequency averaging errors on the actual nested line grid. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.FiniteLineGrid

theorem index_lt_level (g : FiniteLineGrid) {level : ℕ} (hl : level ≤ g.depth) (x : ℝ) :
    (g.index level x).val < g.branching ^ level := by
  let h : FiniteLineGrid := { g with depth := level }
  have ht := h.rawIndex_lt (le_refl level) x
  change g.rawIndex level x < g.branching ^ level at ht
  simpa only [index, Nat.min_eq_left hl] using ht

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BoxPolynomialWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial localization lower bound on a reference interval, with
the horizontal box offset retained explicitly. -/

noncomputable section
open Set

namespace LipschitzHilbert

theorem box_polynomial_base (u r k x : ℝ) (hr : 0 < r) (hx : |x - u| ≤ r) :
    (1 + |k|) ^ 2 / 8 ≤ 1 + (x - (u + r * k)) ^ 2 / r ^ 2 := by
  let v := (x - (u + r * k)) / r
  have hunit : |(x - u) / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]
    exact hx
  have heq : k = (x - u) / r - v := by
    dsimp [v]
    field_simp
    ring
  have hk : |k| ≤ 1 + |v| := by
    rw [heq]
    exact (abs_sub _ _).trans (add_le_add hunit le_rfl)
  have hk2 := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |k|)
    (add_le_add (le_rfl : (1 : ℝ) ≤ 1) hk) 2
  have habs : |v| ^ 2 = v ^ 2 := sq_abs v
  have hs := sq_nonneg (|v| - 2)
  have hv : 1 + (x - (u + r * k)) ^ 2 / r ^ 2 = 1 + v ^ 2 := by
    dsimp [v]
    rw [div_pow]
  rw [hv]
  nlinarith

theorem box_polynomial_weight (u r k x : ℝ) (q : ℕ)
    (hr : 0 < r) (hx : |x - u| ≤ r) :
    ((1 + |k|) ^ 2 / 8) ^ q ≤ polynomialWeight (u + r * k) r q x := by
  exact pow_le_pow_left₀ (by positivity) (box_polynomial_base u r k x hr hx) q

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PolynomialEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial growth about a box is absorbed by a slower packet envelope.
The integrated envelope has the packet length as its only scale factor. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

theorem polynomial_base_le (x s a l r : ℝ) (hl : 0 < l) (hr : 0 < r)
    (hlr : l ≤ r) (hsa : |s - a| ≤ r) :
    1 + (x - a) ^ 2 / r ^ 2 ≤ 4 * (1 + ((x - s) / l) ^ 2) := by
  have hu : |(x - s) / r| ≤ |(x - s) / l| := by
    rw [abs_div, abs_div, abs_of_pos hr, abs_of_pos hl]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hl hlr
  have hv : |(s - a) / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]
    exact hsa
  have hu2 := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hu
  have hv2 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr hv
  simp only [sq_abs, one_pow] at hu2 hv2
  have heq : (x - a) / r = (x - s) / r + (s - a) / r := by ring
  rw [← div_pow, heq]
  nlinarith [sq_nonneg ((x - s) / r - (s - a) / r), sq_nonneg ((x - s) / l)]

theorem polynomialWeight_sq_mul_envelope (x s a l r : ℝ) (q n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r) (hsa : |s - a| ≤ r) :
    polynomialWeight a r q x ^ 2 * lineEnvelope s l (n + 2 * q) x ≤
      16 ^ q * lineEnvelope s l n x := by
  let B := 1 + ((x - s) / l) ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hbase := polynomial_base_le x s a l r hl hr hlr hsa
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + (x - a) ^ 2 / r ^ 2)
    hbase (2 * q)
  have hweight : polynomialWeight a r q x ^ 2 = (1 + (x - a) ^ 2 / r ^ 2) ^ (2 * q) := by
    simp only [polynomialWeight, ← pow_mul, Nat.mul_comm q 2]
  rw [hweight]
  calc
    _ ≤ (4 * B) ^ (2 * q) * (B ^ (n + 2 * q))⁻¹ :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = 16 ^ q * lineEnvelope s l n x := by
      change (4 * B) ^ (2 * q) * (B ^ (n + 2 * q))⁻¹ = 16 ^ q * (B ^ n)⁻¹
      rw [mul_pow, pow_add, mul_inv_rev, ← mul_assoc]
      have hz : B ^ (2 * q) ≠ 0 := pow_ne_zero _ hB.ne'
      have hc : (4 : ℝ) ^ (2 * q) = 16 ^ q := by rw [pow_mul]; norm_num
      rw [mul_assoc ((4 : ℝ) ^ (2 * q)), mul_inv_cancel₀ hz, mul_one, hc]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineTiling
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably many actual finite line meshes cover a reference line. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert

theorem tiledLineGrid_root (origin H : ℝ) (hH : 0 < H) (G N : ℕ) (hG : 0 < G)
    (k : ℤ) :
    (tiledLineGrid origin H hH G N hG k).root =
      Ico (origin + k * H) (origin + (k + 1 : ℤ) * H) := by
  unfold FiniteLineGrid.root tiledLineGrid
  congr 1
  push_cast
  ring

theorem tiledLineGrid_pairwise_disjoint (origin H : ℝ) (hH : 0 < H) (G N : ℕ)
    (hG : 0 < G) :
    Pairwise fun i j => Disjoint (tiledLineGrid origin H hH G N hG i).root
      (tiledLineGrid origin H hH G N hG j).root := by
  intro i j hij
  simp only [tiledLineGrid_root]
  apply Set.disjoint_left.mpr
  intro x hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
    push_cast at hi hj
    have hm := mul_le_mul_of_nonneg_right hc hH.le
    linarith [hi.2, hj.1]
  · have hc : (j : ℝ) + 1 ≤ i := by exact_mod_cast (show j + 1 ≤ i by omega)
    push_cast at hi hj
    have hm := mul_le_mul_of_nonneg_right hc hH.le
    linarith [hj.2, hi.1]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineLatticeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform finite lattice overlap bound from the actual line integral of
the rational envelope. No cardinality factor or implicit lattice assumption
is used. -/

noncomputable section

open Set MeasureTheory Function
open scoped BigOperators

namespace LipschitzHilbert

theorem lineEnvelope_cell_comparison (x k y : ℝ) (hy : y ∈ Ico k (k + 1)) :
    lineEnvelope x 1 1 k ≤ 4 * lineEnvelope x 1 1 y := by
  have hdelta : (y - k) ^ 2 ≤ 1 := by
    have ha : |y - k| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr ha
    simpa only [sq_abs, one_pow] using hs
  have hb : 1 + (y - x) ^ 2 ≤ 4 * (1 + (k - x) ^ 2) := by
    nlinarith [sq_nonneg ((k - x) - (y - k)), sq_nonneg (k - x)]
  simp only [lineEnvelope, div_one, pow_one]
  rw [← one_div, ← div_eq_mul_inv]
  exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hb)

theorem lineEnvelope_le_cell_integral (x k : ℝ) :
    lineEnvelope x 1 1 k ≤ 4 * ∫ y in Ico k (k + 1), lineEnvelope x 1 1 y := by
  have hint : IntegrableOn (lineEnvelope x 1 1) (Ico k (k + 1)) :=
    (integrable_lineEnvelope_one x 1 (by norm_num)).integrableOn
  have hfinite : volume (Ico k (k + 1)) ≠ ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  have h := setIntegral_mono_on (integrableOn_const hfinite : IntegrableOn
      (fun _ : ℝ => lineEnvelope x 1 1 k) (Ico k (k + 1)) volume)
    (hint.const_mul 4) measurableSet_Ico (fun y hy => lineEnvelope_cell_comparison x k y hy)
  rw [integral_const_mul] at h
  simpa [setIntegral_const, Real.volume_Ico, measureReal_def] using h

theorem finite_line_lattice_overlap (x : ℝ) (s : Finset ℤ) :
    (∑ k ∈ s, lineEnvelope x 1 1 k) ≤ 4 * Real.pi := by
  classical
  have hint := integrable_lineEnvelope_one x 1 (by norm_num)
  have hd : (s : Set ℤ).Pairwise (Disjoint on fun k : ℤ => Ico (k : ℝ) (k + 1)) := by
    intro i _ j _ hij
    have h := tiledLineGrid_pairwise_disjoint 0 1 (by norm_num) 2 0 (by norm_num) hij
    simpa only [tiledLineGrid_root, Int.cast_add, Int.cast_one, mul_one, zero_add] using h
  have hsum := integral_biUnion_finset s (fun _ _ => measurableSet_Ico) hd
    (fun _ _ => hint.integrableOn)
  calc
    _ ≤ ∑ k ∈ s, 4 * ∫ y in Ico (k : ℝ) (k + 1), lineEnvelope x 1 1 y :=
      Finset.sum_le_sum (fun k _ => lineEnvelope_le_cell_integral x k)
    _ = 4 * ∫ y in ⋃ k ∈ s, Ico (k : ℝ) (k + 1), lineEnvelope x 1 1 y := by
      rw [← Finset.mul_sum, hsum]
    _ ≤ 4 * ∫ y, lineEnvelope x 1 1 y := by
      exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hint
        (Filter.Eventually.of_forall (lineEnvelope_nonneg x 1 1))) (by norm_num)
    _ = 4 * Real.pi := by rw [integral_lineEnvelope_one x 1 (by norm_num), mul_one]

theorem lineEnvelope_lattice_rescale (a l x : ℝ) (hl : l ≠ 0) (k : ℤ) (n : ℕ) :
    lineEnvelope (a + l * k) l n x = lineEnvelope ((x - a) / l) 1 n k := by
  unfold lineEnvelope
  congr 3
  simp only [div_one]
  have h : (x - (a + l * k)) / l = -((k : ℝ) - (x - a) / l) := by
    field_simp
    ring
  rw [h, neg_sq]

theorem finite_plane_lattice_overlap (x y : ℝ) (s : Finset (ℤ × ℤ)) :
    (∑ p ∈ s, lineEnvelope x 1 1 p.1 * lineEnvelope y 1 1 p.2) ≤
      (4 * Real.pi) ^ 2 := by
  classical
  have hsub : s ⊆ (s.image Prod.fst) ×ˢ (s.image Prod.snd) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,
      Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩
  calc
    _ ≤ ∑ p ∈ (s.image Prod.fst) ×ˢ (s.image Prod.snd),
        lineEnvelope x 1 1 p.1 * lineEnvelope y 1 1 p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
        mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
    _ = (∑ i ∈ s.image Prod.fst, lineEnvelope x 1 1 i) *
        ∑ j ∈ s.image Prod.snd, lineEnvelope y 1 1 j := by
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ ≤ (4 * Real.pi) * (4 * Real.pi) :=
      mul_le_mul (finite_line_lattice_overlap x _) (finite_line_lattice_overlap y _)
        (Finset.sum_nonneg (fun j _ => lineEnvelope_nonneg _ _ _ _)) (by positivity)
    _ = _ := (pow_two _).symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TileLatticeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform overlap for actual rectangular tile-center lattices, allowing
arbitrary horizontal and vertical scales and finite subfamilies. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem finite_scaled_plane_lattice_overlap (a b l W x y : ℝ)
    (hl : l ≠ 0) (hW : W ≠ 0) (s : Finset (ℤ × ℤ)) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (∑ p ∈ s, lineEnvelope (a + l * p.1) l m x *
      lineEnvelope (b + W * p.2) W n y) ≤ (4 * Real.pi) ^ 2 := by
  calc
    _ ≤ ∑ p ∈ s, lineEnvelope ((x - a) / l) 1 1 p.1 *
        lineEnvelope ((y - b) / W) 1 1 p.2 := by
      apply Finset.sum_le_sum
      intro p _
      rw [lineEnvelope_lattice_rescale a l x hl p.1 m,
        lineEnvelope_lattice_rescale b W y hW p.2 n]
      exact mul_le_mul (lineEnvelope_antitone _ _ _ hm) (lineEnvelope_antitone _ _ _ hn)
        (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
    _ ≤ _ := finite_plane_lattice_overlap _ _ s

theorem injective_tile_lattice_overlap {ι : Type*} [Fintype ι]
    (index : ι → ℤ × ℤ) (hinj : Function.Injective index)
    (a b l W x y : ℝ) (hl : l ≠ 0) (hW : W ≠ 0)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (∑ i, lineEnvelope (a + l * (index i).1) l m x *
      lineEnvelope (b + W * (index i).2) W n y) ≤ (4 * Real.pi) ^ 2 := by
  classical
  have h := finite_scaled_plane_lattice_overlap a b l W x y hl hW
    (Finset.univ.image index) hm hn
  rw [Finset.sum_image (fun _ _ _ _ heq => hinj heq)] at h
  exact h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_TransverseBoxDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transverse decay of the reference-line envelope for centers in an
actual offset box. -/

noncomputable section

namespace LipschitzHilbert

theorem box_decay_le_line_envelope (b : ℝ) :
    (((1 + |b|) ^ 2 / 8) ^ 2)⁻¹ ≤ 64 * lineEnvelope 0 1 1 b ^ 2 := by
  have hbase : 1 + b ^ 2 ≤ (1 + |b|) ^ 2 := by nlinarith [abs_nonneg b, sq_abs b]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + b ^ 2) hbase 2
  have hinv := inv_anti₀ (by positivity : 0 < (1 + b ^ 2) ^ 2) hp
  have heq : (((1 + |b|) ^ 2 / 8) ^ 2)⁻¹ = 64 * (((1 + |b|) ^ 2) ^ 2)⁻¹ := by
    rw [div_pow, inv_div]
    norm_num
    ring
  rw [heq]
  have h := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 64)
  simpa only [lineEnvelope, sub_zero, div_one, pow_one, inv_pow] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BoxVariationWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable weights for the fixed-box variation estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem boxVariationWeight_pos (p : ℤ × ℤ) : 0 < boxVariationWeight p := by
  unfold boxVariationWeight lineEnvelope
  positivity

theorem boxVariationWeight_sum {ι : Type*} [Fintype ι]
    (index : ι → ℤ × ℤ) (hinj : Function.Injective index) :
    (∑ i, boxVariationWeight (index i)) ≤ (4 * Real.pi) ^ 2 := by
  have h := injective_tile_lattice_overlap index hinj 0 0 1 1 0 0 (by norm_num)
    (by norm_num) (by norm_num : 1 ≤ (1 : ℕ)) (by norm_num : 1 ≤ (1 : ℕ))
  have heq (k : ℤ) : lineEnvelope (0 + 1 * k) 1 1 0 = lineEnvelope 0 1 1 k := by
    simp [lineEnvelope]
  simpa only [heq, boxVariationWeight] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TailLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict tail bounds pass to almost-everywhere limits. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LipschitzHilbert

theorem strict_tail_bound_of_ae_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : ℕ → X → ℝ) (g : X → ℝ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (t C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, μ.real {x | t < f n x} ≤ C) :
    μ.real {x | t < g x} ≤ C := by
  let S := fun m : ℕ => {x | ∀ n ≥ m, t < f n x}
  have hmono : Monotone S := by
    intro m n hmn x hx i hi
    exact hx i (hmn.trans hi)
  have hsub : ∀ᵐ x ∂μ, x ∈ {x | t < g x} → x ∈ ⋃ m, S m := by
    filter_upwards [hlim] with x hx ht
    have h := (tendsto_order.mp hx).1 t ht
    obtain ⟨m,hm⟩ := eventually_atTop.mp h
    exact mem_iUnion.mpr ⟨m,hm⟩
  have hmass : μ {x | t < g x} ≤ ENNReal.ofReal C := by
    calc
      _ ≤ μ (⋃ m, S m) := measure_mono_ae hsub
      _ = ⨆ m, μ (S m) := hmono.directed_le.measure_iUnion
      _ ≤ ENNReal.ofReal C := by
        apply iSup_le
        intro m
        have hle := ENNReal.ofReal_le_ofReal (hbound m)
        rw [ofReal_measureReal] at hle
        exact (measure_mono (show S m ⊆ {x | t < f m x} from fun _ hx => hx m le_rfl)).trans hle
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  simpa only [measureReal_def, ENNReal.toReal_ofReal hC] using hreal

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FirstExceed
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint first-crossing events for a finite scalar process. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem firstExceed_disjoint {X : Type*} (U : ℕ → X → ℝ) (lambda : ℝ) :
    Pairwise (fun i j => Disjoint (firstExceed U lambda i) (firstExceed U lambda j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (not_lt_of_ge (hxj.2 i h)) hxi.1
  · exact (not_lt_of_ge (hxi.2 j h)) hxj.1

theorem firstExceed_union {X : Type*} (U : ℕ → X → ℝ) (lambda : ℝ) (N : ℕ) :
    (⋃ i : Fin (N + 1), firstExceed U lambda i.val) = finiteMaxEvent U lambda N := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨i, by omega, hi.1⟩
  · rintro ⟨i, hi, hUi⟩
    have hex : ∃ n, lambda < U n x := ⟨i,hUi⟩
    let n := Nat.find hex
    have hn : n ≤ i := Nat.find_min' hex hUi
    apply mem_iUnion.mpr
    refine ⟨⟨n,by omega⟩, Nat.find_spec hex, ?_⟩
    intro j hj
    exact le_of_not_gt (Nat.find_min hex hj)

theorem measurableSet_firstExceed {X : Type*} [MeasurableSpace X]
    (U : ℕ → X → ℝ) (lambda : ℝ) (n : ℕ) (hU : ∀ i ≤ n, Measurable (U i)) :
    MeasurableSet (firstExceed U lambda n) := by
  unfold firstExceed
  simp only [ofPred_and, ofPred_forall]
  exact (measurableSet_lt measurable_const (hU n le_rfl)).inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi =>
      measurableSet_le (hU i hi.le) measurable_const)

theorem firstExceed_measure_sum {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (U : ℕ → X → ℝ) (lambda : ℝ) (N : ℕ)
    (hU : ∀ i ≤ N, Measurable (U i)) :
    (∑ i : Fin (N + 1), μ.real (firstExceed U lambda i.val)) =
      μ.real (finiteMaxEvent U lambda N) := by
  rw [← firstExceed_union]
  symm
  apply measureReal_iUnion_fintype
  · intro i j hij
    exact firstExceed_disjoint U lambda (fun h => hij (Fin.ext h))
  · intro i
    exact measurableSet_firstExceed U lambda i (fun j hj => hU j (by omega))
  · intro i
    exact measure_ne_top μ _

theorem firstExceed_norm_overshoot {X E : Type*} [NormedAddCommGroup E]
    (F : ℕ → X → E) (x : X) {lambda D : ℝ} (hlambda : 0 ≤ lambda)
    (n : ℕ) (hjump : ∀ i < n, ‖F (i + 1) x - F i x‖ ≤ D)
    (hx : x ∈ firstExceed (fun i y => ‖F i y - F 0 y‖) lambda n) :
    ‖F n x - F 0 x‖ ≤ lambda + D := by
  have hn : n ≠ 0 := by
    intro hn
    have hh := hx.1
    simp only [hn, sub_self, norm_zero] at hh
    linarith
  have hp := hx.2 (n - 1) (by omega)
  have hj := hjump (n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega] at hj
  exact (norm_sub_le_norm_sub_add_norm_sub (F n x) (F (n - 1) x) (F 0 x)).trans
    (by linarith)

theorem firstExceed_large_subset {X E : Type*} [NormedAddCommGroup E]
    (F : ℕ → X → E) (N n : ℕ) (hn : n ≤ N) {lambda D δ : ℝ}
    (hlambda : 0 ≤ lambda) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hjump : ∀ i < N, ∀ x, ‖F (i + 1) x - F i x‖ ≤ D) :
    finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) (lambda + D + δ) N ∩
        firstExceed (fun i x => ‖F i x - F 0 x‖) lambda n ⊆
      {x | ∃ i ≤ N - n, δ ≤ ‖F (n + i) x - F n x‖} ∩
        firstExceed (fun i x => ‖F i x - F 0 x‖) lambda n := by
  rintro x ⟨⟨k,hk,hlarge⟩,hx⟩
  refine ⟨?_,hx⟩
  have hkn : n ≤ k := by
    by_contra h
    have hb := hx.2 k (lt_of_not_ge h)
    linarith
  have hstop := firstExceed_norm_overshoot F x hlambda n
    (fun i hi => hjump i (hi.trans_le hn) x) hx
  refine ⟨k - n, by omega, ?_⟩
  rw [show n + (k - n) = k by omega]
  have htri := norm_sub_le_norm_sub_add_norm_sub (F k x) (F n x) (F 0 x)
  linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MartingaleLocalMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction and time shift for a martingale, and the local weak-L1
maximal estimate used in the dyadic John--Nirenberg stopping argument. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LipschitzHilbert

variable {X : Type*} {m : MeasurableSpace X} {μ : Measure X}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ m} {F : ℕ → X → ℝ}

omit [IsFiniteMeasure μ] in
theorem martingale_timeShift (hF : Martingale F ℱ μ) (n : ℕ) :
    Martingale (fun i => F (n + i)) (timeShiftFiltration ℱ n) μ :=
  ⟨fun i => hF.stronglyMeasurable (n + i),
    fun _i _j hij => hF.condExp_ae_eq (Nat.add_le_add_left hij n)⟩

theorem martingale_restrict_initial (hF : Martingale F ℱ μ)
    {s : Set X} (hs : MeasurableSet[ℱ 0] s) : Martingale F ℱ (μ.restrict s) := by
  apply martingale_of_setIntegral_eq_succ hF.stronglyAdapted
    (fun i => (hF.integrable i).integrableOn)
  intro i t ht
  rw [Measure.restrict_restrict (ℱ.le i t ht)]
  exact hF.setIntegral_eq (Nat.le_succ i) (ht.inter (ℱ.mono (Nat.zero_le i) _ hs))

omit [IsFiniteMeasure μ] in
theorem martingale_abs (hF : Martingale F ℱ μ) :
    Submartingale (fun i x => |F i x|) ℱ μ := by
  have heq : (fun i x => |F i x|) = F ⊔ -F := by
    funext i x
    exact abs_eq_max_neg
  rw [heq]
  exact hF.submartingale.sup hF.neg.submartingale

theorem martingale_maximal_L1 (hF : Martingale F ℱ μ)
    {lambda : ℝ} (hlambda : 0 < lambda) (N : ℕ) :
    μ.real {x | ∃ i ≤ N, lambda ≤ |F i x|} ≤ lambda⁻¹ * ∫ x, |F N x| ∂μ := by
  have hmax := maximal_ineq (martingale_abs hF) (fun i x => abs_nonneg (F i x))
    (ε := ⟨lambda,hlambda.le⟩) N
  change _ * μ {x | lambda ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one (fun i => |F i x|)} ≤
    ENNReal.ofReal (∫ x in {x | lambda ≤ (Finset.range (N + 1)).sup'
      Finset.nonempty_range_add_one (fun i => |F i x|)}, |F N x| ∂μ) at hmax
  have hevent : {x | lambda ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      (fun i => |F i x|)} = {x | ∃ i ≤ N, lambda ≤ |F i x|} := by
    ext x
    simp only [mem_ofPred_eq, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff]
  rw [hevent] at hmax
  have hwhole : (∫ x in {x | ∃ i ≤ N, lambda ≤ |F i x|}, |F N x| ∂μ) ≤
      ∫ x, |F N x| ∂μ := by
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun x => abs_nonneg (F N x)) (hF.integrable N).abs
  have hsetnonneg : 0 ≤ ∫ x in {x | ∃ i ≤ N, lambda ≤ |F i x|}, |F N x| ∂μ :=
    integral_nonneg (fun x => abs_nonneg (F N x))
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmax
  have hreal : lambda * μ.real {x | ∃ i ≤ N, lambda ≤ |F i x|} ≤
      ∫ x in {x | ∃ i ≤ N, lambda ≤ |F i x|}, |F N x| ∂μ := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hsetnonneg] at ht
    exact ht
  have hfinal : μ.real {x | ∃ i ≤ N, lambda ≤ |F i x|} ≤
      (∫ x, |F N x| ∂μ) / lambda := by
    apply (le_div_iff₀ hlambda).mpr
    simpa only [mul_comm] using hreal.trans hwhole
  simpa only [div_eq_mul_inv, mul_comm] using hfinal

theorem martingale_local_maximal_L1 (hF : Martingale F ℱ μ) (n N : ℕ)
    {s : Set X} (hs : MeasurableSet[ℱ n] s) {lambda : ℝ} (hlambda : 0 < lambda) :
    (μ.restrict s).real {x | ∃ i ≤ N, lambda ≤ |F (n + i) x - F n x|} ≤
      lambda⁻¹ * ∫ x in s, |F (n + N) x - F n x| ∂μ := by
  have hshift := martingale_timeShift hF n
  have hconst : Martingale (fun _ => F n) (timeShiftFiltration ℱ n) μ :=
    martingale_const_fun _ _ (by
      change StronglyMeasurable[ℱ n] (F n)
      exact hF.stronglyMeasurable n) (hF.integrable n)
  have hcenter : Martingale (fun i x => F (n + i) x - F n x)
      (timeShiftFiltration ℱ n) μ := hshift.sub hconst
  exact martingale_maximal_L1 (martingale_restrict_initial hcenter
    (by change MeasurableSet[ℱ n] s; exact hs)) hlambda N

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MartingaleGoodLambda
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A first-crossing contraction for a finite martingale with bounded
conditional mean oscillation. This is the finite stopping step in the
John--Nirenberg proof; no exponential-tail theorem is assumed. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {X : Type*} {m : MeasurableSpace X} {μ : Measure X}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ m} {F : ℕ → X → ℝ}

theorem martingale_goodLambda (hF : Martingale F ℱ μ) (N : ℕ)
    {A D lambda : ℝ} (hA : 0 < A) (hD : 0 ≤ D) (hlambda : 0 ≤ lambda)
    (hBMO : TerminalMeanOscillationBound F ℱ μ N A)
    (hjump : ∀ i < N, ∀ x, ‖F (i + 1) x - F i x‖ ≤ D) :
    μ.real (finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) (lambda + D + 2 * A) N) ≤
      (1 / 2 : ℝ) * μ.real (finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) lambda N) := by
  let U := fun i x => ‖F i x - F 0 x‖
  let B := fun n => firstExceed U lambda n
  have hUm (i : ℕ) : Measurable (U i) :=
    ((hF.stronglyMeasurable i).measurable.le (ℱ.le i)).sub
      ((hF.stronglyMeasurable 0).measurable.le (ℱ.le 0)) |>.norm
  have hBm (n : ℕ) : MeasurableSet[ℱ n] (B n) := by
    let : MeasurableSpace X := ℱ n
    apply measurableSet_firstExceed U lambda n
    intro i hi
    exact ((hF.stronglyMeasurable i).mono (ℱ.mono hi)).measurable.sub
      ((hF.stronglyMeasurable 0).mono (ℱ.mono (Nat.zero_le n))).measurable |>.norm
  have hcell (n : Fin (N + 1)) :
      μ.real (finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n) ≤
        (1 / 2 : ℝ) * μ.real (B n) := by
    let S := {x | ∃ i ≤ N - n.val, 2 * A ≤ |F (n.val + i) x - F n x|}
    have hSm : MeasurableSet S := by
      change MeasurableSet {x | ∃ i, i ≤ N - n.val ∧ 2 * A ≤ |F (n.val + i) x - F n x|}
      simp only [ofPred_exists, ofPred_and]
      apply MeasurableSet.iUnion
      intro i
      have hd : Measurable (fun x => F (n.val + i) x - F n x) :=
        ((hF.stronglyMeasurable (n.val + i)).measurable.le (ℱ.le _)).sub
          ((hF.stronglyMeasurable n.val).measurable.le (ℱ.le _))
      simpa only [Real.norm_eq_abs] using
        (MeasurableSet.const (i ≤ N - n.val)).inter
          (measurableSet_le measurable_const hd.norm)
    have hlocal := martingale_local_maximal_L1 hF n.val (N - n.val) (hBm n) (by positivity : 0 < 2 * A)
    have hbudget := hBMO n.val (by omega) (B n) (hBm n)
    have hindex : n.val + (N - n.val) = N := by omega
    rw [hindex] at hlocal
    have hsub : finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n ⊆ S ∩ B n := by
      simpa only [S, U, B, Real.norm_eq_abs] using
        firstExceed_large_subset F N n.val (by omega) hlambda hD
          (by positivity : 0 ≤ 2 * A) hjump
    calc
      _ ≤ μ.real (S ∩ B n) := measureReal_mono hsub
      _ = (μ.restrict (B n)).real S := (measureReal_restrict_apply hSm).symm
      _ ≤ (2 * A)⁻¹ * ∫ x in B n, |F N x - F n x| ∂μ := hlocal
      _ ≤ (2 * A)⁻¹ * (A * μ.real (B n)) :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = _ := by field_simp [hA.ne']
  have hcover : finiteMaxEvent U (lambda + D + 2 * A) N ⊆
      ⋃ n : Fin (N + 1), finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n := by
    intro x hx
    obtain ⟨i,hi,hUi⟩ := hx
    have hxsmall : x ∈ finiteMaxEvent U lambda N := ⟨i,hi,by linarith⟩
    rw [← firstExceed_union] at hxsmall
    obtain ⟨n,hn⟩ := mem_iUnion.mp hxsmall
    exact mem_iUnion.mpr ⟨n,⟨i,hi,hUi⟩,hn⟩
  calc
    _ ≤ μ.real (⋃ n : Fin (N + 1), finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n) :=
      measureReal_mono hcover
    _ ≤ ∑ n : Fin (N + 1), μ.real (finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ n : Fin (N + 1), (1 / 2 : ℝ) * μ.real (B n) := Finset.sum_le_sum (fun n _ => hcell n)
    _ = (1 / 2 : ℝ) * μ.real (finiteMaxEvent U lambda N) := by
      rw [← Finset.mul_sum, firstExceed_measure_sum μ U lambda N (fun i _ => hUm i)]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MartingaleGeometricTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iterating the first-crossing contraction gives a geometric tail with
constants independent of the number of time steps. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert

variable {X : Type*} {m : MeasurableSpace X} {μ : Measure X}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ m} {F : ℕ → X → ℝ}

theorem martingale_geometric_tail (hF : Martingale F ℱ μ) (N : ℕ)
    {A D : ℝ} (hA : 0 < A) (hD : 0 ≤ D)
    (hBMO : TerminalMeanOscillationBound F ℱ μ N A)
    (hjump : ∀ i < N, ∀ x, ‖F (i + 1) x - F i x‖ ≤ D) (k : ℕ) :
    μ.real (finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) ((k : ℝ) * (D + 2 * A)) N) ≤
      (1 / 2 : ℝ) ^ k * μ.real univ := by
  induction k with
  | zero =>
    simpa only [Nat.cast_zero, zero_mul, pow_zero, one_mul] using
      (measureReal_mono (μ := μ) (subset_univ
        (finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) 0 N)))
  | succ k ih =>
    have hlambda : 0 ≤ (k : ℝ) * (D + 2 * A) := mul_nonneg (Nat.cast_nonneg k) (by linarith)
    have h := martingale_goodLambda hF N hA hD hlambda hBMO hjump
    have heq : (k : ℝ) * (D + 2 * A) + D + 2 * A =
        ((k + 1 : ℕ) : ℝ) * (D + 2 * A) := by push_cast; ring
    rw [heq] at h
    exact h.trans (by simpa only [pow_succ, mul_assoc, mul_left_comm] using
      mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 1 / 2))

theorem martingale_terminal_geometric_tail (hF : Martingale F ℱ μ) (N : ℕ)
    {A D : ℝ} (hA : 0 < A) (hD : 0 ≤ D)
    (hBMO : TerminalMeanOscillationBound F ℱ μ N A)
    (hjump : ∀ i < N, ∀ x, ‖F (i + 1) x - F i x‖ ≤ D) (k : ℕ) :
    μ.real {x | (k : ℝ) * (D + 2 * A) < ‖F N x - F 0 x‖} ≤
      (1 / 2 : ℝ) ^ k * μ.real univ := by
  apply (measureReal_mono (μ := μ) (show
    {x | (k : ℝ) * (D + 2 * A) < ‖F N x - F 0 x‖} ⊆
      finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) ((k : ℝ) * (D + 2 * A)) N from
        fun _ hx => ⟨N,le_rfl,hx⟩)).trans
  exact martingale_geometric_tail hF N hA hD hBMO hjump k

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MeanOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local mean oscillation estimates used before John--Nirenberg.
The short part is controlled in mean and the long part by its oscillation.
All constants are independent of the dimension of the range. -/

noncomputable section

open MeasureTheory Set

namespace LipschitzHilbert

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem norm_average_sub_le (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → E) (hf : Integrable f μ) (hm : 0 < μ.real univ) (c : E) :
    ‖integralAverage μ f - c‖ ≤ (μ.real univ)⁻¹ * ∫ x, ‖f x - c‖ ∂μ := by
  have heq : integralAverage μ f - c = (μ.real univ)⁻¹ • ∫ x, (f x - c) ∂μ := by
    rw [integral_sub hf (integrable_const c), integral_const, smul_sub,
      smul_smul, inv_mul_cancel₀ hm.ne', one_smul]
    rfl
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.mpr hm.le)

theorem integral_oscillation_le_twice (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → E) (hf : Integrable f μ) (hm : 0 < μ.real univ) (c : E) :
    (∫ x, ‖f x - integralAverage μ f‖ ∂μ) ≤ 2 * ∫ x, ‖f x - c‖ ∂μ := by
  have hpoint (x : X) : ‖f x - integralAverage μ f‖ ≤
      ‖f x - c‖ + ‖integralAverage μ f - c‖ := by
    simpa only [norm_sub_rev] using
      norm_sub_le_norm_sub_add_norm_sub (f x) c (integralAverage μ f)
  calc
    _ ≤ ∫ x, (‖f x - c‖ + ‖integralAverage μ f - c‖) ∂μ :=
      integral_mono (hf.sub (integrable_const _)).norm
        ((hf.sub (integrable_const c)).norm.add (integrable_const _)) hpoint
    _ = (∫ x, ‖f x - c‖ ∂μ) + μ.real univ * ‖integralAverage μ f - c‖ := by
      rw [integral_add (show Integrable (fun x => ‖f x - c‖) μ from
        (hf.sub (integrable_const c)).norm) (integrable_const _),
        integral_const, smul_eq_mul]
    _ ≤ (∫ x, ‖f x - c‖ ∂μ) +
        μ.real univ * ((μ.real univ)⁻¹ * ∫ x, ‖f x - c‖ ∂μ) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (norm_average_sub_le μ f hf hm c) hm.le)
    _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hm.ne']; ring

omit [CompleteSpace E] in
theorem integralAverage_add (μ : Measure X) (f g : X → E)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    integralAverage μ (fun x => f x + g x) = integralAverage μ f + integralAverage μ g := by
  simp only [integralAverage, integral_add hf hg, smul_add]

theorem short_long_mean_oscillation (μ : Measure X) [IsFiniteMeasure μ]
    (f g : X → E) (hf : Integrable f μ) (hg : Integrable g μ)
    (hm : 0 < μ.real univ) {K L : ℝ}
    (hshort : (∫ x, ‖f x‖ ∂μ) ≤ K * μ.real univ)
    (hlong : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ‖g x - g y‖ ≤ L) :
    (∫ x, ‖f x + g x - integralAverage μ (fun y => f y + g y)‖ ∂μ) ≤
      (2 * K + L) * μ.real univ := by
  have hgpoint : ∀ᵐ x ∂μ, ‖g x - integralAverage μ g‖ ≤ L := by
    filter_upwards [hlong] with x hx
    exact norm_sub_mean_le μ g hg hm (g x) L hx
  have hfmean := integral_oscillation_le_twice μ f hf hm (0 : E)
  simp only [sub_zero] at hfmean
  have hgmean : (∫ x, ‖g x - integralAverage μ g‖ ∂μ) ≤ L * μ.real univ := by
    simpa only [integral_const, smul_eq_mul, mul_comm, Pi.sub_apply] using
      integral_mono_ae (hg.sub (integrable_const _)).norm (integrable_const L) hgpoint
  calc
    _ ≤ ∫ x, (‖f x - integralAverage μ f‖ + ‖g x - integralAverage μ g‖) ∂μ := by
      apply integral_mono
        (show Integrable (fun x => ‖f x + g x - integralAverage μ (fun y => f y + g y)‖) μ from
          ((hf.add hg).sub (integrable_const _)).norm)
        (show Integrable (fun x => ‖f x - integralAverage μ f‖ +
            ‖g x - integralAverage μ g‖) μ from
          (hf.sub (integrable_const _)).norm.add (hg.sub (integrable_const _)).norm)
      intro x
      rw [integralAverage_add μ f g hf hg]
      dsimp only
      rw [add_sub_add_comm]
      exact norm_add_le (f x - integralAverage μ f) (g x - integralAverage μ g)
    _ = (∫ x, ‖f x - integralAverage μ f‖ ∂μ) +
        ∫ x, ‖g x - integralAverage μ g‖ ∂μ := by
      exact integral_add (show Integrable (fun x => ‖f x - integralAverage μ f‖) μ from
        (hf.sub (integrable_const _)).norm)
        (show Integrable (fun x => ‖g x - integralAverage μ g‖) μ from
          (hg.sub (integrable_const _)).norm)
    _ ≤ (2 * K + L) * μ.real univ := by linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridBMO
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mean oscillation on the actual line cells controls every martingale
jump by the branching factor. This supplies the overshoot bound in the
dyadic stopping proof of John--Nirenberg. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert.FiniteLineGrid

theorem cell_mass (g : FiniteLineGrid) (level i : ℕ) :
    (volume.restrict (g.cell level i)).real univ = g.meshWidth level := by
  rw [measureReal_def, Measure.restrict_apply_univ, cell, Real.volume_Ico]
  have heq : g.origin + g.meshWidth level * (i + 1) -
      (g.origin + g.meshWidth level * i) = g.meshWidth level := by ring
  rw [heq, ENNReal.toReal_ofReal (g.meshWidth_pos level).le]

theorem cellMean_eq_integralAverage (g : FiniteLineGrid) (f : ℝ → ℝ) (level i : ℕ) :
    g.cellMean f level i = integralAverage (volume.restrict (g.cell level i)) f := by
  simp only [integralAverage, g.cell_mass, cellMean, smul_eq_mul]

theorem cellMean_sub_constant_le (g : FiniteLineGrid) (f : ℝ → ℝ)
    {level i : ℕ} (hf : IntegrableOn f (g.cell level i)) (c : ℝ) :
    |g.cellMean f level i - c| ≤
      (g.meshWidth level)⁻¹ * ∫ x in g.cell level i, |f x - c| := by
  rw [g.cellMean_eq_integralAverage]
  simpa only [Real.norm_eq_abs, g.cell_mass] using
    norm_average_sub_le (volume.restrict (g.cell level i)) f hf
      (by rw [g.cell_mass]; exact g.meshWidth_pos level) c

theorem cell_subset_parent (g : FiniteLineGrid) {level i : ℕ}
    (hl : level + 1 ≤ g.depth) (hi : i < g.branching ^ (level + 1)) :
    g.cell (level + 1) i ⊆ g.cell level (i / g.branching) := by
  intro x hx
  have hr := g.cell_subset_root (level + 1) hi hx
  have hix := (g.index_eq_iff_mem_cell hl hr i).mpr hx
  have hp := congrArg Fin.val (g.index_parent (by omega : level < g.depth) x)
  change (g.index level x).val = (g.index (level + 1) x).val / g.branching at hp
  rw [hix] at hp
  exact (g.index_eq_iff_mem_cell (by omega) hr (i / g.branching)).mp hp

theorem parent_index_lt (g : FiniteLineGrid) {level i : ℕ}
    (hi : i < g.branching ^ (level + 1)) : i / g.branching < g.branching ^ level := by
  apply (Nat.div_lt_iff_lt_mul g.branching_pos).mpr
  simpa only [pow_succ] using hi

theorem meshWidth_succ (g : FiniteLineGrid) (level : ℕ) :
    g.meshWidth (level + 1) = g.meshWidth level / g.branching := by
  simp only [meshWidth, pow_succ, div_div]

theorem cellMean_parent_jump (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {level i : ℕ} (hl : level + 1 ≤ g.depth) (hi : i < g.branching ^ (level + 1)) :
    |g.cellMean f (level + 1) i - g.cellMean f level (i / g.branching)| ≤
      g.branching * A := by
  have hip := g.parent_index_lt hi
  have hsub := g.cell_subset_parent hl hi
  have hfp : IntegrableOn f (g.cell level (i / g.branching)) :=
    hf.mono_measure (Measure.restrict_mono_set volume (g.cell_subset_root level hip))
  have hfc := hfp.mono_set hsub
  have hnorm : IntegrableOn (fun x => |f x - g.cellMean f level (i / g.branching)|)
      (g.cell level (i / g.branching)) := by
    simpa only [IntegrableOn, Real.norm_eq_abs, Pi.sub_apply] using
      (hfp.sub (integrable_const _)).norm
  have hmono : (∫ x in g.cell (level + 1) i, |f x - g.cellMean f level (i / g.branching)|) ≤
      ∫ x in g.cell level (i / g.branching), |f x - g.cellMean f level (i / g.branching)| :=
    setIntegral_mono_set hnorm (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hsub hx)
  calc
    _ ≤ (g.meshWidth (level + 1))⁻¹ *
        ∫ x in g.cell (level + 1) i, |f x - g.cellMean f level (i / g.branching)| :=
      g.cellMean_sub_constant_le f hfc _
    _ ≤ (g.meshWidth (level + 1))⁻¹ * (A * g.meshWidth level) :=
      mul_le_mul_of_nonneg_left (hmono.trans (hA level (i / g.branching) (by omega) hip))
        (inv_nonneg.mpr (g.meshWidth_pos _).le)
    _ = _ := by rw [g.meshWidth_succ]; field_simp [(g.meshWidth_pos level).ne']

theorem average_eq_cellMean (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level)
    {x : ℝ} (hx : x ∈ g.cell level i) :
    g.average g.lineMeasure f level x = g.cellMean f level i := by
  rw [g.average_eq_cell_mean f hf hl hi hx, cellMean, div_eq_mul_inv, mul_comm]

theorem average_jump_le (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {level : ℕ} (hl : level < g.depth) {x : ℝ} (hx : x ∈ g.root) :
    |g.average g.lineMeasure f (level + 1) x - g.average g.lineMeasure f level x| ≤
      g.branching * A := by
  let i := (g.index (level + 1) x).val
  have hi : i < g.branching ^ (level + 1) := g.index_lt_level (by omega) x
  have hxc : x ∈ g.cell (level + 1) i :=
    (g.index_eq_iff_mem_cell (by omega) hx i).mp rfl
  rw [g.average_eq_cellMean f hf (by omega) hi hxc,
    g.average_eq_cellMean f hf (by omega) (g.parent_index_lt hi)
      (g.cell_subset_parent (by omega) hi hxc)]
  exact g.cellMean_parent_jump f hf hA (by omega) hi

theorem average_jump_le_everywhere (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {level : ℕ} (hl : level < g.depth) (x : ℝ) :
    |g.average g.lineMeasure f (level + 1) x - g.average g.lineMeasure f level x| ≤
      g.branching * A := by
  by_cases hx : x ∈ g.root
  · exact g.average_jump_le f hf hA hl hx
  · have ho : g.origin ∈ g.root := ⟨le_rfl, by linarith [g.width_pos]⟩
    have hidx (n : ℕ) : g.index n x = g.index n g.origin := by
      apply Fin.ext
      simp only [index, rawIndex, ite_eq_right hx, ite_eq_left ho, sub_self,
        zero_div, zero_mul, Nat.floor_zero]
    rw [g.average_constant g.lineMeasure f (level + 1) (hidx _),
      g.average_constant g.lineMeasure f level (hidx _)]
    exact g.average_jump_le f hf hA hl ho

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridConditionalBMO
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete cellwise mean-oscillation bound implies the conditional
oscillation hypothesis used by the finite martingale stopping argument. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert.FiniteLineGrid

theorem integrated_oscillation_le (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {n : ℕ} (hn : n ≤ g.depth) {s : Set ℝ} (hs : MeasurableSet[g.filtration n] s) :
    (∫ x in s, |f x - g.average g.lineMeasure f n x| ∂g.lineMeasure) ≤
      A * g.lineMeasure.real s := by
  let G := fun x => |f x - g.average g.lineMeasure f n x|
  have havg : Integrable (g.average g.lineMeasure f n) g.lineMeasure :=
    (g.average_martingale g.lineMeasure f).integrable n
  have hG : Integrable G g.lineMeasure := (hf.sub havg).abs
  have hb : ∀ᵐ x ∂g.lineMeasure, g.average g.lineMeasure G n x ≤ A := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    let i := (g.index n x).val
    have hi : i < g.branching ^ n := g.index_lt_level hn x
    have hxc : x ∈ g.cell n i := (g.index_eq_iff_mem_cell hn hx i).mp rfl
    rw [g.average_eq_cell_mean G hG hn hi hxc]
    have heq : (∫ y in g.cell n i, G y) =
        ∫ y in g.cell n i, |f y - g.cellMean f n i| := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro y hy
      simp only [G, g.average_eq_cellMean f hf hn hi hy]
    rw [heq]
    exact (div_le_iff₀ (g.meshWidth_pos n)).mpr (hA n i hn hi)
  change (∫ x in s, G x ∂g.lineMeasure) ≤ _
  rw [← setIntegral_condExp (g.filtration.le n) hG hs]
  have h := integral_mono_ae (μ := g.lineMeasure.restrict s)
    integrable_condExp.integrableOn (integrable_const A)
    (ae_restrict_of_ae hb)
  simpa only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, mul_comm] using h

theorem terminal_mean_oscillation (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {N : ℕ} (hN : N ≤ g.depth) :
    TerminalMeanOscillationBound (g.average g.lineMeasure f) g.filtration g.lineMeasure N A := by
  intro n hn s hs
  have hsm : MeasurableSet[g.filtration N] s := g.filtration.mono hn _ hs
  have havg : Integrable (g.average g.lineMeasure f n) g.lineMeasure :=
    (g.average_martingale g.lineMeasure f).integrable n
  have heq : g.lineMeasure[(fun x => f x - g.average g.lineMeasure f n x) | g.filtration N] =ᵐ[g.lineMeasure]
      (fun x => g.average g.lineMeasure f N x - g.average g.lineMeasure f n x) := by
    have hsub := condExp_sub hf havg (g.filtration N)
    have hmeas : StronglyMeasurable[g.filtration N] (g.average g.lineMeasure f n) :=
      (g.average_martingale g.lineMeasure f).stronglyMeasurable n |>.mono (g.filtration.mono hn)
    rw [condExp_of_stronglyMeasurable (g.filtration.le N) hmeas havg] at hsub
    exact hsub
  calc
    _ = ∫ x in s, |g.lineMeasure[(fun x => f x - g.average g.lineMeasure f n x) | g.filtration N] x|
        ∂g.lineMeasure := by
      apply setIntegral_congr_ae (g.filtration.le n _ hs)
      filter_upwards [heq] with x hx _
      rw [hx]
    _ ≤ ∫ x in s, |f x - g.average g.lineMeasure f n x| ∂g.lineMeasure :=
      setIntegral_abs_condExp_le hsm _
    _ ≤ _ := g.integrated_oscillation_le f hf hA (hn.trans hN) hs

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridBMO_Tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric John--Nirenberg tails for the concrete line-cell averages. -/

noncomputable section

open MeasureTheory Set

namespace LipschitzHilbert.FiniteLineGrid

theorem mean_oscillation_average_tail (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : 0 < A)
    (hBMO : g.HasMeanOscillationBound f A) {N : ℕ} (hN : N ≤ g.depth) (k : ℕ) :
    g.lineMeasure.real {x | (k : ℝ) * ((g.branching : ℝ) + 2) * A <
      |g.average g.lineMeasure f N x - g.average g.lineMeasure f 0 x|} ≤
        (1 / 2 : ℝ) ^ k * g.lineMeasure.real univ := by
  have htail := martingale_terminal_geometric_tail (g.average_martingale g.lineMeasure f) N hA
    (mul_nonneg (Nat.cast_nonneg g.branching) hA.le)
    (g.terminal_mean_oscillation f hf hBMO hN)
    (fun i hi x => by
      simpa only [Real.norm_eq_abs] using
        g.average_jump_le_everywhere f hf hBMO (hi.trans_le hN) x) k
  have hscale : (k : ℝ) * ((g.branching : ℝ) * A + 2 * A) =
      (k : ℝ) * ((g.branching : ℝ) + 2) * A := by ring
  simpa only [hscale, Real.norm_eq_abs] using htail

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual cell averages converge at every continuity point in the root.
Only this continuous-function specialization of differentiation is needed
for the finite smooth packet and variation functions. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace LipschitzHilbert.FiniteLineGrid

theorem cell_zero (g : FiniteLineGrid) : g.cell 0 0 = g.root := by
  simp only [cell, meshWidth, pow_zero, div_one, Nat.cast_zero, mul_zero,
    add_zero, zero_add, mul_one, root]

theorem average_zero_eq_integralAverage (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {x : ℝ} (hx : x ∈ g.root) :
    g.average g.lineMeasure f 0 x = integralAverage g.lineMeasure f := by
  rw [g.average_eq_cellMean (i := 0) f hf (Nat.zero_le _) (by simp)
    (by simpa only [g.cell_zero] using hx), g.cellMean_eq_integralAverage, g.cell_zero]
  rfl

theorem average_close_of_mesh (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {n : ℕ} (hn : n ≤ g.depth)
    {x : ℝ} (hx : x ∈ g.root) {epsilon delta : ℝ}
    (hlocal : ∀ y, dist y x < delta → |f y - f x| ≤ epsilon)
    (hmesh : g.meshWidth n < delta) :
    |g.average g.lineMeasure f n x - f x| ≤ epsilon := by
  let i := (g.index n x).val
  have hi : i < g.branching ^ n := g.index_lt_level hn x
  have hxc : x ∈ g.cell n i := (g.index_eq_iff_mem_cell hn hx i).mp rfl
  have hfc : IntegrableOn f (g.cell n i) :=
    hf.mono_measure (Measure.restrict_mono_set volume (g.cell_subset_root n hi))
  have hpoint : ∀ᵐ y ∂volume.restrict (g.cell n i), ‖f x - f y‖ ≤ epsilon := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    have hyr := g.cell_subset_root n hi hy
    have hiy := (g.index_eq_iff_mem_cell hn hyr i).mpr hy
    have heq : g.index n y = g.index n x := Fin.ext hiy
    have hd := g.same_index_distance hn hyr hx heq
    have hdist : dist y x < delta := by
      rw [Real.dist_eq]
      exact hd.trans_lt hmesh
    simpa only [Real.norm_eq_abs, abs_sub_comm] using hlocal y hdist
  have h := norm_sub_mean_le (volume.restrict (g.cell n i)) f hfc
    (by rw [g.cell_mass]; exact g.meshWidth_pos n) (f x) epsilon hpoint
  rw [g.average_eq_cellMean f hf hn hi hxc, g.cellMean_eq_integralAverage]
  simpa only [integralAverage, Real.norm_eq_abs, abs_sub_comm] using h

theorem meshWidth_tendsto_zero (g : FiniteLineGrid) (hb : 1 < g.branching) :
    Tendsto g.meshWidth atTop (𝓝 0) := by
  change Tendsto (fun n => g.width / (g.branching : ℝ) ^ n) atTop (𝓝 0)
  have hbR : (1 : ℝ) < g.branching := by exact_mod_cast hb
  have hpow := tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    (r := (g.branching : ℝ)⁻¹) (by rw [abs_of_pos (inv_pos.mpr (by linarith))]; exact inv_lt_one_of_one_lt₀ hbR)
  have h : Tendsto (fun n : ℕ => g.width * ((g.branching : ℝ)⁻¹) ^ n)
      atTop (𝓝 (g.width * 0)) := tendsto_const_nhds.mul hpow
  simpa only [mul_zero, meshWidth, div_eq_mul_inv, inv_pow] using
    (h : Tendsto (fun n : ℕ => g.width * ((g.branching : ℝ)⁻¹) ^ n) atTop (𝓝 (g.width * 0)))

theorem average_tendsto_at_continuity (g : FiniteLineGrid) (hb : 1 < g.branching)
    (f : ℝ → ℝ) (hf : Integrable f g.lineMeasure)
    {x : ℝ} (hx : x ∈ g.root) (hcont : ContinuousAt f x) :
    Tendsto (fun N => (g.withDepth N).average (g.withDepth N).lineMeasure f N x)
      atTop (𝓝 (f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  obtain ⟨delta,hdelta,hlocal⟩ := Metric.continuousAt_iff.mp hcont (epsilon / 2) (by positivity)
  have hmesh := (tendsto_order.mp (g.meshWidth_tendsto_zero hb)).2 delta hdelta
  filter_upwards [hmesh] with N hN
  rw [Real.dist_eq]
  apply lt_of_le_of_lt ((g.withDepth N).average_close_of_mesh f hf le_rfl hx
    (fun y hy => (by simpa only [Real.dist_eq] using (hlocal hy).le)) hN)
  linarith

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ContinuousBMOTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! John--Nirenberg's geometric distribution bound for a continuous
function on an actual finite interval. The proof passes the uniform finite
grid estimate to the function, using pointwise convergence of cell means. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace LipschitzHilbert.FiniteLineGrid

theorem continuous_mean_oscillation_tail (g : FiniteLineGrid) (hb : 1 < g.branching)
    (f : ℝ → ℝ) (hf : Integrable f g.lineMeasure)
    (hc : ∀ x ∈ g.root, ContinuousAt f x) {A : ℝ} (hA : 0 < A)
    (hBMO : g.HasFullMeanOscillationBound f A) (k : ℕ) :
    g.lineMeasure.real {x | (k : ℝ) * ((g.branching : ℝ) + 2) * A <
      |f x - integralAverage g.lineMeasure f|} ≤
        (1 / 2 : ℝ) ^ k * g.lineMeasure.real univ := by
  let F := fun N x => |(g.withDepth N).average (g.withDepth N).lineMeasure f N x -
    integralAverage g.lineMeasure f|
  have hlim : ∀ᵐ x ∂g.lineMeasure,
      Tendsto (fun N => F N x) atTop (𝓝 |f x - integralAverage g.lineMeasure f|) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    have h := (g.average_tendsto_at_continuity hb f hf hx (hc x hx)).sub_const
      (integralAverage g.lineMeasure f)
    simpa only [F, Real.norm_eq_abs] using h.norm
  apply strict_tail_bound_of_ae_tendsto g.lineMeasure F _ hlim _ _ (by positivity)
  intro N
  have hBN : (g.withDepth N).HasMeanOscillationBound f A := by
    intro n i _ hi
    exact hBMO n i hi
  have htail := (g.withDepth N).mean_oscillation_average_tail f hf hA hBN le_rfl k
  have heq : {x | (k : ℝ) * ((g.branching : ℝ) + 2) * A < F N x} =ᵐ[g.lineMeasure]
      {x | (k : ℝ) * ((g.branching : ℝ) + 2) * A <
        |(g.withDepth N).average (g.withDepth N).lineMeasure f N x -
          (g.withDepth N).average (g.withDepth N).lineMeasure f 0 x|} := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    change ((k : ℝ) * ((g.branching : ℝ) + 2) * A < F N x) = ((k : ℝ) * ((g.branching : ℝ) + 2) * A <
        |(g.withDepth N).average (g.withDepth N).lineMeasure f N x -
          (g.withDepth N).average (g.withDepth N).lineMeasure f 0 x|)
    simp only [F, (g.withDepth N).average_zero_eq_integralAverage f hf hx]
    rfl
  have hm := congrArg ENNReal.toReal (measure_congr heq)
  exact hm.trans_le htail

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_GeometricTailExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A geometric distribution bound gives an exponential moment by summing
the level strips. The factor is absolute and no boundedness hypothesis is
needed for the function. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LipschitzHilbert

theorem geometric_tail_exponential {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {H : ℝ} (hH : 0 < H)
    (htail : ∀ n : ℕ, μ.real {x | (n : ℝ) * H < f x} ≤
      (1 / 2 : ℝ) ^ n * μ.real univ) :
    (∫⁻ x, ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ∂μ) ≤ 7 * μ univ := by
  classical
  let S := fun n : ℕ => {x | (n : ℝ) * H < f x}
  let F := fun n : ℕ => (S n).indicator (fun _ => (3 / 2 : ℝ≥0∞) ^ (n + 1))
  have hSm (n : ℕ) : MeasurableSet (S n) := measurableSet_lt measurable_const hf
  have hFm (n : ℕ) : Measurable (F n) := measurable_const.indicator (hSm n)
  have hpoint (x : X) : ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ≤ 1 + ∑' n, F n x := by
    by_cases hx : f x = 0
    · simp [hx]
    · have hfx : 0 < f x := lt_of_le_of_ne (hf0 x) (Ne.symm hx)
      have hk : 0 < ⌈f x / H⌉₊ := Nat.ceil_pos.mpr (div_pos hfx hH)
      let n := ⌈f x / H⌉₊ - 1
      have hn : n + 1 = ⌈f x / H⌉₊ := by dsimp [n]; omega
      have hns : x ∈ S n := by
        apply (lt_div_iff₀ hH).mp
        apply Nat.lt_ceil.mp
        dsimp [n]
        omega
      have hr : (3 / 2 : ℝ) ^ (f x / H) ≤ (3 / 2 : ℝ) ^ (n + 1) := by
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [hn]
        exact Nat.le_ceil _
      have hterm : ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ≤ F n x := by
        dsimp only [F]
        rw [indicator_of_mem hns]
        have h := ENNReal.ofReal_le_ofReal hr
        simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3 / 2),
          ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
          ENNReal.ofReal_ofNat] using h
      have hsum : F n x ≤ ∑' j, F j x := ENNReal.le_tsum (f := fun j => F j x) n
      exact hterm.trans (hsum.trans le_add_self)
  have ht (n : ℕ) : μ (S n) ≤ (1 / 2 : ℝ≥0∞) ^ n * μ univ := by
    have h := ENNReal.ofReal_le_ofReal (htail n)
    rw [ofReal_measureReal, ENNReal.ofReal_mul (pow_nonneg (by norm_num) _),
      ofReal_measureReal] at h
    norm_num only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat] at h
    exact h
  calc
    _ ≤ ∫⁻ x, 1 + ∑' n, F n x ∂μ := lintegral_mono hpoint
    _ = μ univ + ∑' n, ∫⁻ x, F n x ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_const, one_mul,
        lintegral_tsum (fun n => (hFm n).aemeasurable)]
    _ = μ univ + ∑' n, (3 / 2 : ℝ≥0∞) ^ (n + 1) * μ (S n) := by
      congr 1
      apply tsum_congr
      intro n
      exact lintegral_indicator_const (hSm n) _
    _ ≤ μ univ + ∑' n, (3 / 2 : ℝ≥0∞) ^ (n + 1) * ((1 / 2 : ℝ≥0∞) ^ n * μ univ) := by
      gcongr with n
      exact ht n
    _ = μ univ + (3 / 2 : ℝ≥0∞) * (∑' n : ℕ, (3 / 4 : ℝ≥0∞) ^ n) * μ univ := by
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
      congr 1
      apply tsum_congr
      intro n
      rw [pow_succ]
      have hp : (3 / 4 : ℝ≥0∞) ^ n = (3 / 2 : ℝ≥0∞) ^ n * (1 / 2 : ℝ≥0∞) ^ n := by
        rw [← mul_pow]
        congr 1
        have hnn : (3 / 4 : ℝ≥0) = (3 / 2 : ℝ≥0) * (1 / 2 : ℝ≥0) := by norm_num
        have hc := congrArg (fun z : ℝ≥0 => (z : ℝ≥0∞)) hnn
        simpa only [ENNReal.coe_mul, ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0),
          ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat,
          ENNReal.coe_one] using hc
      rw [hp]
      ring
    _ = 7 * μ univ := by
      rw [ENNReal.tsum_geometric]
      have hc : (3 / 2 : ℝ≥0∞) * (1 - 3 / 4)⁻¹ = 6 := by
        have hquarter : (1 - 3 / 4 : ℝ≥0) = 1 / 4 := by
          apply NNReal.eq
          rw [NNReal.coe_sub (by exact_mod_cast (show (3 / 4 : ℝ) ≤ 1 by norm_num))]
          norm_num
        have hne : (1 - 3 / 4 : ℝ≥0) ≠ 0 := by rw [hquarter]; norm_num
        have hnn : (3 / 2 : ℝ≥0) * (1 - 3 / 4)⁻¹ = 6 := by rw [hquarter]; norm_num
        have hc := congrArg (fun z : ℝ≥0 => (z : ℝ≥0∞)) hnn
        simpa only [ENNReal.coe_mul, ENNReal.coe_inv hne,
          ENNReal.coe_sub, ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0),
          ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat,
          ENNReal.coe_one] using hc
      calc
        _ = (1 + (3 / 2 : ℝ≥0∞) * (1 - 3 / 4)⁻¹) * μ univ := by ring
        _ = _ := by rw [hc]; norm_num

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_GeometricTailMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-power moment bounds from the geometric distribution estimate. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem geometric_tail_rpow_moment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {H : ℝ} (hH : 0 < H)
    (htail : ∀ n : ℕ, μ.real {x | (n : ℝ) * H < f x} ≤
      (1 / 2 : ℝ) ^ n * μ.real univ) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ) ≤
      7 * ENNReal.ofReal ((p * H / Real.log (3 / 2)) ^ p) * μ univ := by
  let t : ℝ := Real.log (3 / 2) / H
  have hlog : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have ht : 0 < t := div_pos hlog hH
  have hcoef : p / t = p * H / Real.log (3 / 2) := by
    dsimp [t]
    field_simp
  let K : ℝ := (p * H / Real.log (3 / 2)) ^ p
  have hK : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  have hpoint (x : X) : f x ^ p ≤ K * ((3 / 2 : ℝ) ^ (f x / H)) := by
    have h := ProbabilityTheory.rpow_abs_le_mul_exp_abs (f x) hp ht.ne'
    rw [abs_of_pos ht, abs_of_nonneg (hf0 x), hcoef] at h
    have hexp : Real.exp (t * f x) = (3 / 2 : ℝ) ^ (f x / H) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      congr 1
      dsimp [t]
      ring
    simpa only [hexp, K] using h
  have hpoint' (x : X) : ENNReal.ofReal (f x ^ p) ≤
      ENNReal.ofReal K * ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) := by
    simpa only [ENNReal.ofReal_mul hK] using ENNReal.ofReal_le_ofReal (hpoint x)
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal K * ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ∂μ :=
      lintegral_mono hpoint'
    _ = ENNReal.ofReal K * ∫⁻ x, ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * (7 * μ univ) :=
      mul_le_mul_right (geometric_tail_exponential μ f hf hf0 hH htail) _
    _ = _ := by dsimp [K]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ContinuousBMOMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-power John--Nirenberg moments on an actual interval. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert.FiniteLineGrid

theorem continuous_mean_oscillation_moment (g : FiniteLineGrid) (hb : 1 < g.branching)
    (f : ℝ → ℝ) (hm : Measurable f) (hf : Integrable f g.lineMeasure)
    (hc : ∀ x ∈ g.root, ContinuousAt f x) {A : ℝ} (hA : 0 < A)
    (hBMO : g.HasFullMeanOscillationBound f A) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, ENNReal.ofReal (|f x - integralAverage g.lineMeasure f| ^ p) ∂g.lineMeasure) ≤
      7 * ENNReal.ofReal ((p * (((g.branching : ℝ) + 2) * A) / Real.log (3 / 2)) ^ p) *
        g.lineMeasure univ := by
  have hmeas : Measurable (fun x => |f x - integralAverage g.lineMeasure f|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hm.sub measurable_const).norm
  apply geometric_tail_rpow_moment g.lineMeasure _ hmeas (fun _ => abs_nonneg _)
    (mul_pos (by positivity) hA) _ hp
  intro n
  simpa only [mul_assoc] using g.continuous_mean_oscillation_tail hb f hf hc hA hBMO n

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_EnvelopeDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horizontal derivatives of the fixed rational packet envelope. -/

noncomputable section

namespace LipschitzHilbert

theorem lineEnvelope_three_derivative_bound (a l x : ℝ) (hl : 0 < l) :
    |deriv (lineEnvelope a l 3) x| ≤ (6 / l) * lineEnvelope a l 3 x := by
  rw [(lineEnvelope_three_hasDerivAt a l x).deriv]
  let t := (x-a)/l
  have hb : 0 < 1+t^2 := by positivity
  have ht : |t| ≤ 1+t^2 := by nlinarith [sq_nonneg (|t|-1), sq_abs t]
  have heq : |(-6/l) * t * ((1+t^2)^4)⁻¹| =
      (6/l) * |t| * ((1+t^2)^4)⁻¹ := by
    rw [abs_mul, abs_mul, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 6),
      abs_of_pos hl, abs_of_nonneg (by positivity : 0 ≤ ((1+t^2)^4)⁻¹)]
  change |(-6/l) * t * ((1+t^2)^4)⁻¹| ≤ (6/l) * ((1+t^2)^3)⁻¹
  rw [heq]
  calc
    _ ≤ (6/l) * (1+t^2) * ((1+t^2)^4)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by positivity)) (by positivity)
    _ = _ := by field_simp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RawBMOMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uncentered interval moments from the proved John--Nirenberg estimate
and a bound for the interval mean. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert.FiniteLineGrid

theorem continuous_raw_moment (g : FiniteLineGrid) (hb : 1 < g.branching)
    (f : ℝ → ℝ) (hm : Measurable f) (hf : Integrable f g.lineMeasure)
    (hc : ∀ x ∈ g.root, ContinuousAt f x) {A B p : ℝ}
    (hA : 0 < A) (hBMO : g.HasFullMeanOscillationBound f A)
    (hmean : |integralAverage g.lineMeasure f| ≤ B) (hp : 0 ≤ p) :
    (∫⁻ x, (ENNReal.ofReal |f x|) ^ p ∂g.lineMeasure) ≤
      (2 : ℝ≥0∞) ^ p *
        (7 * ENNReal.ofReal ((p * (((g.branching : ℝ) + 2) * A) / Real.log (3 / 2)) ^ p) +
          (ENNReal.ofReal B) ^ p) * g.lineMeasure univ := by
  let m := integralAverage g.lineMeasure f
  have hcenter := g.continuous_mean_oscillation_moment hb f hm hf hc hA hBMO hp
  have hpoint (x : ℝ) : (ENNReal.ofReal |f x|) ^ p ≤
      (2 : ℝ≥0∞) ^ p * ((ENNReal.ofReal |f x - m|) ^ p + (ENNReal.ofReal B) ^ p) := by
    have habs : |f x| ≤ |f x - m| + B := by
      have ha := norm_add_le (f x - m) m
      simp only [Real.norm_eq_abs] at ha
      rw [sub_add_cancel] at ha
      exact ha.trans (add_le_add le_rfl hmean)
    have hB : 0 ≤ B := (abs_nonneg m).trans hmean
    have h0 : ENNReal.ofReal |f x| ≤ ENNReal.ofReal |f x - m| + ENNReal.ofReal B := by
      rw [← ENNReal.ofReal_add (abs_nonneg _) hB]
      exact ENNReal.ofReal_le_ofReal habs
    exact (ENNReal.rpow_le_rpow h0 hp).trans
      (ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ hp)
  have hmcenter : Measurable (fun x => (ENNReal.ofReal |f x - m|) ^ p) := by
    apply Measurable.pow_const
    apply Measurable.ennreal_ofReal
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hm.sub measurable_const).norm
  have heq : (fun x => (ENNReal.ofReal |f x - m|) ^ p) =
      (fun x => ENNReal.ofReal (|f x - m| ^ p)) := by
    funext x
    exact ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp
  calc
    _ ≤ ∫⁻ x, (2 : ℝ≥0∞) ^ p * ((ENNReal.ofReal |f x - m|) ^ p +
          (ENNReal.ofReal B) ^ p) ∂g.lineMeasure := lintegral_mono hpoint
    _ = (2 : ℝ≥0∞) ^ p * ((∫⁻ x, ENNReal.ofReal (|f x - m| ^ p) ∂g.lineMeasure) +
          (ENNReal.ofReal B) ^ p * g.lineMeasure univ) := by
      rw [lintegral_const_mul (f := fun x => (ENNReal.ofReal |f x - m|) ^ p +
          (ENNReal.ofReal B) ^ p) _ (hmcenter.add measurable_const),
        lintegral_add_left hmcenter, lintegral_const, heq]
    _ ≤ _ := by
      calc
        _ ≤ (2 : ℝ≥0∞) ^ p *
            (7 * ENNReal.ofReal ((p * (((g.branching : ℝ) + 2) * A) / Real.log (3 / 2)) ^ p) *
              g.lineMeasure univ + (ENNReal.ofReal B) ^ p * g.lineMeasure univ) := by
          gcongr
        _ = _ := by ring

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LocalizedEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local line integrals of a packet envelope, retaining both center-box
offsets. This is the positive estimate for the square-function argument. -/

noncomputable section
open Set MeasureTheory

namespace LipschitzHilbert

theorem local_lineEnvelope_weighted (s u l r k : ℝ) (hl : 0 < l) (hr : 0 < r)
    (hlr : l ≤ r) (hs : |s - (u + r*k)| ≤ r) :
    (((1 + |k|) ^ 2 / 8) ^ 2) * (∫ x in Icc (u-r) (u+r), lineEnvelope s l 3 x) ≤
      16 * (Real.pi * l) := by
  have hi : IntegrableOn (lineEnvelope s l 3) (Icc (u-r) (u+r)) :=
    (integrable_lineEnvelope s l hl (by decide : 1 ≤ 3)).restrict
  have hpoint : ∀ x ∈ Icc (u-r) (u+r),
      (((1 + |k|) ^ 2 / 8) ^ 2) * lineEnvelope s l 3 x ≤ 16 * lineEnvelope s l 1 x := by
    intro x hx
    have hxu : |x-u| ≤ r := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hweight : (1 + |k|)^2/8 ≤ polynomialWeight (u+r*k) r 1 x := by
      simpa only [pow_one] using box_polynomial_weight u r k x 1 hr hxu
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (1 + |k|)^2/8) hweight 2
    calc
      _ ≤ polynomialWeight (u+r*k) r 1 x ^ 2 * lineEnvelope s l 3 x :=
        mul_le_mul_of_nonneg_right hp (lineEnvelope_nonneg _ _ _ _)
      _ ≤ _ := by
        simpa only [pow_one] using polynomialWeight_sq_mul_envelope x s (u+r*k) l r 1 1 hl hr hlr hs
  rw [← integral_const_mul]
  calc
    _ ≤ ∫ x in Icc (u-r) (u+r), 16 * lineEnvelope s l 1 x :=
      setIntegral_mono_on (hi.const_mul _) ((integrable_lineEnvelope_one s l hl).restrict.const_mul _)
        measurableSet_Icc hpoint
    _ ≤ ∫ x, 16 * lineEnvelope s l 1 x :=
      setIntegral_le_integral ((integrable_lineEnvelope_one s l hl).const_mul _)
        (Filter.Eventually.of_forall (fun _ => mul_nonneg (by norm_num) (lineEnvelope_nonneg _ _ _ _)))
    _ = _ := by rw [integral_const_mul, integral_lineEnvelope_one s l hl]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PositiveLineKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive horizontal convolution kernel used for the error
majorant, with its short-interval integral bound. -/

noncomputable section
open Set MeasureTheory

namespace LipschitzHilbert

theorem local_lineKernel_integral (l u r s : ℝ) (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r) :
    (∫ x in Icc (u-r) (u+r), lineKernel l (x-s)) ≤
      (1024 * Real.pi) * lineEnvelope u r 2 s := by
  let k := (s-u)/r
  have hs : |s-(u+r*k)| ≤ r := by
    have heq : s-(u+r*k) = 0 := by dsimp [k]; field_simp; ring
    rw [heq, abs_zero]
    exact hr.le
  have hloc := local_lineEnvelope_weighted s u l r k hl hr hlr hs
  have hw : 0 < ((1+|k|)^2/8)^2 := by positivity
  have hhor : (∫ x in Icc (u-r) (u+r), lineEnvelope s l 3 x) ≤
      (16 * (Real.pi*l)) * (((1+|k|)^2/8)^2)⁻¹ := by
    have h : (∫ x in Icc (u-r) (u+r), lineEnvelope s l 3 x) ≤
        (16 * (Real.pi*l)) / (((1+|k|)^2/8)^2) :=
      (le_div_iff₀ hw).mpr (by nlinarith [hloc])
    simpa only [div_eq_mul_inv] using h
  have hweight : lineEnvelope 0 1 1 k ^ 2 = lineEnvelope u r 2 s := by
    simp only [lineEnvelope, sub_zero, div_one, pow_one, ← inv_pow, k]
  simp_rw [lineKernel_shift]
  rw [integral_const_mul]
  calc
    _ ≤ l⁻¹ * ((16 * (Real.pi*l)) * (((1+|k|)^2/8)^2)⁻¹) :=
      mul_le_mul_of_nonneg_left hhor (by positivity)
    _ = (16 * Real.pi) * (((1+|k|)^2/8)^2)⁻¹ := by field_simp
    _ ≤ (16 * Real.pi) * (64 * lineEnvelope 0 1 1 k ^ 2) :=
      mul_le_mul_of_nonneg_left (box_decay_le_line_envelope k) (by positivity)
    _ = _ := by rw [hweight]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineKernelOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An integrable pointwise majorant for translations of a long-scale
kernel. It is used before integrating against a bounded source. -/

noncomputable section
open Set

namespace LipschitzHilbert

theorem lineEnvelope_nearby (s l x z : ℝ) (hl : 0 < l) (hz : |z-x| ≤ 2*l) :
    lineEnvelope s l 1 z ≤ 10 * lineEnvelope s l 1 x := by
  have hv : |(x-z)/l| ≤ 2 := by
    rw [abs_div, abs_of_pos hl, div_le_iff₀ hl, abs_sub_comm]
    exact hz
  have hv2 : ((x-z)/l)^2 ≤ 4 := by nlinarith [sq_abs ((x-z)/l), (abs_le.mp hv).1, (abs_le.mp hv).2]
  have heq : (x-s)/l = (z-s)/l + (x-z)/l := by ring
  have hbase : 1+((x-s)/l)^2 ≤ 10*(1+((z-s)/l)^2) := by
    rw [heq]
    nlinarith [sq_nonneg ((z-s)/l-(x-z)/l), sq_nonneg ((z-s)/l)]
  simp only [lineEnvelope, pow_one]
  rw [← one_div, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity : 0 < 1+((z-s)/l)^2)
    (by positivity : 0 < 1+((x-s)/l)^2)).mpr
  simpa only [one_mul] using hbase

theorem lineKernel_shift_hasDerivAt (l s x : ℝ) :
    HasDerivAt (fun z => lineKernel l (z-s))
      (l⁻¹ * deriv (lineEnvelope s l 3) x) x := by
  have h := (lineEnvelope_three_hasDerivAt s l x).differentiableAt.hasDerivAt.const_mul l⁻¹
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact lineKernel_shift l s z

theorem lineKernel_shift_derivative_bound (l s x z : ℝ) (hl : 0 < l)
    (hz : |z-x| ≤ 2*l) :
    ‖deriv (fun v => lineKernel l (v-s)) z‖ ≤ (60/l^2) * lineEnvelope s l 1 x := by
  rw [(lineKernel_shift_hasDerivAt l s z).deriv, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hl.le), Real.norm_eq_abs]
  calc
    _ ≤ l⁻¹ * ((6/l) * lineEnvelope s l 3 z) :=
      mul_le_mul_of_nonneg_left (lineEnvelope_three_derivative_bound s l z hl) (by positivity)
    _ ≤ l⁻¹ * ((6/l) * (10 * lineEnvelope s l 1 x)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (lineEnvelope_antitone s l z (by decide : 1 ≤ 3)).trans (lineEnvelope_nearby s l x z hl hz)
    _ = _ := by ring

theorem lineKernel_translation_bound (l s x y : ℝ) (hl : 0 < l) (hxy : |x-y| ≤ 2*l) :
    |lineKernel l (x-s) - lineKernel l (y-s)| ≤
      ((60/l^2) * |x-y|) * lineEnvelope s l 1 x := by
  have hx : x ∈ Icc (x-2*l) (x+2*l) := ⟨by linarith, by linarith⟩
  have hy : y ∈ Icc (x-2*l) (x+2*l) := by
    have h := abs_le.mp hxy
    constructor <;> linarith
  have hd (z : ℝ) (hz : z ∈ Icc (x-2*l) (x+2*l)) :
      ‖deriv (fun v => lineKernel l (v-s)) z‖ ≤ (60/l^2) * lineEnvelope s l 1 x :=
    lineKernel_shift_derivative_bound l s x z hl (abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩)
  have h := (convex_Icc (x-2*l) (x+2*l)).norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (lineKernel_shift_hasDerivAt l s z).differentiableAt) hd hy hx
  simp only [Real.norm_eq_abs] at h
  exact h.trans_eq (by ring)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PositiveConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual convolution of the positive error source with the horizontal
kernel. Bounded measurable sources need not be globally integrable. -/

noncomputable section
open Set MeasureTheory

namespace LipschitzHilbert

theorem positiveConvolution_joint_integrable {f : ℝ → ℝ} (hf : Measurable f)
    {C l r : ℝ} (_hC : 0 ≤ C) (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r)
    (hf0 : ∀ s, 0 ≤ f s) (hbound : ∀ s, f s ≤ C) (u : ℝ) :
    Integrable (fun p : ℝ × ℝ => lineKernel l (p.2-p.1) * f p.1)
      (volume.prod (volume.restrict (Icc (u-r) (u+r)))) := by
  let μ := volume.restrict (Icc (u-r) (u+r))
  have hm : Measurable (fun p : ℝ × ℝ => lineKernel l (p.2-p.1) * f p.1) :=
    ((lineKernel_continuous l).measurable.comp (measurable_snd.sub measurable_fst)).mul
      (hf.comp measurable_fst)
  have hpart (s : ℝ) : Integrable (fun x => lineKernel l (x-s) * f s) μ :=
    ((lineKernel_integrable l s hl).mul_const _).restrict
  have hinner (s : ℝ) : (∫ x, ‖lineKernel l (x-s) * f s‖ ∂μ) ≤
      (C * (1024 * Real.pi)) * lineEnvelope u r 2 s := by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (lineKernel_nonneg _ _ hl) (hf0 s))]
    rw [integral_mul_const]
    calc
      _ ≤ ((1024 * Real.pi) * lineEnvelope u r 2 s) * f s :=
        mul_le_mul_of_nonneg_right (local_lineKernel_integral l u r s hl hr hlr) (hf0 s)
      _ ≤ ((1024 * Real.pi) * lineEnvelope u r 2 s) * C :=
        mul_le_mul_of_nonneg_left (hbound s)
          (mul_nonneg (by positivity) (lineEnvelope_nonneg _ _ _ _))
      _ = _ := by ring
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall hpart, ?_⟩
  apply ((integrable_lineEnvelope u r hr (by decide : 1 ≤ 2)).const_mul
    (C * (1024 * Real.pi))).mono' hm.aestronglyMeasurable.norm.integral_prod_right'
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  exact hinner s

theorem positiveConvolution_interval_integrable {f : ℝ → ℝ} (hf : Measurable f)
    {C l r : ℝ} (hC : 0 ≤ C) (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r)
    (hf0 : ∀ s, 0 ≤ f s) (hbound : ∀ s, f s ≤ C) (u : ℝ) :
    IntegrableOn (positiveConvolution l f) (Icc (u-r) (u+r)) :=
  (positiveConvolution_joint_integrable hf hC hl hr hlr hf0 hbound u).integral_prod_right

theorem integral_positiveConvolution_interval {f : ℝ → ℝ} (hf : Measurable f)
    {C l r : ℝ} (hC : 0 ≤ C) (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r)
    (hf0 : ∀ s, 0 ≤ f s) (hbound : ∀ s, f s ≤ C) (u : ℝ) :
    (∫ x in Icc (u-r) (u+r), positiveConvolution l f x) =
      ∫ s, f s * (∫ x in Icc (u-r) (u+r), lineKernel l (x-s)) := by
  have h := integral_integral_swap (f := fun s x => lineKernel l (x-s) * f s)
    (μ := volume) (ν := volume.restrict (Icc (u-r) (u+r)))
    (positiveConvolution_joint_integrable hf hC hl hr hlr hf0 hbound u)
  unfold positiveConvolution
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [integral_mul_const, mul_comm]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PositiveConvolutionOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local Lipschitz continuity of the actual error convolution, obtained
by an integrable bound for kernel translations. -/

noncomputable section
open Set MeasureTheory

namespace LipschitzHilbert

theorem positiveConvolution_oscillation {f : ℝ → ℝ} (hf : Measurable f)
    {C l : ℝ} (_hC : 0 ≤ C) (hl : 0 < l) (hbound : ∀ s, ‖f s‖ ≤ C)
    (x y : ℝ) (hxy : |x-y| ≤ 2*l) :
    |positiveConvolution l f x - positiveConvolution l f y| ≤
      ((60 * Real.pi * C) / l) * |x-y| := by
  have hm : Integrable (fun s => ((C * (60/l^2)) * |x-y|) * lineEnvelope x l 1 s) :=
    (integrable_lineEnvelope_one x l hl).const_mul _
  have hp (s : ℝ) : ‖lineKernel l (x-s) * f s - lineKernel l (y-s) * f s‖ ≤
      ((C * (60/l^2)) * |x-y|) * lineEnvelope x l 1 s := by
    rw [← sub_mul, norm_mul, Real.norm_eq_abs]
    have h := mul_le_mul (lineKernel_translation_bound l s x y hl hxy) (hbound s)
      (norm_nonneg _) (mul_nonneg (by positivity : 0 ≤ (60/l^2) * |x-y|)
        (lineEnvelope_nonneg _ _ _ _))
    have heq : lineEnvelope s l 1 x = lineEnvelope x l 1 s := by
      simp only [lineEnvelope, div_pow, sub_sq_comm]
    rw [heq] at h
    apply h.trans_eq
    ring
  rw [positiveConvolution, positiveConvolution,
    ← integral_sub (positiveConvolution_integrable_at hf hl hbound x)
      (positiveConvolution_integrable_at hf hl hbound y), ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ s, ((C * (60/l^2)) * |x-y|) * lineEnvelope x l 1 s :=
      norm_integral_le_of_norm_le hm (Filter.Eventually.of_forall hp)
    _ = ((C * (60/l^2)) * |x-y|) * (Real.pi*l) := by
      rw [integral_const_mul, integral_lineEnvelope_one x l hl]
    _ = _ := by field_simp

theorem positiveConvolution_continuous {f : ℝ → ℝ} (hf : Measurable f)
    {C l : ℝ} (hC : 0 ≤ C) (hl : 0 < l) (hbound : ∀ s, ‖f s‖ ≤ C) :
    Continuous (positiveConvolution l f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [Metric.continuousAt_iff]
  intro ε hε
  let A := (60 * Real.pi * C) / l
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨min l (ε/(A+1)), lt_min hl (div_pos hε (by positivity)), ?_⟩
  intro y hy
  have hdist : |y-x| < min l (ε/(A+1)) := by simpa only [Real.dist_eq] using hy
  have hsmall : |y-x| ≤ 2*l := by linarith [lt_of_lt_of_le hdist (min_le_left _ _)]
  have h := positiveConvolution_oscillation hf hC hl hbound y x hsmall
  have he : (A+1)*|y-x| < ε := by
    have h := (lt_div_iff₀ (by positivity : 0 < A+1)).mp
      (lt_of_lt_of_le hdist (min_le_right _ _))
    nlinarith
  rw [Real.dist_eq]
  change |positiveConvolution l f y - positiveConvolution l f x| < ε
  change _ ≤ A*|y-x| at h
  nlinarith [abs_nonneg (y-x)]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LongPositiveConvolution
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform long-scale oscillation of the actual positive error majorant. -/

noncomputable section
open Set
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem long_positiveConvolution_oscillation {N : ℕ}
    (f : Fin N → ℝ → ℝ) (hf : ∀ j, Measurable (f j)) {C L : ℝ}
    (hC : 0 ≤ C) (hL : 0 < L) (hbound : ∀ j s, ‖f j s‖ ≤ C)
    (u r : ℝ) (hr : 0 < r) {x y : ℝ}
    (hx : x ∈ Icc (u-r) (u+r)) (hy : y ∈ Icc (u-r) (u+r)) :
    |(∑ j : Fin N, if r < L / (2 : ℝ)^j.val then
      positiveConvolution (L / (2 : ℝ)^j.val) (f j) x else 0) -
      (∑ j : Fin N, if r < L / (2 : ℝ)^j.val then
      positiveConvolution (L / (2 : ℝ)^j.val) (f j) y else 0)| ≤
      240 * Real.pi * C := by
  let len := fun j : Fin N => L / (2 : ℝ)^j.val
  have hlen (j : Fin N) : 0 < len j := by dsimp [len]; positivity
  have hdist : |x-y| ≤ 2*r := abs_le.mpr ⟨by linarith [hx.1,hy.2], by linarith [hx.2,hy.1]⟩
  have heq : (∑ j : Fin N, if r < len j then
      ((60 * Real.pi * C) / len j) * |x-y| else 0) =
      ((60 * Real.pi * C) * |x-y|) * ∑ j : Fin N, if r < len j then (len j)⁻¹ else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : r < len j <;> simp only [hj, ite_true, if_true, ite_false, if_false, mul_zero]
    rw [div_eq_mul_inv]
    ring
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin N, |(if r < len j then positiveConvolution (len j) (f j) x else 0) -
        (if r < len j then positiveConvolution (len j) (f j) y else 0)| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le (s := Finset.univ)
        (f := fun j : Fin N => (if r < len j then positiveConvolution (len j) (f j) x else 0) -
          (if r < len j then positiveConvolution (len j) (f j) y else 0))
    _ ≤ ∑ j : Fin N, if r < len j then ((60 * Real.pi * C) / len j) * |x-y| else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : r < len j
      · simp only [ite_eq_left hj]
        exact positiveConvolution_oscillation (hf j) hC (hlen j) (hbound j) x y (by linarith)
      · simp only [ite_eq_right hj, sub_zero, abs_zero, le_refl]
    _ = _ := heq
    _ ≤ ((60 * Real.pi * C) * (2*r)) * (2/r) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hdist (by positivity))
        (sum_long_dyadic_reciprocals N L r hL hr)
        (Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)) (by positivity)
    _ = _ := by field_simp; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ShortPositiveConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Short-scale convolution control by the sum of the actual source
functions before integration. This avoids a factor counting the scales. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem short_positiveConvolution_integral {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (len : ι → ℝ) (hlen : ∀ j, 0 < len j)
    (hf : ∀ j, Measurable (f j)) (hf0 : ∀ j s, 0 ≤ f j s)
    {M : ℝ} (hM : 0 ≤ M) (hsum : ∀ s, ∑ j, f j s ≤ M)
    (u r : ℝ) (hr : 0 < r) :
    (∫ x in Icc (u-r) (u+r),
      ∑ j, if len j ≤ r then positiveConvolution (len j) (f j) x else 0) ≤
      (1024 * Real.pi ^ 2) * M * r := by
  have hbound (j : ι) (s : ℝ) : f j s ≤ M :=
    (Finset.single_le_sum (fun i _ => hf0 i s) (Finset.mem_univ j)).trans (hsum s)
  let H := fun j s => if len j ≤ r then
    f j s * (∫ x in Icc (u-r) (u+r), lineKernel (len j) (x-s)) else 0
  have hH (j : ι) : Integrable (H j) := by
    by_cases hj : len j ≤ r
    · have hi := (positiveConvolution_joint_integrable (hf j) hM (hlen j) hr hj (hf0 j) (hbound j) u).integral_prod_left
      apply hi.congr
      filter_upwards [] with s
      change (∫ x in Icc (u-r) (u+r), lineKernel (len j) (x-s) * f j s) = H j s
      dsimp only [H]
      rw [ite_eq_left hj, integral_mul_const, mul_comm]
    · simp only [H, ite_eq_right hj]
      exact integrable_zero _ _ _
  have hG (j : ι) : IntegrableOn
      (fun x => if len j ≤ r then positiveConvolution (len j) (f j) x else 0) (Icc (u-r) (u+r)) := by
    by_cases hj : len j ≤ r
    · simpa only [ite_eq_left hj] using
        positiveConvolution_interval_integrable (hf j) hM (hlen j) hr hj (hf0 j) (hbound j) u
    · simp only [ite_eq_right hj]
      exact integrable_zero _ _ _
  have heq (j : ι) : (∫ x in Icc (u-r) (u+r),
      if len j ≤ r then positiveConvolution (len j) (f j) x else 0) = ∫ s, H j s := by
    by_cases hj : len j ≤ r
    · simp only [ite_eq_left hj, H]
      exact integral_positiveConvolution_interval (hf j) hM (hlen j) hr hj (hf0 j) (hbound j) u
    · simp only [ite_eq_right hj, H, integral_zero]
  have hpoint (s : ℝ) : (∑ j, H j s) ≤
      ((1024 * Real.pi) * M) * lineEnvelope u r 2 s := by
    have hpart : (∑ j, if len j ≤ r then f j s else 0) ≤ M := by
      apply le_trans _ (hsum s)
      apply Finset.sum_le_sum
      intro j _
      split_ifs <;> simp only [le_refl, hf0]
    calc
      _ ≤ ∑ j, ((1024 * Real.pi) * lineEnvelope u r 2 s) *
          (if len j ≤ r then f j s else 0) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : len j ≤ r
        · simp only [H, ite_eq_left hj]
          exact (mul_le_mul_of_nonneg_left
            (local_lineKernel_integral (len j) u r s (hlen j) hr hj) (hf0 j s)).trans_eq (mul_comm _ _)
        · simp only [H, ite_eq_right hj, mul_zero, le_refl]
      _ = ((1024 * Real.pi) * lineEnvelope u r 2 s) *
          ∑ j, if len j ≤ r then f j s else 0 := by rw [Finset.mul_sum]
      _ ≤ ((1024 * Real.pi) * lineEnvelope u r 2 s) * M :=
        mul_le_mul_of_nonneg_left hpart (mul_nonneg (by positivity) (lineEnvelope_nonneg _ _ _ _))
      _ = _ := by ring
  rw [integral_finsetSum _ (fun j _ => hG j)]
  simp_rw [heq]
  rw [← integral_finsetSum _ (fun j _ => hH j)]
  calc
    _ ≤ ∫ s, ((1024 * Real.pi) * M) * lineEnvelope u r 2 s :=
      integral_mono (integrable_finsetSum _ (fun j _ => hH j))
        ((integrable_lineEnvelope u r hr (by decide : 1 ≤ 2)).const_mul _) hpoint
    _ = ((1024 * Real.pi) * M) * ∫ s, lineEnvelope u r 2 s := integral_const_mul _ _
    _ ≤ ((1024 * Real.pi) * M) * (Real.pi*r) :=
      mul_le_mul_of_nonneg_left (integral_lineEnvelope_le u r hr (by decide : 1 ≤ 2)) (by positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VariationLineBMO
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Applying the interval John--Nirenberg theorem to a finite packet
variation, using the actual short/long decomposition on each cell. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert.FiniteLineGrid

theorem continuous_integrable_cell (g : FiniteLineGrid) {f : ℝ → ℝ}
    (hf : Continuous f) (level i : ℕ) : IntegrableOn f (g.cell level i) := by
  unfold cell
  exact hf.continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PositiveErrorMajorant
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual positive convolution majorant for the error terms. Source
size and source-sum bounds remain explicit; BMO is derived for this
majorant rather than assumed for every function it dominates. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

namespace LineErrorSources

attribute [local instance] Classical.propDecidable

variable {N : ℕ}

theorem length_pos (P : LineErrorSources N) (j : Fin N) : 0 < P.length j := by
  exact div_pos P.topLength_pos (pow_pos (by norm_num) _)

theorem source_norm_bound (P : LineErrorSources N) (j : Fin N) (s : ℝ) :
    ‖P.source j s‖ ≤ P.sourceBound := by
  rw [Real.norm_eq_abs, abs_of_nonneg (P.source_nonneg j s)]
  exact P.source_bound j s

theorem term_nonneg (P : LineErrorSources N) (j : Fin N) (x : ℝ) : 0 ≤ P.term j x :=
  positiveConvolution_nonneg (P.length_pos j) (P.source_nonneg j) x

theorem term_continuous (P : LineErrorSources N) (j : Fin N) : Continuous (P.term j) :=
  positiveConvolution_continuous (P.measurable_source j) P.sourceBound_nonneg (P.length_pos j) (P.source_norm_bound j)

theorem majorant_nonneg (P : LineErrorSources N) (x : ℝ) : 0 ≤ P.majorant x :=
  Finset.sum_nonneg (fun j _ => P.term_nonneg j x)

theorem majorant_continuous (P : LineErrorSources N) : Continuous P.majorant :=
  continuous_finsetSum _ (fun j _ => P.term_continuous j)

theorem shortPart_nonneg (P : LineErrorSources N) (r x : ℝ) : 0 ≤ P.shortPart r x :=
  Finset.sum_nonneg (fun j _ => by split_ifs; exact P.term_nonneg j x; exact le_rfl)

theorem shortPart_continuous (P : LineErrorSources N) (r : ℝ) : Continuous (P.shortPart r) := by
  apply continuous_finsetSum
  intro j _
  by_cases hj : P.length j ≤ r
  · simpa only [ite_eq_left hj] using P.term_continuous j
  · simp only [ite_eq_right hj]
    exact continuous_const

theorem longPart_continuous (P : LineErrorSources N) (r : ℝ) : Continuous (P.longPart r) := by
  apply continuous_finsetSum
  intro j _
  by_cases hj : r < P.length j
  · simpa only [ite_eq_left hj] using P.term_continuous j
  · simp only [ite_eq_right hj]
    exact continuous_const

theorem majorant_split (P : LineErrorSources N) (r x : ℝ) :
    P.majorant x = P.shortPart r x + P.longPart r x := by
  unfold majorant shortPart longPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : P.length j ≤ r
  · simp only [ite_eq_left hj, ite_eq_right (not_lt.mpr hj), add_zero]
  · simp only [ite_eq_right hj, ite_eq_left (lt_of_not_ge hj), zero_add]

theorem shortPart_integral (P : LineErrorSources N) (u r : ℝ) (hr : 0 < r) :
    (∫ x in Icc (u-r) (u+r), P.shortPart r x) ≤ P.meanConstant * r :=
  short_positiveConvolution_integral P.source P.length P.length_pos P.measurable_source
    P.source_nonneg P.sumBound_nonneg P.source_sum u r hr

theorem longPart_oscillation (P : LineErrorSources N) (u r : ℝ) (hr : 0 < r)
    {x y : ℝ} (hx : x ∈ Icc (u-r) (u+r)) (hy : y ∈ Icc (u-r) (u+r)) :
    |P.longPart r x - P.longPart r y| ≤ P.oscillationConstant :=
  long_positiveConvolution_oscillation P.source P.measurable_source P.sourceBound_nonneg
    P.topLength_pos P.source_norm_bound u r hr hx hy

theorem majorant_mean_oscillation (P : LineErrorSources N) (g : FiniteLineGrid) :
    g.HasFullMeanOscillationBound P.majorant (2 * P.meanConstant + P.oscillationConstant) := by
  intro level i _
  let r := g.meshWidth level / 2
  let u := g.origin + g.meshWidth level * i + r
  have hr : 0 < r := half_pos (g.meshWidth_pos level)
  have hcell : g.cell level i = Ico (u-r) (u+r) := by
    dsimp [FiniteLineGrid.cell,u,r]
    congr 1 <;> ring
  have hs := g.continuous_integrable_cell (P.shortPart_continuous r) level i
  have hl := g.continuous_integrable_cell (P.longPart_continuous r) level i
  have hshort : (∫ x in g.cell level i, ‖P.shortPart r x‖) ≤
      P.meanConstant * (volume.restrict (g.cell level i)).real univ := by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (P.shortPart_nonneg r _)]
    rw [g.cell_mass, hcell, ← integral_Icc_eq_integral_Ico]
    apply (P.shortPart_integral u r hr).trans
    have hK : 0 ≤ P.meanConstant := by
      have := P.sumBound_nonneg
      unfold meanConstant
      positivity
    exact mul_le_mul_of_nonneg_left (by dsimp [r]; linarith [g.meshWidth_pos level]) hK
  have hlong : ∀ᵐ x ∂volume.restrict (g.cell level i), ∀ᵐ y ∂volume.restrict (g.cell level i),
      ‖P.longPart r x - P.longPart r y‖ ≤ P.oscillationConstant := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    rw [hcell] at hx hy
    simpa only [Real.norm_eq_abs] using P.longPart_oscillation u r hr
      (Ico_subset_Icc_self hx) (Ico_subset_Icc_self hy)
  have h := short_long_mean_oscillation (volume.restrict (g.cell level i))
    (P.shortPart r) (P.longPart r) hs hl (by rw [g.cell_mass]; exact g.meshWidth_pos level) hshort hlong
  simp_rw [← P.majorant_split r] at h
  simpa only [Real.norm_eq_abs, g.cellMean_eq_integralAverage, g.cell_mass] using h

end LineErrorSources
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rounded dyadic parameters in the manuscript. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert.SourceParameters

theorem log_step_bounds {L : ℝ} (hL : 0 ≤ L) :
    L ^ (7 / 10 : ℝ) ≤ Real.log (step L) ∧
      Real.log (step L) ≤ L ^ (7 / 10 : ℝ) + 2 * Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr : 0 ≤ L ^ (7 / 10 : ℝ) / (2 * Real.log 2) := by positivity
  have hlo := Nat.le_ceil (L ^ (7 / 10 : ℝ) / (2 * Real.log 2))
  have hhi := (Nat.ceil_lt_add_one hr).le
  rw [step, Real.log_pow, stepExponent, Nat.cast_mul, Nat.cast_ofNat]
  constructor
  · have h := mul_le_mul_of_nonneg_right hlo (show 0 ≤ 2 * Real.log 2 by positivity)
    have heq : L ^ (7 / 10 : ℝ) / (2 * Real.log 2) * (2 * Real.log 2) =
        L ^ (7 / 10 : ℝ) := div_mul_cancel₀ _ (by positivity)
    rw [heq] at h
    nlinarith
  · have h := mul_le_mul_of_nonneg_right hhi (show 0 ≤ 2 * Real.log 2 by positivity)
    have heq : (L ^ (7 / 10 : ℝ) / (2 * Real.log 2) + 1) * (2 * Real.log 2) =
        L ^ (7 / 10 : ℝ) + 2 * Real.log 2 := by
      rw [add_mul, div_mul_cancel₀ _ (by positivity), one_mul]
    rw [heq] at h
    nlinarith

theorem log_branching_le {L : ℝ} (hL : 0 ≤ L) :
    Real.log (branching L) ≤
      (Real.log L ^ 2 + 1) * (L ^ (7 / 10 : ℝ) + 2 * Real.log 2) := by
  rw [branching, Real.log_pow]
  have hK : (blockCount L : ℝ) ≤ Real.log L ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (sq_nonneg (Real.log L))).le
  exact mul_le_mul hK (log_step_bounds hL).2
    (Real.log_nonneg (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))) (by positivity)

/-- The actual rounded dyadic branching satisfies the scale separation
`B^100 ≤ exp(L^0.9)` eventually, with no real-valued stand-in for `B`. -/
theorem eventually_branching_separation :
    ∀ᶠ L : ℝ in atTop, branching L ^ 100 ≤ Real.exp (L ^ (9 / 10 : ℝ)) := by
  have hlog := isLittleO_log_rpow_rpow_atTop (r := 2) (s := 1 / 5) (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)).eventually_ge_atTop (2 * Real.log 2),
    hlog.bound (by norm_num : (0 : ℝ) < 1 / 400)] with L hL hlogL hpow hsmall
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp7 : 0 ≤ L ^ (7 / 10 : ℝ) := Real.rpow_nonneg hL0.le _
  have hp2 : 0 ≤ L ^ (1 / 5 : ℝ) := Real.rpow_nonneg hL0.le _
  have hlogsq : 1 ≤ Real.log L ^ 2 := by nlinarith
  rw [Real.rpow_two] at hsmall
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log L)),
    abs_of_nonneg hp2] at hsmall
  have hcrude : Real.log (branching L) ≤ 4 * L ^ (7 / 10 : ℝ) * Real.log L ^ 2 := by
    apply (log_branching_le hL0.le).trans
    nlinarith [mul_le_mul (show Real.log L ^ 2 + 1 ≤ 2 * Real.log L ^ 2 by linarith)
      (show L ^ (7 / 10 : ℝ) + 2 * Real.log 2 ≤ 2 * L ^ (7 / 10 : ℝ) by linarith)
      (by positivity : 0 ≤ L ^ (7 / 10 : ℝ) + 2 * Real.log 2)
      (by positivity : 0 ≤ 2 * Real.log L ^ 2)]
  have hpower : L ^ (7 / 10 : ℝ) * L ^ (1 / 5 : ℝ) = L ^ (9 / 10 : ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hbound : 100 * Real.log (branching L) ≤ L ^ (9 / 10 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (by norm_num : (0 : ℝ) ≤ 400) hp7)
    nlinarith
  calc
    branching L ^ 100 = Real.exp (100 * Real.log (branching L)) := by
      have heq : Real.log (branching L ^ (100 : ℕ)) = (100 : ℝ) * Real.log (branching L) := by
        simpa only [Nat.cast_ofNat] using (Real.log_pow (branching L) 100)
      rw [← heq, Real.exp_log (pow_pos (branching_pos L) _)]
    _ ≤ Real.exp (L ^ (9 / 10 : ℝ)) := Real.exp_le_exp.mpr hbound

end LipschitzHilbert.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ErrorSourceBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of the line error data from the manuscript's actual
two-coordinate direction profile and common vertical averaging kernel. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem actualErrorSources_log_sumBound {N : ℕ} (J E : ℕ) (direction : ℝ × ℝ → ℝ)
    (hdirection : Measurable direction) (t a c C' A topLength W y : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hA : 0 ≤ A)
    (hC : C' ≤ c*(2 : ℝ)^J) (hL : 0 < topLength) (hW : 0 < W) :
    (actualErrorSources (N := N) J E direction hdirection t a c C' A topLength W y ha hc hA hC hL hW).sumBound =
      (A * ((J+1 : ℕ)+4*c+(4/Real.log 2)*Real.log ((2 : ℝ)^E))) * Real.pi := by
  change (A*((J+4*E+1 : ℕ)+4*c))*Real.pi = _
  rw [Real.log_pow]
  push_cast
  field_simp
  ring

theorem source_branching_eq_two_pow (L : ℝ) :
    SourceParameters.branching L =
      (2 : ℝ)^(SourceParameters.stepExponent L * SourceParameters.blockCount L) := by
  simp only [SourceParameters.branching, SourceParameters.step, pow_mul]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarPositiveConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive planar kernel in coordinates (x,Y), and its exact
factorization into the two line convolutions used for concentration. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

theorem planarPositiveConvolution_integrable (l W : ℝ) (f : ℝ × ℝ → ℝ)
    (hf : Measurable f) (hl : 0 < l) (hW : 0 < W) {C : ℝ}
    (hbound : ∀ z, ‖f z‖ ≤ C) (x y : ℝ) :
    Integrable (fun z : ℝ × ℝ => (lineKernel l (x-z.1) * lineKernel W (y-z.2)) * f z) := by
  have hx : Integrable (fun s => lineKernel l (x-s)) := by
    simp_rw [lineKernel_sub_comm l x]
    exact lineKernel_integrable l x hl
  have hy : Integrable (fun s => lineKernel W (y-s)) := by
    simp_rw [lineKernel_sub_comm W y]
    exact lineKernel_integrable W y hW
  exact (hx.mul_prod hy).mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

theorem planarPositiveConvolution_eq_iterated (l W : ℝ) (f : ℝ × ℝ → ℝ)
    (hf : Measurable f) (hl : 0 < l) (hW : 0 < W) {C : ℝ}
    (hbound : ∀ z, ‖f z‖ ≤ C) (x y : ℝ) :
    planarPositiveConvolution l W f x y =
      positiveConvolution l (fun s => positiveConvolution W (fun t => f (s,t)) y) x := by
  unfold planarPositiveConvolution
  rw [Measure.volume_eq_prod, integral_prod _ (planarPositiveConvolution_integrable l W f hf hl hW hbound x y)]
  simp_rw [mul_assoc, integral_const_mul]
  rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ActualErrorConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact planar convolution interpretation of each constructed line
error source, including scalar normalization. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

theorem planarPositiveConvolution_const_mul (l W c : ℝ) (f : ℝ × ℝ → ℝ) (x y : ℝ) :
    planarPositiveConvolution l W (fun z => c*f z) x y =
      c * planarPositiveConvolution l W f x y := by
  unfold planarPositiveConvolution
  simp_rw [mul_left_comm _ c, integral_const_mul]

theorem actualErrorSources_term_eq {N : ℕ} (J E : ℕ) (direction : ℝ × ℝ → ℝ)
    (hdirection : Measurable direction) (t a c C' A topLength W y : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hA : 0 ≤ A)
    (hC : C' ≤ c*(2:ℝ)^J) (hL : 0 < topLength) (hW : 0 < W) (j : Fin N) (x : ℝ) :
    (actualErrorSources J E direction hdirection t a c C' A topLength W y ha hc hA hC hL hW).term j x =
      planarPositiveConvolution (topLength/(2:ℝ)^j.val) W
        (fun p => A*errorSourceProfile c (C'*((2:ℝ)^E)^4)
          (a*(2:ℝ)^j.val) |direction p-t|) x y := by
  have hf : Measurable (fun p => A*errorSourceProfile c (C'*((2:ℝ)^E)^4)
      (a*(2:ℝ)^j.val) |direction p-t|) := by
    apply Measurable.const_mul
    apply errorSourceProfile_measurable
    simpa only [Real.norm_eq_abs] using (hdirection.sub_const t).norm
  have hb (p : ℝ × ℝ) : ‖A*errorSourceProfile c (C'*((2:ℝ)^E)^4)
      (a*(2:ℝ)^j.val) |direction p-t|‖ ≤ A*(1+c) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA
      (errorSourceProfile_nonneg _ _ _ _ (mul_pos ha (pow_pos (by norm_num) _)) (abs_nonneg _)))]
    exact mul_le_mul_of_nonneg_left (errorSourceProfile_bound _ _ _ _ hc
      (mul_pos ha (pow_pos (by norm_num) _)) (abs_nonneg _)) hA
  exact (planarPositiveConvolution_eq_iterated _ _ _ hf
    (div_pos hL (pow_pos (by norm_num) _)) hW hb x y).symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MultiplierError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular multiplier error is bounded by the actual annulus-plus-
small-angle-ratio source from the manuscript. -/

noncomputable section

namespace LipschitzHilbert

theorem multiplierError_bound (b : ℝ → ℂ) (t d c R M L u : ℝ)
    (hd : 0 < d) (_hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hb : ∀ s, ‖b s‖ ≤ M)
    (hnear : |u-t| ≤ c*d → ‖b u-b t‖ ≤ L * (|u-t|/d))
    (hfar : R*d < |u-t| → b u = 0) :
    ‖multiplierError b t d u‖ ≤ (2*M+L) * errorSourceProfile c R d |u-t| := by
  have hA : 0 ≤ 2*M+L := by positivity
  have hprofile := errorSourceProfile_nonneg c R d |u-t| hd (abs_nonneg _)
  by_cases hn : |u-t| ≤ c*d
  · have hsel : |u-t| ≤ d := hn.trans (by nlinarith)
    have hratio : 0 ≤ |u-t|/d := div_nonneg (abs_nonneg _) hd.le
    have hp : |u-t|/d ≤ errorSourceProfile c R d |u-t| := by
      unfold errorSourceProfile
      rw [ite_eq_left hn]
      split_ifs <;> linarith
    calc
      _ = ‖b u-b t‖ := by rw [multiplierError, ite_eq_left hsel]
      _ ≤ L * (|u-t|/d) := hnear hn
      _ ≤ (2*M+L) * (|u-t|/d) := mul_le_mul_of_nonneg_right (by linarith) hratio
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hA
  · by_cases hf : |u-t| ≤ R*d
    · have hp : errorSourceProfile c R d |u-t| = 1 := by
        unfold errorSourceProfile
        rw [ite_eq_left ⟨(lt_of_not_ge hn).le,hf⟩, ite_eq_right hn, add_zero]
      rw [hp,mul_one]
      unfold multiplierError
      split_ifs
      · exact (norm_sub_le _ _).trans (by linarith [hb u,hb t])
      · simpa only [sub_zero] using (hb u).trans (by linarith)
    · have hfar' : R*d < |u-t| := lt_of_not_ge hf
      have hsel : ¬ |u-t| ≤ d := by nlinarith
      rw [multiplierError, hfar hfar', ite_eq_right hsel, sub_self, norm_zero]
      exact mul_nonneg hA hprofile

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TwoPointEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-point decay estimate behind the positive error convolution.
Only fixed exponents six and three are needed. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem envelope_triangle_base (s l x y : ℝ) :
    1 + ((x-y)/l)^2 ≤ 2 * (1+((x-s)/l)^2) * (1+((y-s)/l)^2) := by
  have heq : (x-y)/l = (x-s)/l - (y-s)/l := by ring
  rw [heq]
  nlinarith [sq_nonneg ((x-s)/l + (y-s)/l),
    sq_nonneg (((x-s)/l)*((y-s)/l))]

theorem envelope_three_product (s l x y : ℝ) :
    lineEnvelope s l 3 x * lineEnvelope s l 3 y ≤ 8 * lineEnvelope y l 3 x := by
  let A := 1+((x-s)/l)^2
  let B := 1+((y-s)/l)^2
  let D := 1+((x-y)/l)^2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have h := pow_le_pow_left₀ hD.le (envelope_triangle_base s l x y) 3
  change (A^3)⁻¹ * (B^3)⁻¹ ≤ 8 * (D^3)⁻¹
  rw [← mul_inv, ← one_div, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hA 3) (pow_pos hB 3)) (pow_pos hD 3)).mpr
  simpa only [mul_pow, show (2:ℝ)^3=8 by norm_num, one_mul, mul_assoc] using h

theorem envelope_six_product (s l x y : ℝ) :
    lineEnvelope s l 6 x * lineEnvelope s l 6 y ≤
      8 * lineEnvelope y l 3 x * lineEnvelope s l 3 x := by
  have hsmall : lineEnvelope s l 3 y ≤ 1 := by
    simpa only [lineEnvelope, pow_zero, inv_one] using
      lineEnvelope_antitone s l y (by decide : 0 ≤ 3)
  have hpow (z : ℝ) : lineEnvelope s l 6 z = lineEnvelope s l 3 z ^ 2 := by
    unfold lineEnvelope
    rw [show (6:ℕ) = 3*2 from rfl, pow_mul, inv_pow]
  have heq : lineEnvelope s l 6 x * lineEnvelope s l 6 y =
      (lineEnvelope s l 3 x * lineEnvelope s l 3 y) *
        (lineEnvelope s l 3 x * lineEnvelope s l 3 y) := by
    rw [hpow x, hpow y]
    ring
  rw [heq]
  have h1 := envelope_three_product s l x y
  have h2 : lineEnvelope s l 3 x * lineEnvelope s l 3 y ≤ lineEnvelope s l 3 x := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall (lineEnvelope_nonneg _ _ _ _)
  calc
    _ ≤ (8 * lineEnvelope y l 3 x) * lineEnvelope s l 3 x :=
      mul_le_mul h1 h2 (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
        (mul_nonneg (by norm_num) (lineEnvelope_nonneg _ _ _ _))
    _ = _ := by ring

theorem two_point_tile_envelope {ι : Type*} [Fintype ι]
    (site : ι → ℤ × ℤ) (hinj : Function.Injective site)
    (a b l W x y x' y' : ℝ) (hl : 0 < l) (hW : 0 < W) :
    (∑ i, (lineEnvelope (a+l*(site i).1) l 6 x * lineEnvelope (b+W*(site i).2) W 6 y) *
      (lineEnvelope (a+l*(site i).1) l 6 x' * lineEnvelope (b+W*(site i).2) W 6 y')) ≤
    (64 * (4 * Real.pi)^2) * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y := by
  have hterm (i : ι) :
      (lineEnvelope (a+l*(site i).1) l 6 x * lineEnvelope (b+W*(site i).2) W 6 y) *
      (lineEnvelope (a+l*(site i).1) l 6 x' * lineEnvelope (b+W*(site i).2) W 6 y') ≤
      (64 * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y) *
      (lineEnvelope (a+l*(site i).1) l 3 x * lineEnvelope (b+W*(site i).2) W 3 y) := by
    have hx := envelope_six_product (a+l*(site i).1) l x x'
    have hy := envelope_six_product (b+W*(site i).2) W y y'
    have h := mul_le_mul hx hy
      (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
      (mul_nonneg (mul_nonneg (by norm_num) (lineEnvelope_nonneg _ _ _ _)) (lineEnvelope_nonneg _ _ _ _))
    first | (convert h using 1 <;> ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))
  calc
    _ ≤ ∑ i, (64 * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y) *
        (lineEnvelope (a+l*(site i).1) l 3 x * lineEnvelope (b+W*(site i).2) W 3 y) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = (64 * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y) *
        ∑ i, lineEnvelope (a+l*(site i).1) l 3 x * lineEnvelope (b+W*(site i).2) W 3 y :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (64 * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y) * (4*Real.pi)^2 :=
      mul_le_mul_of_nonneg_left (injective_tile_lattice_overlap site hinj a b l W x y
        hl.ne' hW.ne' (by decide : 1 ≤ 3) (by decide : 1 ≤ 3))
        (mul_nonneg (mul_nonneg (by norm_num) (lineEnvelope_nonneg _ _ _ _))
          (lineEnvelope_nonneg _ _ _ _))
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_TileEnvelopeKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-point lattice overlap after normalization by tile area. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem tileEnvelope_nonneg (a b l W : ℝ) (n : ℕ) (z : ℝ × ℝ) :
    0 ≤ tileEnvelope a b l W n z :=
  mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)

theorem tileEnvelope_integrable (a b l W : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hl : 0 < l) (hW : 0 < W) : Integrable (tileEnvelope a b l W n) :=
  (integrable_lineEnvelope a l hl hn).mul_prod (integrable_lineEnvelope b W hW hn)

theorem two_point_tile_kernel {ι : Type*} [Fintype ι]
    (site : ι → ℤ × ℤ) (hinj : Function.Injective site)
    (a b l W : ℝ) (hl : 0 < l) (hW : 0 < W) (z z' : ℝ × ℝ) :
    (∑ i, tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6 z *
      tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6 z') / (l*W) ≤
    (64 * (4*Real.pi)^2) * (lineKernel l (z.1-z'.1) * lineKernel W (z.2-z'.2)) := by
  have h := div_le_div_of_nonneg_right
    (two_point_tile_envelope site hinj a b l W z.1 z.2 z'.1 z'.2 hl hW)
    (mul_nonneg hl.le hW.le)
  convert h using 1
  all_goals first | rfl | (rw [lineKernel_shift, lineKernel_shift]; ring)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LatticeCoefficientConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual analyzing coefficients controlled by a common scalar source
satisfy the fixed-scale positive convolution estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LipschitzHilbert

theorem lattice_coefficient_convolution {ι κ : Type*} [Fintype ι] [Fintype κ]
    (site : ι → ℤ × ℤ) (hinj : Function.Injective site) (a b l W : ℝ)
    (hl : 0 < l) (hW : 0 < W) (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (hf0 : ∀ z, 0 ≤ f z) {M : ℝ} (hfb : ∀ z, ‖f z‖ ≤ M)
    (wave : ι → κ → ℝ × ℝ → ℂ) (hw : ∀ i k, Measurable (wave i k))
    (hwf : ∀ i k z, ‖wave i k z‖ ≤
      tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6 z * f z)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (z : ℝ × ℝ) :
    (∑ i, ‖analyzingCoefficient volume (fun _ : ι => l*W) wave g i‖ *
      tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6 z) ≤
      (64 * (4*Real.pi)^2) * planarPositiveConvolution l W f z.1 z.2 := by
  let E := fun i => tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6
  have hEi (i : ι) : Integrable (fun p => E i p * f p) :=
    (tileEnvelope_integrable _ _ _ _ (by decide : 1 ≤ 6) hl hW).mul_bdd
      hf.aestronglyMeasurable (Filter.Eventually.of_forall hfb)
  have hEn (i : ι) (p : ℝ × ℝ) : 0 ≤ E i p := tileEnvelope_nonneg _ _ _ _ _ _
  have hint (i : ι) (k : κ) : Integrable (fun p => g p k * conj (wave i k p)) := by
    have hgm : Measurable (fun p => g p k) :=
      (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
    apply (hEi i).mono' (hgm.mul (continuous_star.measurable.comp (hw i k))).aestronglyMeasurable
    filter_upwards [] with p
    dsimp only [Pi.mul_apply, Function.comp_apply]
    rw [norm_mul, norm_star]
    have hgk := (PiLp.norm_apply_le (g p) k).trans (hg1 p)
    exact (mul_le_mul_of_nonneg_right hgk (norm_nonneg _)).trans
      (by simpa only [one_mul] using hwf i k p)
  have ha (i : ι) : ‖analyzingCoefficient volume (fun _ : ι => l*W) wave g i‖ ≤
      (l*W)⁻¹ * ∫ p, E i p * f p :=
    analyzingCoefficient_norm_le volume (fun _ : ι => l*W) wave g i (fun p => E i p * f p)
      (mul_pos hl hW) (hEi i) (fun p => mul_nonneg (hEn i p) (hf0 p))
      (hint i) hg1 (hwf i)
  have hsumI : Integrable (fun p => ∑ i, (E i z * E i p / (l*W)) * f p) := by
    apply integrable_finsetSum
    intro i _
    convert (hEi i).const_mul (E i z / (l*W)) using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    ring
  have hkerI := planarPositiveConvolution_integrable l W f hf hl hW hfb z.1 z.2
  calc
    _ ≤ ∑ i, ((l*W)⁻¹ * ∫ p, E i p * f p) * E i z :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (ha i) (hEn i z))
    _ = ∫ p, ∑ i, (E i z * E i p / (l*W)) * f p := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro i _
        have heq : (fun p => (E i z * E i p / (l*W)) * f p) =
            (fun p => (E i z / (l*W)) * (E i p * f p)) := by funext p; ring
        rw [heq, integral_const_mul]
        ring
      · intro i _
        convert (hEi i).const_mul (E i z / (l*W)) using 1
        all_goals try with_reducible_and_instances rfl
        funext p
        ring
    _ ≤ ∫ p, (64*(4*Real.pi)^2) *
        ((lineKernel l (z.1-p.1) * lineKernel W (z.2-p.2)) * f p) := by
      apply integral_mono hsumI (hkerI.const_mul _)
      intro p
      have h := mul_le_mul_of_nonneg_right
        (two_point_tile_kernel site hinj a b l W hl hW z p) (hf0 p)
      convert h using 1
      · simp only [Finset.sum_mul, Finset.sum_div]
        rfl
      · ring
    _ = _ := integral_const_mul _ _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularErrorConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-scale convolution majorant for coefficients of the actual
angular multiplier error, including its two-coordinate direction profile. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem angularErrorWave_measurable {ι κ : Type*}
    (b : ι → κ → ℝ → ℂ) (ψ : ι → κ → ℝ × ℝ → ℂ)
    (u : ℝ × ℝ → ℝ) (t d : ℝ)
    (hb : ∀ i k, Measurable (b i k)) (hψ : ∀ i k, Measurable (ψ i k))
    (hu : Measurable u) (i : ι) (k : κ) :
    Measurable (angularErrorWave b ψ u t d i k) := by
  have huabs : Measurable (fun z => |u z-t|) := by
    simpa only [Real.norm_eq_abs] using (hu.sub_const t).norm
  have hsel : MeasurableSet {z | |u z-t| ≤ d} :=
    measurableSet_le huabs measurable_const
  exact ((hb i k |>.comp hu).sub
    (Measurable.ite hsel measurable_const measurable_const)).mul (hψ i k)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ErrorSynthesisVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual error synthesis variation is bounded by its positive
coefficient envelope, then by the constructed error moments. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem norm_diagonalSynthesis_le {Ω ι κ : Type*} [Fintype ι] [Fintype κ]
    (wave : ι → κ → Ω → ℂ) (c : ι → EuclideanSpace ℂ κ) (E : ι → ℝ)
    (z : Ω) {D : ℝ} (hD : 0 ≤ D) (hE : ∀ i, 0 ≤ E i)
    (hw : ∀ i k, ‖wave i k z‖ ≤ D * E i) :
    ‖diagonalSynthesis wave c z‖ ≤ D * ∑ i, ‖c i‖ * E i := by
  have heq : diagonalSynthesis wave c z = ∑ i, WithLp.toLp 2 (fun k => c i k * wave i k z) := by
    ext k
    simp only [diagonalSynthesis, WithLp.ofLp_sum, Finset.sum_apply]
  rw [heq, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  convert diagonal_packet_norm (c i) (fun k => wave i k z) (mul_nonneg hD (hE i)) (hw i) using 1
  all_goals try with_reducible_and_instances rfl
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PolynomialPacket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed polynomial weights preserve the required packet decay and
horizontal derivative bounds, after choosing the original packet order. -/

noncomputable section

namespace LipschitzHilbert

theorem polynomialWeight_derivative (a r x : ℝ) (q : ℕ) (hr : 0 < r) :
    |deriv (polynomialWeight a r q) x| ≤
      (2*(q:ℝ)/r)*polynomialWeight a r q x := by
  cases q with
  | zero =>
    change |deriv (fun _ : ℝ => (1:ℝ)) x| ≤ _
    simp
  | succ q =>
    let t := (x-a)/r
    let B := 1+t^2
    have hB : 0 < B := by dsimp [B]; positivity
    have ht : |t| ≤ B := by dsimp [B]; nlinarith [sq_nonneg (|t|-1), sq_abs t]
    have hd := ((((hasDerivAt_id x).sub_const a).div_const r).pow 2).const_add 1 |>.pow (q+1)
    dsimp only [Pi.pow_apply, id_eq] at hd
    change HasDerivAt (fun y : ℝ => (1+((y-a)/r)^2)^(q+1)) _ x at hd
    have heq : (fun y : ℝ => (1+((y-a)/r)^2)^(q+1)) = polynomialWeight a r (q+1) := by
      funext y
      simp only [polynomialWeight, div_pow]
    rw [heq] at hd
    rw [hd.deriv]
    have habs : |(q+1:ℝ) * B^q * (2*t*(1/r))| =
        (2*(q+1:ℝ)/r)*B^q*|t| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (q+1:ℝ)),
        abs_of_nonneg (pow_nonneg hB.le q), abs_of_pos (by norm_num : (0:ℝ)<2),
        abs_of_pos (by positivity : 0 < 1/r)]
      ring
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, Nat.cast_ofNat] at *
    simp only [Nat.reduceSub, pow_one, polynomialWeight, ← div_pow]
    change |(q+1:ℝ)*B^q*(2*t*(1/r))| ≤ (2*(q+1:ℝ)/r)*B^(q+1)
    rw [habs, pow_succ]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ht
      (show 0 ≤ (2*(q+1:ℝ)/r)*B^q by positivity)

theorem polynomialWeight_mul_envelope (x s a l r : ℝ) (q n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r) (hsa : |s-a| ≤ r) :
    polynomialWeight a r q x * lineEnvelope s l (n+2*q) x ≤
      16^q * lineEnvelope s l n x := by
  have hP := polynomialWeight_one_le a r q x
  have hsq : polynomialWeight a r q x ≤ polynomialWeight a r q x^2 := by nlinarith
  exact (mul_le_mul_of_nonneg_right hsq (lineEnvelope_nonneg _ _ _ _)).trans
    (polynomialWeight_sq_mul_envelope x s a l r q n hl hr hlr hsa)

theorem polynomialLocalization_packet_bound (f : SchwartzMap ℝ ℂ)
    (a r s l C : ℝ) (q n : ℕ) (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r)
    (hsa : |s-a| ≤ r) (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*lineEnvelope s l (n+2*q) x) (x : ℝ) :
    ‖polynomialLocalization a r q f x‖ ≤ (16^q*C)*lineEnvelope s l n x := by
  rw [polynomialLocalization_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ((polynomialWeight_one_le a r q x).trans' (by norm_num))]
  calc
    _ ≤ polynomialWeight a r q x * (C*lineEnvelope s l (n+2*q) x) :=
      mul_le_mul_of_nonneg_left (hf x) (zero_le_one.trans (polynomialWeight_one_le a r q x))
    _ = C*(polynomialWeight a r q x * lineEnvelope s l (n+2*q) x) := by ring
    _ ≤ C*(16^q*lineEnvelope s l n x) := mul_le_mul_of_nonneg_left
      (polynomialWeight_mul_envelope x s a l r q n hl hr hlr hsa) hC
    _ = _ := by ring

theorem polynomialWeight_differentiable (a r : ℝ) (q : ℕ) :
    Differentiable ℝ (polynomialWeight a r q) := by
  unfold polynomialWeight
  fun_prop

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absorb the transverse factor of the top polynomial into fixed packet
decay. The resulting constant is uniform over the reference line. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

theorem vertical_weighted_envelope (y s a W R X : ℝ) (q n : ℕ)
    (hW : 0 < W) (hR : 0 < R) (hWR : W ≤ R) (hs : |s-a| ≤ R) (hX : 0 ≤ X) :
    polynomialWeight a R q y * (X*lineEnvelope s W (n+2*q) y) ≤
      (16^q*X)*lineEnvelope s W n y := by
  have h := mul_le_mul_of_nonneg_left
    (polynomialWeight_mul_envelope y s a W R q n hW hR hWR hs) hX
  first | (convert h using 1 <;> ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))

theorem vertical_weighted_wave (f : SchwartzMap ℝ ℂ)
    (y s a W R X : ℝ) (q n : ℕ)
    (hW : 0 < W) (hR : 0 < R) (hWR : W ≤ R) (hs : |s-a| ≤ R) (hX : 0 ≤ X)
    (x : ℝ) (hf : ‖f x‖ ≤ X*lineEnvelope s W (n+2*q) y) :
    ‖((polynomialWeight a R q y : ℂ) • f) x‖ ≤
      (16^q*X)*lineEnvelope s W n y := by
  rw [smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (zero_le_one.trans (polynomialWeight_one_le a R q y))]
  exact (mul_le_mul_of_nonneg_left hf
    (zero_le_one.trans (polynomialWeight_one_le a R q y))).trans
      (vertical_weighted_envelope y s a W R X q n hW hR hWR hs hX)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_TopWeightedPacket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both factors of a fixed top polynomial can be absorbed into the
original packet orders, uniformly in the horizontal reference line. -/

noncomputable section
open scoped BigOperators
open FourierTransform
open scoped FourierTransform

namespace LipschitzHilbert

theorem topWeightedWave_apply (f : SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q : ℕ) (x : ℝ) :
    topWeightedWave f a r b R y q x =
      (polynomialWeight a r q x * polynomialWeight b R q y : ℝ) * f x := by
  rw [topWeightedWave, polynomialLocalization_apply, smul_apply, smul_eq_mul]
  push_cast
  ring

theorem topWeightedWave_bound (f : SchwartzMap ℝ ℂ)
    (a r b R y s l t W C : ℝ) (q m n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hW : 0 < W) (hR : 0 < R)
    (hlr : l ≤ r) (hWR : W ≤ R) (hs : |s-a| ≤ r) (ht : |t-b| ≤ R) (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*(lineEnvelope s l (m+2*q) x * lineEnvelope t W (n+2*q) y))
    (x : ℝ) :
    ‖topWeightedWave f a r b R y q x‖ ≤
      (16^q*(16^q*C))*(lineEnvelope s l m x * lineEnvelope t W n y) := by
  have hv (z : ℝ) : ‖((polynomialWeight b R q y : ℂ) • f) z‖ ≤
      (16^q*C*lineEnvelope t W n y)*lineEnvelope s l (m+2*q) z := by
    have h := vertical_weighted_wave f y t b W R (C*lineEnvelope s l (m+2*q) z)
      q n hW hR hWR ht (mul_nonneg hC (lineEnvelope_nonneg _ _ _ _)) z
      (by simpa only [mul_assoc] using hf z)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have h := polynomialLocalization_packet_bound
    ((polynomialWeight b R q y : ℂ) • f) a r s l
    (16^q*C*lineEnvelope t W n y) q m hl hr hlr hs
    (mul_nonneg (mul_nonneg (by positivity) hC) (lineEnvelope_nonneg _ _ _ _)) hv x
  convert h using 1
  · rfl
  · ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PolynomialMomentBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put the explicit John--Nirenberg moment expression in the polynomial
form needed when the moment order grows with the manuscript parameter. -/

noncomputable section
open scoped ENNReal

namespace LipschitzHilbert

theorem polynomial_moment_majorant (Q R : ℝ) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (n : ℕ) (hn : 1 ≤ n) :
    (2:ℝ)^n * (7*((n:ℝ)*Q)^n+R^n) ≤ (16*(Q+R+1)*(n:ℝ))^n := by
  let S := Q+R+1
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hA : (n:ℝ)*Q ≤ (n:ℝ)*S := by dsimp [S]; nlinarith
  have hB : R ≤ (n:ℝ)*S := by
    have h := mul_le_mul_of_nonneg_right hnR hS
    dsimp [S] at h ⊢
    nlinarith
  have hAn := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg n) hQ) hA n
  have hBn := pow_le_pow_left₀ hR hB n
  have h8 : (8:ℝ) ≤ 8^n := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 8) hn
  calc
    _ ≤ 2^n * (8*((n:ℝ)*S)^n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ ≤ 2^n * (8^n*((n:ℝ)*S)^n) := by gcongr
    _ = (16*(Q+R+1)*(n:ℝ))^n := by
      rw [← mul_assoc, ← mul_pow, ← mul_pow]
      congr 1
      dsimp [S]
      ring

theorem ennreal_polynomial_moment_majorant (Q R : ℝ) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (n : ℕ) (hn : 1 ≤ n) :
    (2:ℝ≥0∞)^(n:ℝ) * (7*ENNReal.ofReal (((n:ℝ)*Q)^(n:ℝ)) +
      (ENNReal.ofReal R)^(n:ℝ)) ≤ ENNReal.ofReal ((16*(Q+R+1)*(n:ℝ))^n) := by
  have h := ENNReal.ofReal_le_ofReal (polynomial_moment_majorant Q R hQ hR n hn)
  simpa only [Real.rpow_natCast, ENNReal.rpow_natCast,
    ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2^n),
    ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ 7*((n:ℝ)*Q)^n) (pow_nonneg hR n),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 7),
    ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_pow hR,
    ENNReal.ofReal_ofNat] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MomentSuperlevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Use a natural moment at its chosen order to obtain a geometric
exceptional-set bound. No asymptotic or unspecified tail input is assumed. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem quarter_pow_exp (n : ℕ) :
    (1/4:ℝ)^n = Real.exp (-(Real.log 4)*(n:ℝ)) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num),
    Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0), Real.log_one]
  congr 1
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ExponentialThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Select the moment order explicitly to absorb a positive global
prefactor into the prescribed exponential exceptional-area budget. -/

noncomputable section

namespace LipschitzHilbert

theorem quarter_ceil_bound (x : ℝ) :
    (1/4:ℝ)^⌈x / Real.log 4⌉₊ ≤ Real.exp (-x) := by
  rw [quarter_pow_exp]
  apply Real.exp_le_exp.mpr
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hc := (div_le_iff₀ hlog).mp (Nat.le_ceil (x / Real.log 4))
  nlinarith

theorem prefactor_quarter_ceil_bound (M x : ℝ) (hM : 0 < M) :
    M * (1/4:ℝ)^⌈(x+Real.log M) / Real.log 4⌉₊ ≤ Real.exp (-x) := by
  calc
    _ ≤ M * Real.exp (-(x+Real.log M)) :=
      mul_le_mul_of_nonneg_left (quarter_ceil_bound (x+Real.log M)) hM.le
    _ = Real.exp (Real.log M) * Real.exp (-(x+Real.log M)) := by
      rw [Real.exp_log hM]
    _ = Real.exp (-x) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The extra successor guarantees a positive moment order and retains
the requested exponential bound. -/
theorem prefactor_quarter_successor_bound (M x : ℝ) (hM : 0 < M) :
    M * (1/4:ℝ)^(⌈(x+Real.log M) / Real.log 4⌉₊+1) ≤ Real.exp (-x) := by
  calc
    _ ≤ M * (1/4:ℝ)^⌈(x+Real.log M) / Real.log 4⌉₊ := by
      rw [pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/4)
        ⌈(x+Real.log M) / Real.log 4⌉₊]
    _ ≤ _ := prefactor_quarter_ceil_bound M x hM

theorem exponential_moment_order_le (J c L M : ℝ)
    (hJ : 0 ≤ J) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlog : Real.log M ≤ c*L) :
    ((⌈(J*L+Real.log M) / Real.log 4⌉₊+1:ℕ):ℝ) ≤
      ((J+c)/Real.log 4+2)*L := by
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hnum : 0 ≤ J*L+Real.log M :=
    add_nonneg (mul_nonneg hJ (by linarith)) (Real.log_nonneg hM)
  have hceil := Nat.ceil_lt_add_one (div_nonneg hnum h4.le)
  have hdiv : (J*L+Real.log M)/Real.log 4 ≤ ((J+c)/Real.log 4)*L := by
    calc
      _ ≤ (J*L+c*L)/Real.log 4 := div_le_div_of_nonneg_right (by linarith) h4.le
      _ = _ := by ring
  push_cast
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_GlobalExceptionalArea
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the decaying top-box exceptional areas over the entire plane.
This uses the actual summable lattice weight, rather than discarding
the boxes outside the top rectangle. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace LipschitzHilbert

theorem boxVariationWeight_tsum :
    (∑' p : ℤ × ℤ, ENNReal.ofReal (boxVariationWeight p)) ≤
      ENNReal.ofReal ((4*Real.pi)^2) := by
  apply ENNReal.summable.tsum_le_of_sum_le
  intro s
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => (boxVariationWeight_pos p).le)]
  apply ENNReal.ofReal_le_ofReal
  have h := boxVariationWeight_sum (fun p : s => (p : ℤ × ℤ)) Subtype.val_injective
  simpa only [Finset.univ_eq_attach, Finset.sum_attach] using h

theorem global_exceptional_area {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (bad : ℤ × ℤ → Set Ω) (A : ℝ≥0∞)
    (hbad : ∀ p, μ (bad p) ≤ A * ENNReal.ofReal (boxVariationWeight p)) :
    μ (⋃ p, bad p) ≤ A * ENNReal.ofReal ((4*Real.pi)^2) := by
  calc
    _ ≤ ∑' p, μ (bad p) := measure_iUnion_le _
    _ ≤ ∑' p, A * ENNReal.ofReal (boxVariationWeight p) := ENNReal.tsum_le_tsum hbad
    _ = A * ∑' p, ENNReal.ofReal (boxVariationWeight p) := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul' le_rfl boxVariationWeight_tsum

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer horizontal moments through vertical averaging. In applications
the first measure is a fixed expanded vertical interval and the second is
the horizontal line interval. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem lintegral_ofReal_average_swap {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [SFinite μ] [SFinite ν]
    (F : Ω × Ξ → ℝ) (hF : Measurable F)
    (hi : ∀ x, Integrable (fun t => F (t,x)) μ)
    (h0 : ∀ z, 0 ≤ F z) :
    (∫⁻ x, ENNReal.ofReal (⨍ t, F (t,x) ∂μ) ∂ν) =
      (μ Set.univ)⁻¹ * ∫⁻ t, ∫⁻ x, ENNReal.ofReal (F (t,x)) ∂ν ∂μ := by
  simp_rw [ofReal_average (hi _) (Filter.Eventually.of_forall fun t => h0 (t,_)),
    ENNReal.div_eq_inv_mul]
  rw [lintegral_const_mul _ (hF.ennreal_ofReal.lintegral_prod_left)]
  congr 1
  exact (lintegral_lintegral_swap hF.ennreal_ofReal.aemeasurable).symm

theorem verticalSquareEnergy_measurable {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [SFinite μ] (V D : Ω × Ξ → ℝ)
    (hV : Measurable V) (hD : Measurable D) :
    Measurable (fun x => verticalSquareEnergy μ (fun t => V (t,x)) (fun t => D (t,x))) := by
  have h : Measurable (fun x => ∫ t, V (t,x)^2 + D (t,x)^2 ∂μ) :=
    ((hV.pow_const 2).add (hD.pow_const 2)).stronglyMeasurable.integral_prod_left'.measurable
  simpa only [verticalSquareEnergy, average_eq, smul_eq_mul] using
    (h.const_mul (μ.real univ)⁻¹).const_mul 2

theorem verticalSquareEnergy_line_moment {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsFiniteMeasure μ] [NeZero μ] [SFinite ν]
    (V D : Ω × Ξ → ℝ) (hV : Measurable V) (hD : Measurable D) (n : ℕ)
    (hiV : ∀ x, Integrable (fun t => V (t,x)^2) μ)
    (hiD : ∀ x, Integrable (fun t => D (t,x)^2) μ)
    (hi : ∀ x, Integrable (fun t => (V (t,x)^2+D (t,x)^2)^n) μ)
    (hiVn : ∀ x, Integrable (fun t => V (t,x)^(2*n)) μ)
    (hiDn : ∀ x, Integrable (fun t => D (t,x)^(2*n)) μ)
    (C : ℝ≥0∞)
    (hline : ∀ t, (∫⁻ x, ENNReal.ofReal (V (t,x)^(2*n)+D (t,x)^(2*n)) ∂ν) ≤ C) :
    (∫⁻ x, ENNReal.ofReal
      (verticalSquareEnergy μ (fun t => V (t,x)) (fun t => D (t,x)))^n ∂ν) ≤
      (4:ℝ≥0∞)^n * C := by
  have hp (x : Ξ) := averaged_square_moment μ (fun t => V (t,x))
    (fun t => D (t,x)) n (hiV x) (hiD x) (hi x) (hiVn x) (hiDn x)
  have hnonneg (x : Ξ) : 0 ≤ verticalSquareEnergy μ (fun t => V (t,x))
      (fun t => D (t,x)) := by
    apply mul_nonneg (by norm_num)
    exact integral_nonneg (fun t => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hpow (x : Ξ) : ENNReal.ofReal
      (verticalSquareEnergy μ (fun t => V (t,x)) (fun t => D (t,x)))^n ≤
      (4:ℝ≥0∞)^n * ENNReal.ofReal (⨍ t, V (t,x)^(2*n)+D (t,x)^(2*n) ∂μ) := by
    have hfour : ENNReal.ofReal (4:ℝ) = 4 := by norm_num
    rw [← ENNReal.ofReal_pow (hnonneg x), ← hfour, ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 4),
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4^n)]
    exact ENNReal.ofReal_le_ofReal (hp x)
  calc
    _ ≤ ∫⁻ x, (4:ℝ≥0∞)^n * ENNReal.ofReal
        (⨍ t, V (t,x)^(2*n)+D (t,x)^(2*n) ∂μ) ∂ν := lintegral_mono hpow
    _ = (4:ℝ≥0∞)^n * ((μ univ)⁻¹ *
        ∫⁻ t, ∫⁻ x, ENNReal.ofReal (V (t,x)^(2*n)+D (t,x)^(2*n)) ∂ν ∂μ) := by
      rw [lintegral_const_mul' _ _ (by finiteness)]
      congr 1
      apply lintegral_ofReal_average_swap μ ν (fun z => V z^(2*n)+D z^(2*n))
        ((hV.pow_const (2*n)).add (hD.pow_const (2*n))) (fun x => (hiVn x).add (hiDn x))
      intro z
      simpa only [pow_mul] using
        add_nonneg (pow_nonneg (sq_nonneg (V z)) n) (pow_nonneg (sq_nonneg (D z)) n)
    _ ≤ (4:ℝ≥0∞)^n * ((μ univ)⁻¹ * ∫⁻ _t, C ∂μ) := by
      gcongr
      exact hline _
    _ = _ := by
      rw [lintegral_const, mul_comm C (μ univ), ← mul_assoc (μ univ)⁻¹,
        ENNReal.inv_mul_cancel (NeZero.ne (μ univ))
          (measure_ne_top μ univ), one_mul]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NeighborhoodEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single measurable energy can control every member of a finite family
of interval sums throughout a vertical neighborhood. -/

noncomputable section
open MeasureTheory Set

namespace LipschitzHilbert

theorem interval_energy_domination {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a b : ℝ} (hab : a < b)
    (hf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b)))
    (V D : ℝ → ℝ) (hV : ContinuousOn V (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (hbV : ∀ t ∈ Icc a b, ‖f t‖ ≤ V t)
    (hbD : ∀ t ∈ Icc a b, ‖deriv f t‖ ≤ D t)
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖f x‖^2 ≤ verticalSquareEnergy (volume.restrict (Icc a b)) V
      (fun t => (b-a)*D t) := by
  have hm : 0 < b-a := sub_pos.mpr hab
  have hcont : ContinuousOn f (Icc a b) := fun t ht =>
    (hf t ht).continuousAt.continuousWithinAt
  have hiV : IntegrableOn (fun t => V t^2) (Icc a b) volume := (hV.pow 2).integrableOn_Icc
  have hiD : IntegrableOn (fun t => D t^2) (Icc a b) volume := (hD.pow 2).integrableOn_Icc
  have hvi : (∫ t in Icc a b, ‖f t‖^2) ≤ ∫ t in Icc a b, V t^2 := by
    apply integral_mono_ae (hcont.norm.pow 2).integrableOn_Icc hiV
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact pow_le_pow_left₀ (norm_nonneg _) (hbV t ht) 2
  have hdi : (∫ t in Icc a b, ‖deriv f t‖^2) ≤ ∫ t in Icc a b, D t^2 := by
    apply integral_mono_ae (hd.integrable_norm_pow (by decide)) hiD
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact pow_le_pow_left₀ (norm_nonneg _) (hbD t ht) 2
  have h := (interval_pointwise_square f hab hf hd hx).trans
    (add_le_add (mul_le_mul_of_nonneg_left hvi (by positivity))
      (mul_le_mul_of_nonneg_left hdi (by positivity)))
  have hmass : (volume.restrict (Icc a b)).real univ = b-a := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal hm.le]
  change ‖f x‖^2 ≤ 2 * (⨍ t in Icc a b, V t^2+((b-a)*D t)^2)
  rw [average_eq, hmass, smul_eq_mul]
  simp only [mul_pow]
  rw [integral_add hiV (hiD.const_mul _), integral_const_mul]
  have heq : 2 * ((b-a)⁻¹ * ((∫ t in Icc a b, V t^2) +
      (b-a)^2 * (∫ t in Icc a b, D t^2))) =
      (2/(b-a)) * (∫ t in Icc a b, V t^2) +
      2*(b-a)*(∫ t in Icc a b, D t^2) := by field_simp [hm.ne']
  rwa [heq]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NeighborhoodExceptional
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable exceptional set for a common neighborhood majorant.
The moment order is an integer, so even orders may grow with the manuscript
parameter without changing any packet regularity order. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem interval_vertical_moment (ν : Measure ℝ) [SFinite ν]
    (V D : ℝ × ℝ → ℝ) (hV : Continuous V) (hD : Continuous D)
    {a b : ℝ} (hab : a < b) (n : ℕ) (C : ℝ≥0∞)
    (hline : ∀ t, (∫⁻ x, ENNReal.ofReal (V (t,x)^(2*n)+D (t,x)^(2*n)) ∂ν) ≤ C) :
    (∫⁻ x, ENNReal.ofReal (verticalSquareEnergy (volume.restrict (Icc a b))
      (fun t => V (t,x)) (fun t => D (t,x)))^n ∂ν) ≤ (4:ℝ≥0∞)^n*C := by
  let μ := volume.restrict (Icc a b)
  have hm : μ univ ≠ 0 := by
    dsimp [μ]
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
  let : NeZero μ := ⟨fun h => hm (by rw [h]; simp)⟩
  have hcV (x : ℝ) : Continuous (fun t => V (t,x)) := hV.comp (continuous_id.prodMk continuous_const)
  have hcD (x : ℝ) : Continuous (fun t => D (t,x)) := hD.comp (continuous_id.prodMk continuous_const)
  exact verticalSquareEnergy_line_moment μ ν V D hV.measurable hD.measurable n
    (fun x => ((hcV x).pow 2).continuousOn.integrableOn_Icc)
    (fun x => ((hcD x).pow 2).continuousOn.integrableOn_Icc)
    (fun x => (((hcV x).pow 2).add ((hcD x).pow 2)).pow n |>.continuousOn.integrableOn_Icc)
    (fun x => ((hcV x).pow (2*n)).continuousOn.integrableOn_Icc)
    (fun x => ((hcD x).pow (2*n)).continuousOn.integrableOn_Icc) C hline

theorem energy_superlevel_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Ω → ℝ) (hE : Measurable E)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold) (n : ℕ) (C : ℝ≥0∞)
    (hmoment : (∫⁻ x, ENNReal.ofReal (E x)^n ∂μ) ≤ C) :
    (ENNReal.ofReal threshold)^(2*n) * μ {x | threshold^2 ≤ E x} ≤ C := by
  have hsub : {x | threshold^2 ≤ E x} ⊆
      {x | (ENNReal.ofReal threshold)^(2*n) ≤ ENNReal.ofReal (E x)^n} := by
    intro x hx
    change (ENNReal.ofReal threshold)^(2*n) ≤ ENNReal.ofReal (E x)^n
    have h := pow_le_pow_left' (ENNReal.ofReal_le_ofReal hx) n
    simpa only [ENNReal.ofReal_pow hthreshold, pow_mul] using h
  exact (mul_le_mul' le_rfl (measure_mono hsub)).trans
    ((mul_meas_ge_le_lintegral (hE.ennreal_ofReal.pow_const n) _).trans hmoment)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DemodulatedVertical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove the vertical carrier before applying the interval Sobolev
estimate. The derivative norm is exactly the covariant derivative norm,
independently of the carrier frequencies and Hilbert dimension. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert
open PhaseCombinatorics

theorem character_hasDerivAt (frequency y : ℝ) :
    HasDerivAt (character frequency) ((frequency:ℂ)*Complex.I*character frequency y) y := by
  have h := (((hasDerivAt_id y).const_mul frequency).ofReal_comp.mul_const Complex.I).cexp
  refine h.congr_deriv ?_
  · simp only [id_eq, mul_one]
    symm
    change (frequency:ℂ)*Complex.I*character frequency y =
      character frequency y*((frequency:ℂ)*Complex.I)
    ring

theorem demodulatedSignal_norm {κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : κ → ℝ → ℂ) (y : ℝ) :
    ‖demodulatedSignal frequency f y‖ = ‖(WithLp.toLp 2 (fun k => f k y) : EuclideanSpace ℂ κ)‖ :=
  norm_diagonalModulation (fun k => -frequency k) (WithLp.toLp 2 (fun k => f k y)) y

theorem demodulatedSignal_hasDerivAt {κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : κ → ℝ → ℂ) (y : ℝ)
    (hf : ∀ k, DifferentiableAt ℝ (f k) y) :
    HasDerivAt (demodulatedSignal frequency f)
      (diagonalModulation (fun k => -frequency k) (covariantSignal frequency f y) y) y := by
  have hc : HasDerivAt (fun t k => f k t * character (-frequency k) t)
      (fun k => (deriv (f k) y - (frequency k:ℂ)*Complex.I*f k y) *
        character (-frequency k) y) y := by
    apply hasDerivAt_pi.mpr
    intro k
    have h := (hf k).hasDerivAt.mul (character_hasDerivAt (-frequency k) y)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℂ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt y hc

theorem demodulatedSignal_deriv_norm {κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : κ → ℝ → ℂ) (y : ℝ)
    (hf : ∀ k, DifferentiableAt ℝ (f k) y) :
    ‖deriv (demodulatedSignal frequency f) y‖ = ‖covariantSignal frequency f y‖ := by
  rw [(demodulatedSignal_hasDerivAt frequency f y hf).deriv, norm_diagonalModulation]

theorem demodulated_deriv_memLp {κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : κ → ℝ → ℂ) (μ : Measure ℝ)
    (hf : ∀ᵐ y ∂μ, ∀ k, DifferentiableAt ℝ (f k) y)
    (hD : MemLp (covariantSignal frequency f) 2 μ) :
    MemLp (deriv (demodulatedSignal frequency f)) 2 μ := by
  apply hD.congr_norm (aestronglyMeasurable_deriv _ μ)
  filter_upwards [hf] with y hy
  exact (demodulatedSignal_deriv_norm frequency f y hy).symm

theorem covariant_interval_energy {κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : κ → ℝ → ℂ) {a b : ℝ} (hab : a < b)
    (hf : ∀ y ∈ Set.Icc a b, ∀ k, DifferentiableAt ℝ (f k) y)
    (hD : MemLp (covariantSignal frequency f) 2 (volume.restrict (Set.Icc a b)))
    (V D : ℝ → ℝ) (hV : ContinuousOn V (Set.Icc a b)) (hDC : ContinuousOn D (Set.Icc a b))
    (hbV : ∀ y ∈ Set.Icc a b, ‖(WithLp.toLp 2 (fun k => f k y) : EuclideanSpace ℂ κ)‖ ≤ V y)
    (hbD : ∀ y ∈ Set.Icc a b, ‖covariantSignal frequency f y‖ ≤ D y)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ‖(WithLp.toLp 2 (fun k => f k x) : EuclideanSpace ℂ κ)‖^2 ≤
      verticalSquareEnergy (volume.restrict (Set.Icc a b)) V (fun t => (b-a)*D t) := by
  have hd := demodulated_deriv_memLp frequency f (volume.restrict (Set.Icc a b))
    ((ae_restrict_mem measurableSet_Icc).mono fun y hy => hf y hy) hD
  have h := interval_energy_domination (demodulatedSignal frequency f) hab
    (fun y hy => (demodulatedSignal_hasDerivAt frequency f y (hf y hy)).differentiableAt)
    hd V D hV hDC
    (fun y hy => by rw [demodulatedSignal_norm]; exact hbV y hy)
    (fun y hy => by rw [demodulatedSignal_deriv_norm frequency f y (hf y hy)]; exact hbD y hy) hx
  simpa only [demodulatedSignal_norm] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform vertical neighborhoods for an entire family of sums, with
one measurable exceptional set and an explicit area moment bound. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem top_neighborhood_exceptional {α κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : α → κ → ℝ → ℝ → ℂ)
    (V D : ℝ × ℝ → ℝ) (hV : Continuous V) (hD : Continuous D)
    (U : Set ℝ) (hU : MeasurableSet U) (c r threshold : ℝ)
    (hr : 0 < r) (hthreshold : 0 ≤ threshold) (n : ℕ) (C : ℝ≥0∞)
    (hline : ∀ y, (∫⁻ x in U, ENNReal.ofReal
      (V (y,x)^(2*n)+(4*r*D (y,x))^(2*n))) ≤ C)
    (hf : ∀ i x y, y ∈ Icc (c-2*r) (c+2*r) → ∀ k,
      DifferentiableAt ℝ (f i k x) y)
    (hmem : ∀ i x, MemLp (covariantSignal frequency (fun k => f i k x)) 2
      (volume.restrict (Icc (c-2*r) (c+2*r))))
    (hbV : ∀ i x y, y ∈ Icc (c-2*r) (c+2*r) →
      ‖(WithLp.toLp 2 (fun k => f i k x y) : EuclideanSpace ℂ κ)‖ ≤ V (y,x))
    (hbD : ∀ i x y, y ∈ Icc (c-2*r) (c+2*r) →
      ‖covariantSignal frequency (fun k => f i k x) y‖ ≤ D (y,x)) :
    ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ bad ⊆ U ×ˢ Icc (c-r) (c+r) ∧
      (ENNReal.ofReal threshold)^(2*n)*(volume.prod volume) bad ≤
        (4:ℝ≥0∞)^n*C*ENNReal.ofReal (2*r) ∧
      ∀ i x z v, x ∈ U → |z-c| ≤ r → |v| ≤ r → (x,z) ∉ bad →
        ‖(WithLp.toLp 2 (fun k => f i k x (z+v)) : EuclideanSpace ℂ κ)‖ ≤ threshold := by
  let μ := volume.restrict (Icc (c-2*r) (c+2*r))
  let E : ℝ → ℝ := fun x => verticalSquareEnergy μ
    (fun y => V (y,x)) (fun y => 4*r*D (y,x))
  have hE : Measurable E := verticalSquareEnergy_measurable μ V
    (fun z => 4*r*D z) hV.measurable (hD.measurable.const_mul _)
  let B := {x | threshold^2 ≤ E x}
  have hB : MeasurableSet B := measurableSet_le measurable_const hE
  let bad := (U ∩ B) ×ˢ Icc (c-r) (c+r)
  have hmoment : (∫⁻ x in U, ENNReal.ofReal (E x)^n) ≤ (4:ℝ≥0∞)^n*C :=
    interval_vertical_moment (volume.restrict U) V (fun z => 4*r*D z) hV
      (hD.const_mul _) (by linarith : c-2*r < c+2*r) n C hline
  have hmark := energy_superlevel_moment (volume.restrict U) E hE threshold hthreshold n
    ((4:ℝ≥0∞)^n*C) hmoment
  change (ENNReal.ofReal threshold)^(2*n)*(volume.restrict U) B ≤ _ at hmark
  rw [Measure.restrict_apply hB, inter_comm B U] at hmark
  refine ⟨bad, (hU.inter hB).prod measurableSet_Icc, ?_, ?_, ?_⟩
  · exact prod_mono inter_subset_left Subset.rfl
  · change (ENNReal.ofReal threshold)^(2*n) *
      (volume.prod volume) ((U ∩ B) ×ˢ Icc (c-r) (c+r)) ≤ _
    rw [Measure.prod_prod, Real.volume_Icc, show c+r-(c-r)=2*r by ring, ← mul_assoc]
    exact mul_le_mul' hmark le_rfl
  · intro i x z v hx hz hv hout
    have hzi : z ∈ Icc (c-r) (c+r) := by
      rcases abs_le.mp hz with ⟨h1,h2⟩
      constructor <;> linarith
    have houtE : ¬ threshold^2 ≤ E x := fun he => hout ⟨⟨hx,he⟩,hzi⟩
    have hzv : z+v ∈ Icc (c-2*r) (c+2*r) := by
      rcases abs_le.mp hz with ⟨h1,h2⟩
      rcases abs_le.mp hv with ⟨h3,h4⟩
      constructor <;> linarith
    have hp := covariant_interval_energy frequency (fun k => f i k x)
      (by linarith : c-2*r < c+2*r) (fun y hy => hf i x y hy) (hmem i x)
      (fun y => V (y,x)) (fun y => D (y,x))
      (hV.comp (continuous_id.prodMk continuous_const)).continuousOn
      (hD.comp (continuous_id.prodMk continuous_const)).continuousOn
      (fun y hy => hbV i x y hy) (fun y hy => hbD i x y hy) hzv
    have hs : ‖(WithLp.toLp 2 (fun k => f i k x (z+v)) : EuclideanSpace ℂ κ)‖^2 ≤ E x := by
      convert hp using 1
      all_goals try with_reducible_and_instances rfl
      dsimp only [E, μ]
      congr 1
      funext y
      ring
    have he := lt_of_not_ge houtE
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun k => f i k x (z+v)) : EuclideanSpace ℂ κ)]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NeighborhoodGeometric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common vertical-neighborhood exceptional set has exponentially
small area when the chosen even line moment has polynomial growth. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem quarter_area_of_even_moment (X M : ℝ≥0∞) (A : ℝ) (hA : 0 < A) (n : ℕ)
    (h : (ENNReal.ofReal (4*A))^(2*n)*X ≤ (ENNReal.ofReal (2*A))^(2*n)*M) :
    X ≤ (1/4:ℝ≥0∞)^n*M := by
  have ha0 : (ENNReal.ofReal (4*A))^(2*n) ≠ 0 :=
    pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
  have hat : (ENNReal.ofReal (4*A))^(2*n) ≠ ⊤ := by finiteness
  have hr : ENNReal.ofReal (2*A)/ENNReal.ofReal (4*A) = (1/2:ℝ≥0∞) := by
    rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < 4*A)]
    have heq : (2*A)/(4*A) = (1/2:ℝ) := by field_simp [hA.ne']; norm_num
    rw [heq, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)]
    norm_num [pow_two]
  calc
    X = ((ENNReal.ofReal (4*A))^(2*n))⁻¹ *
        ((ENNReal.ofReal (4*A))^(2*n)*X) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 hat, one_mul]
    _ ≤ ((ENNReal.ofReal (4*A))^(2*n))⁻¹ *
        ((ENNReal.ofReal (2*A))^(2*n)*M) := mul_le_mul' le_rfl h
    _ = (ENNReal.ofReal (2*A)/ENNReal.ofReal (4*A))^(2*n)*M := by
      rw [ENNReal.div_eq_inv_mul, mul_pow, ENNReal.inv_pow]
      ring
    _ = _ := by
      have hquarter : (1/2:ℝ≥0∞)^2 = 1/4 := by
        rw [ENNReal.div_eq_inv_mul, mul_one, ← ENNReal.inv_pow]
        norm_num [pow_two]
      rw [hr, pow_mul, hquarter]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WeightedExceptionalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Raising the box threshold by the reciprocal lattice weight gives
summable exceptional areas, with a fixed spatial decay order. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem weighted_quarter_area_of_even_moment (X M : ℝ≥0∞) (A w : ℝ)
    (hA : 0 < A) (hw : 0 < w) (n : ℕ)
    (h : (ENNReal.ofReal (4*A/w))^(2*n)*X ≤ (ENNReal.ofReal (2*A))^(2*n)*M) :
    X ≤ (1/4:ℝ≥0∞)^n*(ENNReal.ofReal w)^(2*n)*M := by
  have heq : (ENNReal.ofReal (2*(A/w)))^(2*n)*(ENNReal.ofReal w)^(2*n) =
      (ENNReal.ofReal (2*A))^(2*n) := by
    rw [← mul_pow, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*(A/w))]
    congr 2
    field_simp
  have h' : (ENNReal.ofReal (4*(A/w)))^(2*n)*X ≤
      (ENNReal.ofReal (2*(A/w)))^(2*n)*((ENNReal.ofReal w)^(2*n)*M) := by
    rw [← mul_assoc, heq]
    rw [show 4*(A/w) = 4*A/w by ring]
    exact h
  have hp := quarter_area_of_even_moment X ((ENNReal.ofReal w)^(2*n)*M)
    (A/w) (div_pos hA hw) n h'
  simpa only [mul_assoc] using hp

theorem weighted_quarter_area_le (X M : ℝ≥0∞) (A w : ℝ)
    (hA : 0 < A) (hw : 0 < w) (hw1 : w ≤ 1) (n : ℕ) (hn : 1 ≤ n)
    (h : (ENNReal.ofReal (4*A/w))^(2*n)*X ≤ (ENNReal.ofReal (2*A))^(2*n)*M) :
    X ≤ (1/4:ℝ≥0∞)^n*ENNReal.ofReal w*M := by
  have hp : (ENNReal.ofReal w)^(2*n) ≤ ENNReal.ofReal w := by
    have hw' : ENNReal.ofReal w ≤ 1 := by exact_mod_cast ENNReal.ofReal_le_ofReal hw1
    simpa only [pow_one] using pow_le_pow_right_of_le_one' hw' (show 1 ≤ 2*n by omega)
  exact (weighted_quarter_area_of_even_moment X M A w hA hw n h).trans
    (mul_le_mul' (mul_le_mul' le_rfl hp) le_rfl)

theorem boxVariationWeight_le_one (p : ℤ × ℤ) : boxVariationWeight p ≤ 1 := by
  have h (x : ℝ) : lineEnvelope 0 1 1 x ≤ 1 := by
    simp only [lineEnvelope, sub_zero, div_one, pow_one]
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
  exact (mul_le_mul (h p.1) (h p.2) (lineEnvelope_nonneg _ _ _ _) (by norm_num)).trans_eq
    (one_mul _)

theorem global_weighted_even_moment_area {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (bad : ℤ × ℤ → Set Ω) (M : ℝ≥0∞) (A : ℝ) (hA : 0 < A)
    (n : ℕ) (hn : 1 ≤ n)
    (hbad : ∀ p, (ENNReal.ofReal (4*A/boxVariationWeight p))^(2*n)*μ (bad p) ≤
      (ENNReal.ofReal (2*A))^(2*n)*M) :
    μ (⋃ p, bad p) ≤ (1/4:ℝ≥0∞)^n*M*ENNReal.ofReal ((4*Real.pi)^2) := by
  apply global_exceptional_area μ bad ((1/4:ℝ≥0∞)^n*M)
  intro p
  have hp := weighted_quarter_area_le (μ (bad p)) M A (boxVariationWeight p) hA
    (boxVariationWeight_pos p) (boxVariationWeight_le_one p) n hn (hbad p)
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopBoxPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed polynomial top weights dominate the reciprocal lattice decay
uniformly on a whole box and all its allowed vertical shifts. -/

noncomputable section
open Set

namespace LipschitzHilbert

theorem box_polynomial_base_two (a r k x : ℝ) (hr : 0 < r)
    (hx : |x-(a+r*k)| ≤ 2*r) :
    (1+k^2)/16 ≤ 1+((x-a)/r)^2 := by
  let t := (x-a)/r
  have hd : |t-k| ≤ 2 := by
    have heq : t-k = (x-(a+r*k))/r := by dsimp [t]; field_simp; ring
    rw [heq, abs_div, abs_of_pos hr, div_le_iff₀ hr]
    exact hx
  have hs : (t-k)^2 ≤ 4 := by nlinarith [abs_le.mp hd, sq_abs (t-k)]
  dsimp only [t] at *
  nlinarith [sq_nonneg (k-2*((x-a)/r)), sq_nonneg ((x-a)/r)]

theorem topWeight_box_lower (a b r R x z v : ℝ) (p : ℤ × ℤ) (q : ℕ)
    (hr : 0 < r) (hR : 0 < R)
    (hx : |x-(a+r*p.1)| ≤ r) (hz : |z-(b+R*p.2)| ≤ R) (hv : |v| ≤ R) :
    ((boxVariationWeight p)⁻¹/256)^q ≤
      polynomialWeight a r q x * polynomialWeight b R q (z+v) := by
  have hx2 : |x-(a+r*p.1)| ≤ 2*r := hx.trans (by linarith)
  have hz2 : |(z+v)-(b+R*p.2)| ≤ 2*R := by
    calc
      _ = |(z-(b+R*p.2))+v| := by congr 1; ring
      _ ≤ |z-(b+R*p.2)|+|v| := abs_add_le _ _
      _ ≤ 2*R := by linarith
  have h1 := box_polynomial_base_two a r p.1 x hr hx2
  have h2 := box_polynomial_base_two b R p.2 (z+v) hR hz2
  have hprod := mul_le_mul h1 h2 (by positivity : 0 ≤ (1+(p.2:ℝ)^2)/16)
    (by positivity : 0 ≤ 1+((x-a)/r)^2)
  have hinv : (boxVariationWeight p)⁻¹ = (1+(p.1:ℝ)^2)*(1+(p.2:ℝ)^2) := by
    simp only [boxVariationWeight, lineEnvelope, sub_zero, div_one, pow_one, mul_inv_rev, inv_inv]
    ring
  rw [hinv]
  have hbase : ((1+(p.1:ℝ)^2)*(1+(p.2:ℝ)^2))/256 ≤
      (1+((x-a)/r)^2)*(1+((z+v-b)/R)^2) := by nlinarith [hprod]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤
    ((1+(p.1:ℝ)^2)*(1+(p.2:ℝ)^2))/256) hbase q
  simpa only [polynomialWeight, ← div_pow, mul_pow] using hp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopBoxDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert a weighted top bound to a decaying unweighted bound, using
one fixed polynomial degree independently of the moment order. -/

noncomputable section

namespace LipschitzHilbert

theorem weighted_bound_to_box_decay (A S w P : ℝ) (hS : 0 ≤ S) (hw : 0 < w)
    (q : ℕ) (hq : 1 ≤ q) (hP : (w⁻¹/256)^q ≤ P) (hbound : P*S ≤ A/w) :
    S ≤ 256^q*A*w^(q-1) := by
  have hL : 0 < (w⁻¹/256)^q := by positivity
  apply (mul_le_mul_iff_right₀ hL).mp
  calc
    ((w⁻¹/256)^q)*S ≤ P*S := mul_le_mul_of_nonneg_right hP hS
    _ ≤ A/w := hbound
    _ = ((w⁻¹/256)^q)*(256^q*A*w^(q-1)) := by
      obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
      subst q
      simp only [Nat.succ_sub_one, pow_succ, div_pow, inv_pow]
      field_simp [hw.ne']

theorem topWeight_bound_to_box_decay (a b r R x z v A S : ℝ) (p : ℤ × ℤ)
    (q : ℕ) (hq : 1 ≤ q) (hS : 0 ≤ S) (hr : 0 < r) (hR : 0 < R)
    (hx : |x-(a+r*p.1)| ≤ r) (hz : |z-(b+R*p.2)| ≤ R) (hv : |v| ≤ R)
    (hbound : (polynomialWeight a r q x * polynomialWeight b R q (z+v))*S ≤
      A/boxVariationWeight p) :
    S ≤ 256^q*A*boxVariationWeight p^(q-1) :=
  weighted_bound_to_box_decay A S (boxVariationWeight p) _ hS (boxVariationWeight_pos p)
    q hq (topWeight_box_lower a b r R x z v p q hr hR hx hz hv) hbound

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_GlobalTopBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Glue the measurable box exceptions across the full plane, retaining
both the summable area estimate and polynomial decay away from the top. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem floor_box_mem_Ico (a r x : ℝ) (hr : 0 < r) :
    x ∈ Ico (a+r*(⌊(x-a)/r⌋:ℤ)) (a+r*((⌊(x-a)/r⌋:ℤ)+1)) := by
  have hlo := mul_le_mul_of_nonneg_right (Int.floor_le ((x-a)/r)) hr.le
  have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one ((x-a)/r)) hr
  rw [div_mul_cancel₀ _ hr.ne'] at hlo hhi
  constructor <;> linarith

theorem global_top_box_gluing {α E : Type*} [NormedAddCommGroup E]
    (F : α → ℝ → ℝ → E) (bad : ℤ × ℤ → Set (ℝ × ℝ))
    (hmeas : ∀ p, MeasurableSet (bad p))
    (a b r R A : ℝ) (hr : 0 < r) (hR : 0 < R) (hA : 0 < A)
    (M : ℝ≥0∞) (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q)
    (harea : ∀ p, (ENNReal.ofReal (4*A/boxVariationWeight p))^(2*n)*
      (volume.prod volume) (bad p) ≤ (ENNReal.ofReal (2*A))^(2*n)*M)
    (hpoint : ∀ p i x z v,
      x ∈ Ico (a+r*p.1) (a+r*((p.1:ℝ)+1)) → |z-(b+R*p.2)| ≤ R → |v| ≤ R →
      (x,z) ∉ bad p →
      (polynomialWeight a r q x * polynomialWeight b R q (z+v))*‖F i x (z+v)‖ ≤
        4*A/boxVariationWeight p) :
    ∃ exceptional : Set (ℝ × ℝ), MeasurableSet exceptional ∧
      (volume.prod volume) exceptional ≤ (1/4:ℝ≥0∞)^n*M*ENNReal.ofReal ((4*Real.pi)^2) ∧
      ∀ i x z v, |v| ≤ R → (x,z) ∉ exceptional →
        ‖F i x (z+v)‖ ≤ 256^q*(4*A)*
          boxVariationWeight (packetBoxIndex a b r R x z)^(q-1) := by
  refine ⟨⋃ p, bad p, MeasurableSet.iUnion hmeas,
    global_weighted_even_moment_area (volume.prod volume) bad M A hA n hn harea, ?_⟩
  intro i x z v hv hout
  let p := packetBoxIndex a b r R x z
  have hpout : (x,z) ∉ bad p := fun h => hout (mem_iUnion.mpr ⟨p,h⟩)
  have hx : x ∈ Ico (a+r*p.1) (a+r*((p.1:ℝ)+1)) := floor_box_mem_Ico a r x hr
  have hz := packetBoxIndex_vertical a b r R x z hR
  exact topWeight_bound_to_box_decay a b r R x z v (4*A) ‖F i x (z+v)‖ p q hq
    (norm_nonneg _) hr hR (packetBoxIndex_horizontal a b r R x z hr) hz hv
    (hpoint p i x z v hx hz hv hpout)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_GlobalNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global top concentration from uniform local line moments. Box
exceptions are constructed by the proved vertical Sobolev estimate,
and their areas are summed over the whole plane. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem global_top_neighborhood {α κ E : Type*} [Fintype κ] [NormedAddCommGroup E]
    (frequency : κ → ℝ) (f : α → κ → ℝ → ℝ → ℂ) (F : α → ℝ → ℝ → E)
    (V D : ℝ × ℝ → ℝ) (hV : Continuous V) (hD : Continuous D)
    (a b r R A : ℝ) (hr : 0 < r) (hR : 0 < R) (hA : 0 < A)
    (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q)
    (hline : ∀ (p : ℤ × ℤ) y, (∫⁻ x in Ico (a+r*p.1) (a+r*((p.1:ℝ)+1)),
      ENNReal.ofReal (V (y,x)^(2*n)+(4*R*D (y,x))^(2*n))) ≤
        2*(ENNReal.ofReal A)^(2*n)*ENNReal.ofReal r)
    (hdiff : ∀ i k x y, DifferentiableAt ℝ (f i k x) y)
    (hmem : ∀ (p : ℤ × ℤ) i x, MemLp (covariantSignal frequency (fun k => f i k x)) 2
      (volume.restrict (Icc (b+R*p.2-2*R) (b+R*p.2+2*R))))
    (hbV : ∀ i x y, ‖(WithLp.toLp 2 (fun k => f i k x y) : EuclideanSpace ℂ κ)‖ ≤ V (y,x))
    (hbD : ∀ i x y, ‖covariantSignal frequency (fun k => f i k x) y‖ ≤ D (y,x))
    (hweighted : ∀ i x y, ‖(WithLp.toLp 2 (fun k => f i k x y) : EuclideanSpace ℂ κ)‖ =
      (polynomialWeight a r q x * polynomialWeight b R q y)*‖F i x y‖) :
    ∃ exceptional : Set (ℝ × ℝ), MeasurableSet exceptional ∧
      (volume.prod volume) exceptional ≤ (1/4:ℝ≥0∞)^n*
        (2*ENNReal.ofReal r*ENNReal.ofReal (2*R))*ENNReal.ofReal ((4*Real.pi)^2) ∧
      ∀ i x z v, |v| ≤ R → (x,z) ∉ exceptional →
        ‖F i x (z+v)‖ ≤ 256^q*(4*A)*
          boxVariationWeight (packetBoxIndex a b r R x z)^(q-1) := by
  have hlocal (p : ℤ × ℤ) := top_neighborhood_exceptional frequency f V D hV hD
    (Ico (a+r*p.1) (a+r*((p.1:ℝ)+1))) measurableSet_Ico (b+R*p.2) R
    (4*A/boxVariationWeight p) hR
    (div_nonneg (by positivity) (boxVariationWeight_pos p).le) n
    (2*(ENNReal.ofReal A)^(2*n)*ENNReal.ofReal r) (hline p)
    (fun i x y _ k => hdiff i k x y) (hmem p)
    (fun i x y _ => hbV i x y) (fun i x y _ => hbD i x y)
  choose bad hbad using hlocal
  apply global_top_box_gluing F bad (fun p => (hbad p).1) a b r R A hr hR hA
    (2*ENNReal.ofReal r*ENNReal.ofReal (2*R)) n q hn hq
  · intro p
    have h := (hbad p).2.2.1
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    simp only [ENNReal.ofReal_ofNat, pow_mul]
    norm_num
    ring
  · intro p i x z v hx hz hv hout
    have h := (hbad p).2.2.2 i x z v hx hz hv hout
    rwa [hweighted] at h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual decaying top weights and their motion along a reference line. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace SlopeBox

theorem radius_nonnegative (T : SlopeBox) (z : ℝ × ℝ) : 0 ≤ T.radius z :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem weight_pos (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) (z : ℝ × ℝ) :
    0 < T.weight K D z := by
  unfold weight
  have hr := T.radius_nonnegative z
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) D)
    (Real.rpow_pos_of_pos (by positivity) _)

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopFamilyException
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One common moment order sums all actual top exceptional sets with
the total top area. This is independent of the number of tops. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert

theorem topExceptionMoment_pos (M J L : ℝ) : 1 ≤ topExceptionMoment M J L := by
  unfold topExceptionMoment
  omega

theorem topExceptionMoment_le (M J L c : ℝ) (hJ : 0 ≤ J) (hL : 1 ≤ L)
    (hM : 1 ≤ M) (hlog : Real.log M ≤ c*L) :
    (topExceptionMoment M J L:ℝ) ≤ ((J+c)/Real.log 4+2)*L :=
  exponential_moment_order_le J c L M hJ hL hM hlog

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopLatticeDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the lattice decay in the global concentration estimate into
the eighth power of the manuscript's actual slope-box weight. -/

noncomputable section
namespace LipschitzHilbert

theorem floor_abs_bound (x : ℝ) : |x| ≤ |((⌊x⌋:ℤ):ℝ)|+1 := by
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  exact abs_le.mpr ⟨by linarith [neg_abs_le (⌊x⌋:ℝ)],
    by linarith [le_abs_self (⌊x⌋:ℝ)]⟩

theorem boxVariationWeight_floor_bound (x y : ℝ) :
    (1+|x|+|y|)*boxVariationWeight (⌊x⌋,⌊y⌋) ≤ 5 := by
  let i : ℝ := ⌊x⌋
  let j : ℝ := ⌊y⌋
  have hi : |i| ≤ 1+i^2 := by nlinarith [sq_nonneg (|i|-1), sq_abs i]
  have hj : |j| ≤ 1+j^2 := by nlinarith [sq_nonneg (|j|-1), sq_abs j]
  have hbase : 1+|x|+|y| ≤ 5*((1+i^2)*(1+j^2)) := by
    have hx := floor_abs_bound x
    have hy := floor_abs_bound y
    change |x| ≤ |i|+1 at hx
    change |y| ≤ |j|+1 at hy
    nlinarith [sq_nonneg i, sq_nonneg j, mul_nonneg (sq_nonneg i) (sq_nonneg j)]
  have hden : 0 < (1+i^2)*(1+j^2) := by positivity
  have heq : boxVariationWeight (⌊x⌋,⌊y⌋) = ((1+i^2)*(1+j^2))⁻¹ := by
    simp [boxVariationWeight, lineEnvelope, i, j, mul_comm]
  rw [heq, ← div_eq_mul_inv]
  exact (div_le_iff₀ hden).mpr hbase

theorem boxVariationWeight_floor_power (x y : ℝ) (m : ℕ) :
    boxVariationWeight (⌊x⌋,⌊y⌋)^m ≤ 5^m/(1+|x|+|y|)^m := by
  have hb : 0 < 1+|x|+|y| := by positivity
  apply (le_div_iff₀ (pow_pos hb m)).mpr
  have hp := pow_le_pow_left₀
    (mul_nonneg (by positivity) (boxVariationWeight_pos (⌊x⌋,⌊y⌋)).le)
    (boxVariationWeight_floor_bound x y) m
  simpa only [mul_pow, mul_comm] using hp

namespace SlopeBox

theorem weight_nat_eighth (T : SlopeBox) (K : ℝ) (hK : 0 < K) (d : ℕ) (z : ℝ × ℝ) :
    (T.weight K (d:ℝ) z)^8 = (2:ℝ)^(8*d)/(1+T.radius z/K)^(8*d) := by
  have hb : 0 ≤ 1+T.radius z/K := by
    have := T.radius_nonnegative z
    positivity
  simp only [weight, Real.rpow_neg hb, Real.rpow_natCast, mul_pow, inv_pow, ← pow_mul]
  rw [mul_comm d 8]
  simp only [div_eq_mul_inv]

theorem lattice_decay_le_weight (T : SlopeBox) (K : ℝ) (hK : 0 < K)
    (d : ℕ) (z : ℝ × ℝ) :
    boxVariationWeight (packetBoxIndex T.x (T.y-T.slope*T.x)
      (K*T.length) (K*T.width) z.1 (z.2-T.slope*z.1))^(8*d) ≤
        (5:ℝ)^(8*d)*(T.weight K (d:ℝ) z)^8 := by
  let X := (z.1-T.x)/(K*T.length)
  let Y := ((z.2-T.slope*z.1)-(T.y-T.slope*T.x))/(K*T.width)
  have hr : 1+|X|+|Y| = 1+T.radius z/K := by
    unfold radius horizontal transverse
    dsimp [X,Y]
    rw [abs_div, abs_div, abs_of_pos (mul_pos hK T.length_pos),
      abs_of_pos (mul_pos hK T.width_pos), abs_div, abs_div,
      abs_of_pos T.length_pos, abs_of_pos T.width_pos]
    have heq : (z.2-T.slope*z.1)-(T.y-T.slope*T.x) =
        (z.2-T.y)-T.slope*(z.1-T.x) := by ring
    rw [heq]
    ring
  have hp := boxVariationWeight_floor_power X Y (8*d)
  change boxVariationWeight (⌊X⌋,⌊Y⌋)^(8*d) ≤ _
  apply hp.trans
  rw [hr, T.weight_nat_eighth K hK]
  have hden : 0 < (1+T.radius z/K)^(8*d) := by
    have := T.radius_nonnegative z
    positivity
  have htwo : (1:ℝ) ≤ 2^(8*d) := one_le_pow₀ (by norm_num)
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hden.le
  exact le_mul_of_one_le_right (by positivity) htwo

end SlopeBox
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlopeTopNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the global lattice neighborhood bound to physical slope
coordinates and the exact top weight, with an exponential area bound. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

theorem topAreaPrefactor_pos (K : ℝ) (hK : 0 < K) : 0 < topAreaPrefactor K := by
  unfold topAreaPrefactor
  positivity

theorem slope_top_neighborhood {ι E : Type*} [NormedAddCommGroup E]
    (T : SlopeBox) (K A J L : ℝ) (d : ℕ) (hK : 0 < K) (hA : 0 ≤ A)
    (F : ι → ℝ → ℝ → E)
    (hlocal : ∀ n : ℕ, 1 ≤ n → ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ (1/4:ℝ≥0∞)^n*
        (2*ENNReal.ofReal (K*T.length)*ENNReal.ofReal (2*(K*T.width)))*
          ENNReal.ofReal ((4*Real.pi)^2) ∧
      ∀ i x y v, |v| ≤ K*T.width → (x,y) ∉ bad →
        ‖F i x (y+v)‖ ≤ A*(n:ℝ)*
          boxVariationWeight (packetBoxIndex T.x (T.y-T.slope*T.x)
            (K*T.length) (K*T.width) x y)^(8*d)) :
    let n := topExceptionMoment (topAreaPrefactor K) J L
    ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*T.area) ∧
      ∀ i z v, |v| ≤ K*T.width → z ∉ bad →
        ‖F i z.1 ((z.2-T.slope*z.1)+v)‖ ≤
          (A*(n:ℝ)*5^(8*d))*(T.weight K (d:ℝ) z)^8 := by
  dsimp only
  let n := topExceptionMoment (topAreaPrefactor K) J L
  obtain ⟨bad,hbad,harea,hpoint⟩ := hlocal n (topExceptionMoment_pos _ _ _)
  let physical := slopeShear T.slope '' bad
  have hphysical : MeasurableSet physical := (slopeShear T.slope).measurableSet_image.mpr hbad
  have hmeasure : (volume.prod volume) physical = (volume.prod volume) bad := by
    have h := (slopeShear_measurePreserving T.slope).measure_preimage_equiv physical
    rw [show (slopeShear T.slope) ⁻¹' physical = bad from
      Equiv.preimage_image _ _] at h
    exact h.symm
  have hfactor :
      (2*ENNReal.ofReal (K*T.length)*ENNReal.ofReal (2*(K*T.width)))*
        ENNReal.ofReal ((4*Real.pi)^2) =
      ENNReal.ofReal (topAreaPrefactor K)*ENNReal.ofReal T.area := by
    have hl := T.length_pos
    have hw := T.width_pos
    have htwo : (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) := by norm_num
    rw [htwo, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*(K*T.length)),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*(K*T.length)*(2*(K*T.width))),
      ← ENNReal.ofReal_mul (topAreaPrefactor_pos K hK).le]
    congr 1
    unfold topAreaPrefactor SlopeBox.area
    ring
  have hexp : (1/4:ℝ≥0∞)^n*ENNReal.ofReal (topAreaPrefactor K) ≤
      ENNReal.ofReal (Real.exp (-J*L)) := by
    have h := ENNReal.ofReal_le_ofReal
      (prefactor_quarter_successor_bound (topAreaPrefactor K) (J*L) (topAreaPrefactor_pos K hK))
    rw [ENNReal.ofReal_mul (topAreaPrefactor_pos K hK).le,
      ENNReal.ofReal_pow (by norm_num)] at h
    have hq : ENNReal.ofReal (1/4:ℝ) = (1/4:ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [hq, show -(J*L) = -J*L by ring] at h
    simpa only [n, topExceptionMoment, mul_comm] using h
  refine ⟨physical,hphysical,?_,?_⟩
  · rw [hmeasure]
    rw [mul_assoc, hfactor] at harea
    calc
      _ ≤ ((1/4:ℝ≥0∞)^n*ENNReal.ofReal (topAreaPrefactor K))*ENNReal.ofReal T.area := by
        simpa only [mul_assoc] using harea
      _ ≤ ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal T.area := mul_le_mul' hexp le_rfl
      _ = _ := (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
  · intro i z v hv hout
    have hcoord : (z.1,z.2-T.slope*z.1) ∉ bad := by
      intro hin
      apply hout
      refine ⟨(z.1,z.2-T.slope*z.1),hin,?_⟩
      simp [slopeShear]
    have hp := hpoint i z.1 (z.2-T.slope*z.1) v hv hcoord
    have hdecay := T.lattice_decay_le_weight K hK d z
    exact hp.trans (by
      have h := mul_le_mul_of_nonneg_left hdecay (mul_nonneg hA (Nat.cast_nonneg n))
      simpa only [mul_assoc] using h)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_TopCovariantPacket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scaled covariant derivative of a top-weighted packet is another
Schwartz packet. Its extra scalar factor is bounded by 8q independently
of the top size and the vertical carrier frequency. -/

noncomputable section
open FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert

theorem topCovariantFactor_bound (b R y : ℝ) (q : ℕ) (hR : 0 < R) :
    |topCovariantFactor b R y q| ≤ 8*(q:ℝ) := by
  have hY : 0 < polynomialWeight b R q y :=
    zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _)
  unfold topCovariantFactor
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<4),
    abs_of_pos hR, abs_of_pos hY]
  apply (div_le_iff₀ hY).mpr
  calc
    _ ≤ 4*R*((2*(q:ℝ)/R)*polynomialWeight b R q y) :=
      mul_le_mul_of_nonneg_left (polynomialWeight_derivative b R y q hR) (by positivity)
    _ = _ := by field_simp; ring

theorem topCovariantWave_bound (f df : SchwartzMap ℝ ℂ)
    (a r b R y s l t W C : ℝ) (q m n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hW : 0 < W) (hR : 0 < R)
    (hlr : l ≤ r) (hWR : W ≤ R) (hs : |s-a| ≤ r) (ht : |t-b| ≤ R) (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*(lineEnvelope s l (m+2*q) x * lineEnvelope t W (n+2*q) y))
    (hdf : ∀ x, ‖df x‖ ≤ C*(lineEnvelope s l (m+2*q) x * lineEnvelope t W (n+2*q) y))
    (x : ℝ) :
    ‖topCovariantWave f df a r b R y q x‖ ≤
      ((8*(q:ℝ)+1)*(16^q*(16^q*C)))*(lineEnvelope s l m x * lineEnvelope t W n y) := by
  have h1 := topWeightedWave_bound f a r b R y s l t W C q m n hl hr hW hR hlr hWR hs ht hC hf x
  have h2 := topWeightedWave_bound df a r b R y s l t W C q m n hl hr hW hR hlr hWR hs ht hC hdf x
  change ‖(topCovariantFactor b R y q:ℂ)*topWeightedWave f a r b R y q x +
    topWeightedWave df a r b R y q x‖ ≤ _
  calc
    _ ≤ ‖(topCovariantFactor b R y q:ℂ)*topWeightedWave f a r b R y q x‖ +
        ‖topWeightedWave df a r b R y q x‖ := norm_add_le _ _
    _ = |topCovariantFactor b R y q| *‖topWeightedWave f a r b R y q x‖ +
        ‖topWeightedWave df a r b R y q x‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (8*(q:ℝ))*((16^q*(16^q*C))*(lineEnvelope s l m x*lineEnvelope t W n y)) +
        (16^q*(16^q*C))*(lineEnvelope s l m x*lineEnvelope t W n y) :=
      add_le_add (mul_le_mul (topCovariantFactor_bound b R y q hR) h1 (norm_nonneg _)
        (by positivity)) h2
    _ = _ := by ring

theorem topWeightedWave_covariant (f df : ℝ → SchwartzMap ℝ ℂ)
    (a r b R y frequency x : ℝ) (q : ℕ)
    (hf : DifferentiableAt ℝ (fun t => f t x) y)
    (hdf : (4*R:ℂ)*(deriv (fun t => f t x) y-(frequency:ℂ)*Complex.I*f y x) = df y x) :
    (4*R:ℂ)*(deriv (fun t => topWeightedWave (f t) a r b R t q x) y -
      (frequency:ℂ)*Complex.I*topWeightedWave (f y) a r b R y q x) =
        topCovariantWave (f y) (df y) a r b R y q x := by
  have hY : polynomialWeight b R q y ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _))
  have hc : topCovariantFactor b R y q*polynomialWeight b R q y =
      4*R*deriv (polynomialWeight b R q) y := by
    exact div_mul_cancel₀ _ hY
  have hcC := congrArg (fun t : ℝ => (t:ℂ)) hc
  push_cast at hcC
  have hv := ((((polynomialWeight_differentiable b R q) y).hasDerivAt.ofReal_comp).mul
    hf.hasDerivAt).const_mul (polynomialWeight a r q x:ℂ)
  have heq : (fun t => (polynomialWeight a r q x:ℂ)*((polynomialWeight b R q t:ℂ)*f t x)) =
      (fun t => topWeightedWave (f t) a r b R t q x) := by
    funext t
    rw [topWeightedWave_apply]
    push_cast
    ring
  change HasDerivAt (fun t => (polynomialWeight a r q x:ℂ)*
    ((polynomialWeight b R q t:ℂ)*f t x)) _ y at hv
  rw [heq] at hv
  rw [hv.deriv]
  change _ = (topCovariantFactor b R y q:ℂ)*topWeightedWave (f y) a r b R y q x +
    topWeightedWave (df y) a r b R y q x
  simp only [topWeightedWave_apply]
  rw [← hdf]
  push_cast
  linear_combination -(polynomialWeight a r q x:ℂ)*(f y x)*hcC

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopCovariantContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity and vertical differentiability of the constructed weighted
packet pair, derived from the original packets and their covariant waves. -/

noncomputable section
namespace LipschitzHilbert

theorem topCovariantFactor_continuous (b R : ℝ) (q : ℕ) :
    Continuous (fun y => topCovariantFactor b R y q) := by
  have hp : ContDiff ℝ 1 (polynomialWeight b R q) := by
    unfold polynomialWeight
    fun_prop
  exact (continuous_const.mul hp.continuous_deriv_one).div hp.continuous
    (fun y => ne_of_gt (zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _)))

theorem topWeightedWave_jointContinuous (f : ℝ → SchwartzMap ℝ ℂ)
    (a r b R : ℝ) (q : ℕ)
    (hf : Continuous (fun z : ℝ × ℝ => f z.1 z.2)) :
    Continuous (fun z : ℝ × ℝ => topWeightedWave (f z.1) a r b R z.1 q z.2) := by
  simp only [topWeightedWave_apply]
  unfold polynomialWeight
  fun_prop

theorem topCovariantWave_jointContinuous (f df : ℝ → SchwartzMap ℝ ℂ)
    (a r b R : ℝ) (q : ℕ)
    (hf : Continuous (fun z : ℝ × ℝ => f z.1 z.2))
    (hdf : Continuous (fun z : ℝ × ℝ => df z.1 z.2)) :
    Continuous (fun z : ℝ × ℝ => topCovariantWave (f z.1) (df z.1) a r b R z.1 q z.2) := by
  have h1 := topWeightedWave_jointContinuous f a r b R q hf
  have h2 := topWeightedWave_jointContinuous df a r b R q hdf
  have hc : Continuous (fun z : ℝ × ℝ => topCovariantFactor b R z.1 q) :=
    (topCovariantFactor_continuous b R q).comp continuous_fst
  change Continuous (fun z : ℝ × ℝ => (topCovariantFactor b R z.1 q:ℂ)*
    topWeightedWave (f z.1) a r b R z.1 q z.2 +
      topWeightedWave (df z.1) a r b R z.1 q z.2)
  exact ((Complex.continuous_ofReal.comp hc).mul h1).add h2

theorem topWeightedWave_vertical_differentiable (f : ℝ → SchwartzMap ℝ ℂ)
    (a r b R x y : ℝ) (q : ℕ) (hf : DifferentiableAt ℝ (fun t => f t x) y) :
    DifferentiableAt ℝ (fun t => topWeightedWave (f t) a r b R t q x) y := by
  have heq : (fun t => topWeightedWave (f t) a r b R t q x) =
      (fun t => (polynomialWeight a r q x:ℂ)*((polynomialWeight b R q t:ℂ)*f t x)) := by
    funext t
    rw [topWeightedWave_apply]
    push_cast
    ring
  rw [heq]
  exact (((((polynomialWeight_differentiable b R q) y).hasDerivAt.ofReal_comp).mul
    hf.hasDerivAt).const_mul _).differentiableAt

theorem topWeightedWave_covariant_continuous (f df : ℝ → SchwartzMap ℝ ℂ)
    (a r b R frequency : ℝ) (q : ℕ) (hR : 0 < R)
    (hf : Continuous (fun z : ℝ × ℝ => f z.1 z.2))
    (hdf : Continuous (fun z : ℝ × ℝ => df z.1 z.2))
    (hfd : ∀ x y, DifferentiableAt ℝ (fun t => f t x) y)
    (hcov : ∀ x y, (4*R:ℂ)*(deriv (fun t => f t x) y-(frequency:ℂ)*Complex.I*f y x) = df y x) :
    Continuous (fun z : ℝ × ℝ =>
      deriv (fun t => topWeightedWave (f t) a r b R t q z.2) z.1 -
        (frequency:ℂ)*Complex.I*topWeightedWave (f z.1) a r b R z.1 q z.2) := by
  have heq : (fun z : ℝ × ℝ =>
      deriv (fun t => topWeightedWave (f t) a r b R t q z.2) z.1 -
        (frequency:ℂ)*Complex.I*topWeightedWave (f z.1) a r b R z.1 q z.2) =
      (fun z : ℝ × ℝ => (4*R:ℂ)⁻¹*topCovariantWave (f z.1) (df z.1) a r b R z.1 q z.2) := by
    funext z
    rw [← topWeightedWave_covariant f df a r b R z.1 frequency z.2 q
      (hfd z.2 z.1) (hcov z.2 z.1)]
    rw [← mul_assoc, inv_mul_cancel₀, one_mul]
    exact mul_ne_zero (by norm_num) (by exact_mod_cast hR.ne')
  rw [heq]
  exact continuous_const.mul (topCovariantWave_jointContinuous f df a r b R q hf hdf)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeightedPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One common packet constant for the weighted wave and its constructed
scaled covariant derivative. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert

theorem topPairConstant_pos (C : ℝ) (q : ℕ) (hC : 0 < C) :
    0 < topPairConstant C q := by unfold topPairConstant; positivity

theorem topPairConstant_bounds (C : ℝ) (q : ℕ) (hC : 0 ≤ C) :
    16^q*(16^q*C) ≤ topPairConstant C q ∧
    16^q*(1+2*(q:ℝ))*(16^q*C) ≤ topPairConstant C q ∧
    (8*(q:ℝ)+1)*(16^q*(16^q*C)) ≤ topPairConstant C q := by
  have h1 : (1:ℝ) ≤ 1+2*(q:ℝ) := by nlinarith [show (0:ℝ) ≤ q from Nat.cast_nonneg q]
  have h8 : (1:ℝ) ≤ 8*(q:ℝ)+1 := by nlinarith [show (0:ℝ) ≤ q from Nat.cast_nonneg q]
  have hbase : 0 ≤ 16^q*(16^q*C) := by positivity
  have hder : 0 ≤ 16^q*(1+2*(q:ℝ))*(16^q*C) := by positivity
  have hb : 16^q*(16^q*C) ≤ 16^q*(1+2*(q:ℝ))*(16^q*C) := by
    convert le_mul_of_one_le_left hbase h1 using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hd : 16^q*(1+2*(q:ℝ))*(16^q*C) ≤ topPairConstant C q :=
    le_mul_of_one_le_left hder h8
  refine ⟨hb.trans hd, hd, ?_⟩
  exact mul_le_mul_of_nonneg_left hb (by positivity)

theorem topWeightedPair_bound (f : Fin 2 → SchwartzMap ℝ ℂ)
    (a r b R y s l t W C : ℝ) (q m n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hW : 0 < W) (hR : 0 < R)
    (hlr : l ≤ r) (hWR : W ≤ R) (hs : |s-a| ≤ r) (ht : |t-b| ≤ R) (hC : 0 ≤ C)
    (hf : ∀ i x, ‖f i x‖ ≤ C*(lineEnvelope s l (m+2*q) x*lineEnvelope t W (n+2*q) y))
    (i : Fin 2) (x : ℝ) :
    ‖topWeightedPair f a r b R y q i x‖ ≤
      topPairConstant C q*(lineEnvelope s l m x*lineEnvelope t W n y) := by
  have hconst := topPairConstant_bounds C q hC
  have henv : 0 ≤ lineEnvelope s l m x*lineEnvelope t W n y :=
    mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  fin_cases i
  · simpa [topWeightedPair] using
      (topWeightedWave_bound (f 0) a r b R y s l t W C q m n hl hr hW hR hlr hWR hs ht hC (hf 0) x).trans
        (mul_le_mul_of_nonneg_right hconst.1 henv)
  · simpa [topWeightedPair] using
      (topCovariantWave_bound (f 0) (f 1) a r b R y s l t W C q m n hl hr hW hR hlr hWR hs ht hC
        (hf 0) (hf 1) x).trans (mul_le_mul_of_nonneg_right hconst.2.2 henv)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteBandDerivative
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical differentiation commutes with the actual finite band sums.
The covariant derivative uses the same carrier in every band of a fixed
coordinate, so no carrier-frequency factor is lost. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem scalarBandPartial_hasDerivAt {N : ℕ} (F : Fin N → ℝ → ℂ)
    (n : ℕ) (y : ℝ) (hF : ∀ j, DifferentiableAt ℝ (F j) y) :
    HasDerivAt (scalarBandPartial F n)
      (scalarBandPartial (fun j => deriv (F j)) n y) y := by
  apply HasDerivAt.fun_sum
  intro j _
  by_cases hj : j.val < n
  · simpa only [hj, ite_true, if_true] using (hF j).hasDerivAt
  · simpa only [hj, ite_false, if_false] using (hasDerivAt_const y (0:ℂ))

theorem scalarBandPartial_covariant {N : ℕ} (F : Fin N → ℝ → ℂ)
    (n : ℕ) (frequency y : ℝ) (hF : ∀ j, DifferentiableAt ℝ (F j) y) :
    deriv (scalarBandPartial F n) y - (frequency:ℂ)*Complex.I*scalarBandPartial F n y =
      scalarBandPartial (fun j t => deriv (F j) t-(frequency:ℂ)*Complex.I*F j t) n y := by
  rw [(scalarBandPartial_hasDerivAt F n y hF).deriv]
  unfold scalarBandPartial
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem bandIntervalSignal_covariant {N : ℕ} {κ : Type*} [Fintype κ]
    (F : Fin N → κ → ℝ → ℂ) (a b : ℕ) (frequency : κ → ℝ) (y : ℝ)
    (hF : ∀ j k, DifferentiableAt ℝ (F j k) y) :
    covariantSignal frequency (fun k t => bandIntervalSignal F a b t k) y =
      bandIntervalSignal (fun j k t => deriv (F j k) t-
        (frequency k:ℂ)*Complex.I*F j k t) a b y := by
  ext k
  change deriv (fun t => scalarBandPartial (fun j => F j k) b t -
      scalarBandPartial (fun j => F j k) a t) y -
      (frequency k:ℂ)*Complex.I*(scalarBandPartial (fun j => F j k) b y -
        scalarBandPartial (fun j => F j k) a y) = _
  have hd := (scalarBandPartial_hasDerivAt (fun j => F j k) b y (fun j => hF j k)).sub
    (scalarBandPartial_hasDerivAt (fun j => F j k) a y (fun j => hF j k))
  change HasDerivAt (fun t => scalarBandPartial (fun j => F j k) b t -
    scalarBandPartial (fun j => F j k) a t) _ y at hd
  rw [hd.deriv]
  have hb := scalarBandPartial_covariant (fun j => F j k) b (frequency k) y (fun j => hF j k)
  have ha := scalarBandPartial_covariant (fun j => F j k) a (frequency k) y (fun j => hF j k)
  change _ = scalarBandPartial _ b y - scalarBandPartial _ a y
  rw [← hb, ← ha]
  rw [(scalarBandPartial_hasDerivAt (fun j => F j k) b y (fun j => hF j k)).deriv,
    (scalarBandPartial_hasDerivAt (fun j => F j k) a y (fun j => hF j k)).deriv]
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarPacketDifferentiation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact vertical derivatives of packet syntheses. Coefficients stay
fixed during differentiation, including when they are analyzing integrals. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

omit [Fintype κ] in
theorem planarPacketBand_hasDerivAt (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (j : Fin N) (k : κ) (x y : ℝ)
    (hw : ∀ i, DifferentiableAt ℝ (fun t => wave j i k t x) y) :
    HasDerivAt (planarPacketBand coeff wave j k x)
      (∑ i, coeff j i k * deriv (fun t => wave j i k t x) y) y := by
  apply HasDerivAt.fun_sum
  intro i _
  exact (hw i).hasDerivAt.const_mul _

omit [Fintype κ] in
theorem planarPacketBand_covariant (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (frequency : κ → ℝ)
    (j : Fin N) (k : κ) (x y : ℝ)
    (hw : ∀ i, DifferentiableAt ℝ (fun t => wave j i k t x) y) :
    deriv (planarPacketBand coeff wave j k x) y -
      (frequency k:ℂ)*Complex.I*planarPacketBand coeff wave j k x y =
    planarPacketBand coeff
      (fun j i k t s => deriv (fun z => wave j i k z s) t -
        (frequency k:ℂ)*Complex.I*wave j i k t s) j k x y := by
  rw [(planarPacketBand_hasDerivAt coeff wave j k x y hw).deriv]
  unfold planarPacketBand
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype κ] in
theorem planarPacketInterval_smul (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (s : ℝ) (a b : ℕ) (x y : ℝ) :
    planarPacketInterval coeff (fun j i k t z => (s:ℂ)*wave j i k t z) a b x y =
      s • planarPacketInterval coeff wave a b x y := by
  have hs (j : Fin N) (k : κ) :
      planarPacketBand coeff (fun j i k t z => (s:ℂ)*wave j i k t z) j k x y =
        (s:ℂ)*planarPacketBand coeff wave j k x y := by
    simp only [planarPacketBand, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hp (n : ℕ) (k : κ) :
      scalarBandPartial (fun j => planarPacketBand coeff
        (fun j i k t z => (s:ℂ)*wave j i k t z) j k x) n y =
      (s:ℂ)*scalarBandPartial (fun j => planarPacketBand coeff wave j k x) n y := by
    simp only [scalarBandPartial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp only [hs, mul_zero]
  ext k
  change _ = (s:ℂ)*(_-_)
  simp only [planarPacketInterval, bandIntervalSignal, WithLp.ofLp_toLp, hp, mul_sub]

theorem planarPacketInterval_covariant (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (frequency : κ → ℝ)
    (a b : ℕ) (x y : ℝ)
    (hw : ∀ j i k t, DifferentiableAt ℝ (fun z => wave j i k z x) t) :
    covariantSignal frequency (fun k t => planarPacketInterval coeff wave a b x t k) y =
    planarPacketInterval coeff
      (fun j i k t s => deriv (fun z => wave j i k z s) t -
        (frequency k:ℂ)*Complex.I*wave j i k t s) a b x y := by
  unfold planarPacketInterval
  rw [bandIntervalSignal_covariant _ _ _ _ _ (fun j k =>
    (planarPacketBand_hasDerivAt coeff wave j k x y (fun i => hw j i k y)).differentiableAt)]
  congr 1
  funext j k t
  exact planarPacketBand_covariant coeff wave frequency j k x t
    (fun i => hw j i k t)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarPacketContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint continuity and local square integrability for actual packet
interval sums and their covariant derivatives. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

omit [Fintype κ] in
theorem planarPacketBand_continuous (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ)
    (hw : ∀ j i k, Continuous (fun z : ℝ × ℝ => wave j i k z.1 z.2))
    (j : Fin N) (k : κ) :
    Continuous (fun z : ℝ × ℝ => planarPacketBand coeff wave j k z.2 z.1) := by
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hw j i k))

omit [Fintype κ] in
theorem planarPacketPartial_continuous (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ)
    (hw : ∀ j i k, Continuous (fun z : ℝ × ℝ => wave j i k z.1 z.2)) (n : ℕ) :
    Continuous (fun z : ℝ × ℝ => (WithLp.toLp 2 (fun k =>
      scalarBandPartial (fun j => planarPacketBand coeff wave j k z.2) n z.1) :
        EuclideanSpace ℂ κ)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val < n
  · simpa only [hj, ite_true, if_true] using planarPacketBand_continuous coeff wave hw j k
  · simpa only [hj, ite_false, if_false] using (continuous_const : Continuous (fun _ : ℝ × ℝ => (0:ℂ)))

theorem planarPacketInterval_continuous (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ)
    (hw : ∀ j i k, Continuous (fun z : ℝ × ℝ => wave j i k z.1 z.2)) (a b : ℕ) :
    Continuous (fun z : ℝ × ℝ => planarPacketInterval coeff wave a b z.2 z.1) := by
  convert (planarPacketPartial_continuous coeff wave hw b).sub
    (planarPacketPartial_continuous coeff wave hw a) using 1
  all_goals try with_reducible_and_instances rfl
  ext z k
  rfl

theorem planarPacketInterval_memLp (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ)
    (hw : ∀ j i k, Continuous (fun z : ℝ × ℝ => wave j i k z.1 z.2))
    (a b : ℕ) (x lower upper : ℝ) :
    MemLp (planarPacketInterval coeff wave a b x) 2 (volume.restrict (Icc lower upper)) := by
  have hplane := planarPacketInterval_continuous coeff wave hw a b
  have hc := hplane.comp (f := fun y : ℝ => (y,x))
    (continuous_id.prodMk continuous_const)
  change Continuous (planarPacketInterval coeff wave a b x) at hc
  exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    (hc.norm.pow 2).continuousOn.integrableOn_Icc

omit [Fintype κ] in
theorem planarPacketInterval_component_differentiable
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (a b : ℕ) (x y : ℝ) (k : κ)
    (hd : ∀ j i, DifferentiableAt ℝ (fun t => wave j i k t x) y) :
    DifferentiableAt ℝ (fun t => planarPacketInterval coeff wave a b x t k) y := by
  change DifferentiableAt ℝ (fun t =>
    scalarBandPartial (fun j => planarPacketBand coeff wave j k x) b t -
    scalarBandPartial (fun j => planarPacketBand coeff wave j k x) a t) y
  have hb (n : ℕ) := (scalarBandPartial_hasDerivAt
    (fun j => planarPacketBand coeff wave j k x) n y (fun j =>
      (planarPacketBand_hasDerivAt coeff wave j k x y (hd j)).differentiableAt)).differentiableAt
  exact (hb b).sub (hb a)

theorem planarPacketInterval_covariant_memLp
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (frequency : κ → ℝ)
    (hd : ∀ j i k x t, DifferentiableAt ℝ (fun z => wave j i k z x) t)
    (hD : ∀ j i k, Continuous (fun z : ℝ × ℝ =>
      deriv (fun t => wave j i k t z.2) z.1 - (frequency k:ℂ)*Complex.I*wave j i k z.1 z.2))
    (a b : ℕ) (x lower upper : ℝ) :
    MemLp (covariantSignal frequency (fun k t => planarPacketInterval coeff wave a b x t k))
      2 (volume.restrict (Icc lower upper)) := by
  let D := fun j i k t s => deriv (fun z => wave j i k z s) t -
    (frequency k:ℂ)*Complex.I*wave j i k t s
  have heq : covariantSignal frequency (fun k t => planarPacketInterval coeff wave a b x t k) =
      fun y => planarPacketInterval coeff D a b x y := by
    funext y
    exact planarPacketInterval_covariant coeff wave frequency a b x y (fun j i k => hd j i k x)
  have hDc : ∀ j i k, Continuous (fun z : ℝ × ℝ => D j i k z.1 z.2) := hD
  rw [heq]
  exact planarPacketInterval_memLp coeff D hDc a b x lower upper

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarPacketLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise multiplier identities for the actual finite planar packet
synthesis. A spatially varying multiplier is frozen at the evaluation
point before using linearity of the finite sum. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

omit [Fintype κ] in
theorem planarPacketInterval_congr_at (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f g : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (a b : ℕ) (x y : ℝ)
    (h : ∀ j i k, f j i k y x = g j i k y x) :
    planarPacketInterval coeff f a b x y = planarPacketInterval coeff g a b x y := by
  ext k
  simp only [planarPacketInterval, bandIntervalSignal, WithLp.ofLp_toLp,
    scalarBandPartial, planarPacketBand, h]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopCovariantData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A second raw covariant wave supplies the neighborhood estimate for
the first covariant derivative, while the analyzing coefficients stay fixed. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert

variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem planarPacketInterval_scaled_covariant_eq
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave replacement : ∀ j, ι j → κ → ℝ → ℝ → ℂ)
    (frequency : κ → ℝ) (s : ℝ) (a b : ℕ) (x y : ℝ)
    (hd : ∀ j u k t, DifferentiableAt ℝ (fun z => wave j u k z x) t)
    (hcov : ∀ j u k, (s:ℂ)*(deriv (fun z => wave j u k z x) y -
      (frequency k:ℂ)*Complex.I*wave j u k y x) = replacement j u k y x) :
    s • covariantSignal frequency (fun k t => planarPacketInterval coeff wave a b x t k) y =
      planarPacketInterval coeff replacement a b x y := by
  rw [planarPacketInterval_covariant coeff wave frequency a b x y hd,
    ← planarPacketInterval_smul]
  exact planarPacketInterval_congr_at coeff _ replacement a b x y hcov

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed polynomial threshold pays for both the raw packet constant
and the moment order, before choosing any finite family or later mask. -/

noncomputable section
namespace LipschitzHilbert

theorem topAreaPrefactor_one_le : 1 ≤ topAreaPrefactor 1 := by
  unfold topAreaPrefactor
  nlinarith [Real.pi_pos, Real.two_le_pi]

theorem topAreaPrefactor_scale (K : ℝ) :
    topAreaPrefactor K = topAreaPrefactor 1*K^2 := by
  unfold topAreaPrefactor
  ring

theorem topExceptionMoment_power_le (J a L : ℝ) (hJ : 0 ≤ J)
    (ha : 0 ≤ a) (hL : 1 ≤ L) :
    (topExceptionMoment (topAreaPrefactor (L^a)) J L:ℝ) ≤
      ((J+Real.log (topAreaPrefactor 1)+2*a)/Real.log 4+2)*L := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hK : 1 ≤ L^a := Real.one_le_rpow hL ha
  have hC := topAreaPrefactor_one_le
  have hM : 1 ≤ topAreaPrefactor (L^a) := by
    rw [topAreaPrefactor_scale]
    have hs : (1:ℝ) ≤ (L^a)^2 := one_le_pow₀ hK
    nlinarith
  have hlogbound : Real.log (topAreaPrefactor (L^a)) ≤
      (Real.log (topAreaPrefactor 1)+2*a)*L := by
    rw [topAreaPrefactor_scale (L^a), Real.log_mul (by positivity : topAreaPrefactor 1 ≠ 0)
      (by positivity : (L^a)^2 ≠ 0), Real.log_pow, Real.log_rpow hL0]
    have hlog : Real.log L ≤ L := Real.log_le_self hL0.le
    have hlogC := Real.log_nonneg hC
    norm_num only [Nat.cast_ofNat]
    calc
      _ = Real.log (topAreaPrefactor 1)+(2*a)*Real.log L := by ring
      _ ≤ Real.log (topAreaPrefactor 1)*L+(2*a)*L :=
        add_le_add (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hL hlogC)
          (mul_le_mul_of_nonneg_left hlog (by positivity))
      _ = _ := by ring
  simpa only [add_assoc] using topExceptionMoment_le (topAreaPrefactor (L^a)) J L
    (Real.log (topAreaPrefactor 1)+2*a) hJ hL hM hlogbound

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeightedInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed polynomial weights commute exactly with the actual finite
interval synthesis, without changing the analyzing coefficients. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

omit [Fintype κ] in
theorem planarPacketInterval_commonWeight
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (w : ℝ → ℝ → ℝ)
    (a b : ℕ) (x y : ℝ) :
    planarPacketInterval coeff (fun j u k t z => (w z t:ℂ)*wave j u k t z) a b x y =
      w x y • planarPacketInterval coeff wave a b x y := by
  have h := planarPacketInterval_smul coeff wave (w x y) a b x y
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext k
  rfl

omit [Fintype κ] in
theorem planarPacketInterval_topWeighted
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
    (u r v R : ℝ) (q : ℕ) (a b : ℕ) (x y : ℝ) :
    planarPacketInterval coeff (fun j i k t z => topWeightedWave (wave j i k t) u r v R t q z)
      a b x y = (polynomialWeight u r q x*polynomialWeight v R q y) •
        planarPacketInterval coeff (fun j i k t z => wave j i k t z) a b x y := by
  simp_rw [topWeightedWave_apply]
  exact planarPacketInterval_commonWeight coeff _
    (fun x y => polynomialWeight u r q x*polynomialWeight v R q y) a b x y

theorem planarPacketInterval_topWeighted_norm
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
    (u r v R : ℝ) (q : ℕ) (a b : ℕ) (x y : ℝ) :
    ‖planarPacketInterval coeff (fun j i k t z => topWeightedWave (wave j i k t) u r v R t q z)
      a b x y‖ = (polynomialWeight u r q x*polynomialWeight v R q y) *
        ‖planarPacketInterval coeff (fun j i k t z => wave j i k t z) a b x y‖ := by
  rw [planarPacketInterval_topWeighted, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))
      (zero_le_one.trans (polynomialWeight_one_le _ _ _ _)))]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceErrorSupported
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Error moments on a reference interval only use retained packet
lengths. Empty longer scales do not enlarge the interval. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.LineErrorSources
attribute [local instance] Classical.propDecidable
variable {N : ℕ}

theorem restrictLength_source_zero (P : LineErrorSources N) (H : ℝ) (j : Fin N)
    (h : H < (P.restrictLength H).length j) : (P.restrictLength H).source j = 0 := by
  have hn : ¬ P.length j ≤ H := not_le.mpr h
  funext x
  simp only [restrictLength,ite_eq_right hn,Pi.zero_apply]

theorem majorant_root_integral_of_supported (P : LineErrorSources N) (g : FiniteLineGrid)
    (hsource : ∀ j, g.width < P.length j → P.source j = 0) :
    (∫ x, P.majorant x ∂g.lineMeasure) ≤ P.meanConstant*g.width := by
  have heq : P.shortPart g.width = P.majorant := by
    funext x
    unfold shortPart majorant
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : P.length j ≤ g.width
    · exact ite_eq_left h
    · rw [ite_eq_right h]
      simp only [term,hsource j (lt_of_not_ge h),positiveConvolution]
      simp
  have h := P.shortPart_integral g.origin g.width g.width_pos
  rw [heq] at h
  have hi : IntegrableOn P.majorant (Icc (g.origin-g.width) (g.origin+g.width)) :=
    P.majorant_continuous.continuousOn.integrableOn_Icc
  have hsub : g.root ⊆ Icc (g.origin-g.width) (g.origin+g.width) := by
    intro x hx
    exact ⟨by linarith [hx.1,g.width_pos],hx.2.le⟩
  exact (setIntegral_mono_set hi (Filter.Eventually.of_forall P.majorant_nonneg)
    (Filter.Eventually.of_forall (fun _ hx => hsub hx))).trans h

theorem majorant_mean_of_supported (P : LineErrorSources N) (g : FiniteLineGrid)
    (hsource : ∀ j, g.width < P.length j → P.source j = 0) :
    |integralAverage g.lineMeasure P.majorant| ≤ P.meanConstant := by
  have hmass : g.lineMeasure.real univ = g.width := by
    change (volume.restrict g.root).real univ = g.width
    simpa only [g.cell_zero,FiniteLineGrid.meshWidth,pow_zero,div_one] using g.cell_mass 0 0
  rw [integralAverage,smul_eq_mul,abs_mul,abs_of_nonneg (inv_nonneg.mpr measureReal_nonneg),
    abs_of_nonneg (integral_nonneg P.majorant_nonneg),hmass]
  calc
    _ ≤ g.width⁻¹*(P.meanConstant*g.width) := mul_le_mul_of_nonneg_left
      (P.majorant_root_integral_of_supported g hsource) (inv_nonneg.mpr g.width_pos.le)
    _ = _ := by field_simp [g.width_pos.ne']

theorem majorant_moment_of_supported (P : LineErrorSources N) (g : FiniteLineGrid)
    (hb : 1 < g.branching) (hsource : ∀ j, g.width < P.length j → P.source j = 0)
    {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, (ENNReal.ofReal (P.majorant x))^p ∂g.lineMeasure) ≤
      (2:ℝ≥0∞)^p*(7*ENNReal.ofReal
        ((p*(((g.branching:ℝ)+2)*(2*P.meanConstant+P.oscillationConstant+1))/Real.log (3/2))^p)+
        (ENNReal.ofReal P.meanConstant)^p)*g.lineMeasure univ := by
  have hi : Integrable P.majorant g.lineMeasure := by
    have h := g.continuous_integrable_cell P.majorant_continuous 0 0
    rwa [g.cell_zero] at h
  have hmean : 0 ≤ P.meanConstant := by
    unfold meanConstant
    exact mul_nonneg (by positivity) P.sumBound_nonneg
  have hosc : 0 ≤ P.oscillationConstant := by
    unfold oscillationConstant
    exact mul_nonneg (by positivity) P.sourceBound_nonneg
  have hA : 0 < 2*P.meanConstant+P.oscillationConstant+1 := by positivity
  have hBMO : g.HasFullMeanOscillationBound P.majorant
      (2*P.meanConstant+P.oscillationConstant+1) := by
    intro level i hi
    exact (P.majorant_mean_oscillation g level i hi).trans
      (mul_le_mul_of_nonneg_right (by linarith) (g.meshWidth_pos level).le)
  have h := g.continuous_raw_moment hb P.majorant P.majorant_continuous.measurable hi
    (fun _ _ => P.majorant_continuous.continuousAt) hA hBMO
    (P.majorant_mean_of_supported g hsource) hp
  simpa only [abs_of_nonneg (P.majorant_nonneg _)] using h

end LipschitzHilbert.LineErrorSources

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceErrorTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial thresholds for the actual positive convolution error.
Only the source bound and its logarithmic scale sum enter the constants. -/

noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal Topology
namespace LipschitzHilbert.LineErrorSources

variable {N : ℕ}

theorem momentBase_pos (P : LineErrorSources N) (grid : FiniteLineGrid) :
    0 < P.momentBase grid := by
  have hsum := P.sumBound_nonneg
  have hsource := P.sourceBound_nonneg
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  unfold momentBase meanConstant oscillationConstant
  positivity

theorem majorant_moment_natural (P : LineErrorSources N) (grid : FiniteLineGrid)
    (hb : 1 < grid.branching) (hsource : ∀ j, grid.width < P.length j → P.source j = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    (∫⁻ x, (ENNReal.ofReal (P.majorant x))^n ∂grid.lineMeasure) ≤
      ENNReal.ofReal ((P.momentBase grid*(n:ℝ))^n)*grid.lineMeasure univ := by
  have hmean : 0 ≤ P.meanConstant := by
    unfold meanConstant
    exact mul_nonneg (by positivity) P.sumBound_nonneg
  have hosc : 0 ≤ P.oscillationConstant := by
    unfold oscillationConstant
    exact mul_nonneg (by positivity) P.sourceBound_nonneg
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  have h := ennreal_polynomial_moment_majorant
    ((((grid.branching:ℝ)+2)*(2*P.meanConstant+P.oscillationConstant+1))/Real.log (3/2))
    P.meanConstant (by positivity) hmean n hn
  have hm := P.majorant_moment_of_supported grid hb hsource (p := n) (Nat.cast_nonneg n)
  simp only [ENNReal.rpow_natCast] at hm
  exact hm.trans (mul_le_mul' (by simpa only [momentBase,mul_div_assoc,ENNReal.rpow_natCast] using h) le_rfl)

end LipschitzHilbert.LineErrorSources

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularErrorTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The wide source cone costs only the proved logarithmic source sum.
Empty scales are removed before the reference-interval moment estimate. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert

namespace LineErrorSources
variable {N : ℕ}

theorem restrictLength_term_eq (P : LineErrorSources N) (H : ℝ) (j : Fin N) (x : ℝ) :
    (P.restrictLength H).term j x = if P.length j ≤ H then P.term j x else 0 := by
  change positiveConvolution (P.length j)
    (fun x => if P.length j ≤ H then P.source j x else 0) x =
      if P.length j ≤ H then positiveConvolution (P.length j) (P.source j) x else 0
  by_cases h : P.length j ≤ H
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h,positiveConvolution,mul_zero,integral_zero]

end LineErrorSources

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlopeLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The slope-label multiplicity assumption in §2 of the manuscript
gives a uniform number of labels active at a fixed source direction.
This includes vector-valued selectors: taking the union over all bin
components does not increase the count.  The last lemmas split the
active labels at every scale into a fixed finite set of lattice slots. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.SourceSlopeLabels

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

theorem window_card_le (labels : Finset ι) (slope : ι → ℝ)
    {t d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : LocalMultiplicity labels slope d M) (hK : radius ≤ K) :
    (window labels slope t d radius).card ≤ (2 * K + 1) * M := by
  classical
  let active := window labels slope t d radius
  let bin : ι → ℤ := fun i => ⌊(slope i - t) / d⌋
  let bins : Finset ℤ := Finset.Icc (-(K : ℤ)) K
  have hmaps : (active : Set ι).MapsTo bin bins := by
    intro i hi
    have hwin : |slope i - t| ≤ radius * d := (Finset.mem_filter.mp hi).2
    have habs : |slope i - t| ≤ (K : ℝ) * d :=
      hwin.trans (mul_le_mul_of_nonneg_right hK hd.le)
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    have hlow : -(K : ℝ) ≤ (slope i - t) / d := by
      apply (le_div_iff₀ hd).mpr
      linarith
    have hupp : (slope i - t) / d < (K : ℝ) + 1 := by
      apply (div_lt_iff₀ hd).mpr
      nlinarith
    exact Finset.mem_Icc.mpr ⟨Int.le_floor.mpr (by simpa using hlow),
      Int.floor_le_iff.mpr (by simpa using hupp)⟩
  have hfiber (b : ℤ) : (active.filter (fun i => bin i = b)).card ≤ M := by
    apply (Finset.card_le_card (show active.filter (fun i => bin i = b) ⊆
      labels.filter (fun i => t + (b : ℝ) * d ≤ slope i ∧
        slope i < (t + (b : ℝ) * d) + d) from ?_)).trans
      (hlocal (t + (b : ℝ) * d))
    intro i hi
    obtain ⟨hia, hib⟩ := Finset.mem_filter.mp hi
    have hil : i ∈ labels := (Finset.mem_filter.mp hia).1
    have h0 := Int.floor_le ((slope i - t) / d)
    have h1 := Int.lt_floor_add_one ((slope i - t) / d)
    change ⌊(slope i - t) / d⌋ = b at hib
    rw [hib] at h0 h1
    have h0' := (le_div_iff₀ hd).mp h0
    have h1' := (div_lt_iff₀ hd).mp h1
    exact Finset.mem_filter.mpr ⟨hil, by constructor <;> nlinarith⟩
  have hcount : bins.card = 2 * K + 1 := by
    have hcount' : (bins.card : ℤ) = 2 * (K : ℤ) + 1 := by
      dsimp [bins]
      rw [Int.card_Icc_of_le (a := -(K : ℤ)) (b := (K : ℤ)) (by omega)]
      omega
    exact_mod_cast hcount'
  calc
    active.card = ∑ b ∈ bins, (active.filter (fun i => bin i = b)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _b ∈ bins, M := Finset.sum_le_sum fun b _ => hfiber b
    _ = (2 * K + 1) * M := by simp [hcount]

theorem active_card_le (labels : Finset ι) (slope : ι → ℝ)
    {κ : Type*} (selector : ι → κ → ℝ → ℂ)
    {t d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : LocalMultiplicity labels slope d M) (hK : radius ≤ K)
    (hsupport : ∀ i ∈ labels, ∀ k, selector i k t ≠ 0 →
      |t - slope i| ≤ radius * d) :
    (active labels selector t).card ≤ (2 * K + 1) * M := by
  classical
  apply (Finset.card_le_card (show active labels selector t ⊆
    window labels slope t d radius from ?_)).trans
    (window_card_le labels slope hd hlocal hK)
  intro i hi
  obtain ⟨hil, k, hk⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hil, by simpa only [abs_sub_comm] using hsupport i hil k hk⟩

/-- For coefficient errors the original and frozen selectors contribute
at most twice the same absolute label bound. -/
theorem active_union_card_le (labels : Finset ι) (slope : ι → ℝ)
    {κ : Type*} (selector : ι → κ → ℝ → ℂ)
    {t u d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : LocalMultiplicity labels slope d M) (hK : radius ≤ K)
    (hsupport : ∀ i ∈ labels, ∀ k x, selector i k x ≠ 0 →
      |x - slope i| ≤ radius * d) :
    ((active labels selector u) ∪ (active labels selector t)).card ≤
      2 * ((2 * K + 1) * M) := by
  classical
  calc
    _ ≤ (active labels selector u).card + (active labels selector t).card :=
      Finset.card_union_le _ _
    _ ≤ (2 * K + 1) * M + (2 * K + 1) * M := Nat.add_le_add
      (active_card_le labels slope selector hd hlocal hK (fun i hi k => hsupport i hi k u))
      (active_card_le labels slope selector hd hlocal hK (fun i hi k => hsupport i hi k t))
    _ = _ := by omega

end LipschitzHilbert.SourceSlopeLabels

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSingleScaleEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The single-scale estimate in §5, `conc:original-positive`.
The lattice estimate is summed at the source point before integrating.
Only pointwise overlap of the label multipliers appears, so the estimate
has no factor counting the available labels. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem planarPositiveConvolution_sum {Λ : Type*} [Fintype Λ]
    (f : Λ → ℝ×ℝ → ℝ) (hf : ∀ b, Measurable (f b))
    {l W B : ℝ} (hl : 0 < l) (hW : 0 < W)
    (hbound : ∀ b z, ‖f b z‖ ≤ B) (x y : ℝ) :
    planarPositiveConvolution l W (fun z => ∑ b, f b z) x y =
      ∑ b, planarPositiveConvolution l W (f b) x y := by
  unfold planarPositiveConvolution
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun b _ =>
    planarPositiveConvolution_integrable l W (f b) (hf b) hl hW (hbound b) x y)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledErrorConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular errors are summed over their active labels at the source
point, before the lattice convolution. Consequently the wide reference
cone contributes no factor counting all available labels. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

/-- Pointwise domination of the sum of sources passes through the
common positive convolution, with the same constant. -/
theorem sum_planarPositiveConvolution_le_source {Λ : Type*} [Fintype Λ]
    (f : Λ → ℝ×ℝ → ℝ) (hf : ∀ b, Measurable (f b)) (hf0 : ∀ b z, 0 ≤ f b z)
    (source : ℝ×ℝ → ℝ) (hs : Measurable source) (hs0 : ∀ z, 0 ≤ source z)
    {l W C B : ℝ} (hl : 0 < l) (hW : 0 < W) (hC : 0 ≤ C) (_hB : 0 ≤ B)
    (hsB : ∀ z, source z ≤ B) (hoverlap : ∀ z, ∑ b, f b z ≤ C*source z)
    (x y : ℝ) :
    (∑ b, planarPositiveConvolution l W (f b) x y) ≤
      C*planarPositiveConvolution l W source x y := by
  have hsum0 (z : ℝ×ℝ) : 0 ≤ ∑ b, f b z := Finset.sum_nonneg (fun b _ => hf0 b z)
  have hsumB (z : ℝ×ℝ) : (∑ b, f b z) ≤ C*B :=
    (hoverlap z).trans (mul_le_mul_of_nonneg_left (hsB z) hC)
  have hfb (b : Λ) (z : ℝ×ℝ) : ‖f b z‖ ≤ C*B := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hf0 b z)]
    exact (Finset.single_le_sum (fun a _ => hf0 a z) (Finset.mem_univ b)).trans (hsumB z)
  rw [← planarPositiveConvolution_sum f hf hl hW hfb]
  calc
    _ ≤ planarPositiveConvolution l W (fun z => C*source z) x y := by
      apply integral_mono
        (planarPositiveConvolution_integrable l W _
          (Finset.measurable_sum _ (fun b _ => hf b)) hl hW
          (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (hsum0 z)]; exact hsumB z) x y)
        (planarPositiveConvolution_integrable l W _ (hs.const_mul C) hl hW
          (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hC (hs0 z))]
                       exact mul_le_mul_of_nonneg_left (hsB z) hC) x y)
      intro z
      exact mul_le_mul_of_nonneg_left (hoverlap z)
        (mul_nonneg (lineKernel_nonneg _ _ hl) (lineKernel_nonneg _ _ hW))
    _ = _ := planarPositiveConvolution_const_mul l W C source x y

/-- The actual coefficient error for a finite family of translated
lattices. Only active selector labels enter the source overlap. -/
theorem source_labeled_error_convolution {Λ κ : Type*} [Fintype Λ] [Fintype κ]
    (ι : Λ → Type*) [∀ b, Fintype (ι b)]
    (site : ∀ b, ι b → ℤ×ℤ) (hinj : ∀ b, Function.Injective (site b))
    (originX originY slope : Λ → ℝ) {l W d radius C M Lip small wide : ℝ} {K H : ℕ}
    (hl : 0 < l) (hW : 0 < W) (hd : 0 < d)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hLip : 0 ≤ Lip)
    (hsmall : 0 < small) (hsmall1 : small ≤ 1) (hwide : 1 ≤ wide)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ slope d H) (hK : radius ≤ K)
    (selector : Λ → κ → ℝ → ℂ) (hselector : ∀ b k, Measurable (selector b k))
    (hselectorBound : ∀ b k s, ‖selector b k s‖ ≤ M)
    (hsupport : ∀ b k s, selector b k s ≠ 0 → |s-slope b| ≤ radius*d)
    (direction : ℝ×ℝ → ℝ) (hdirection : Measurable direction) (t : ℝ)
    (hnear : ∀ b k s, |s-t| ≤ small*d →
      ‖selector b k s-selector b k t‖ ≤ Lip*(|s-t|/d))
    (hfar : ∀ b k s, wide*d < |s-t| → selector b k s = 0)
    (wave : ∀ b, ι b → κ → ℝ×ℝ → ℂ) (hwave : ∀ b i k, Measurable (wave b i k))
    (hwaveBound : ∀ b i k z, ‖wave b i k z‖ ≤
      C*tileEnvelope (originX b+l*(site b i).1) (originY b+W*(site b i).2) l W 6 z)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (z : ℝ×ℝ) :
    (∑ b, ∑ i, ‖analyzingCoefficient volume (fun _ : ι b => l*W)
      (angularErrorWave (fun _ k => selector b k) (wave b) direction t d) g i‖*
      tileEnvelope (originX b+l*(site b i).1) (originY b+W*(site b i).2) l W 6 z) ≤
      (64*(4*Real.pi)^2)*
        (2*((2*K+1)*H):ℕ)*
        planarPositiveConvolution l W
          (fun p => (C*(2*M+Lip))*errorSourceProfile small wide d |direction p-t|) z.1 z.2 := by
  classical
  let active := fun (b : Λ) (p : ℝ×ℝ) =>
    (∃ k, selector b k (direction p) ≠ 0) ∨ (∃ k, selector b k t ≠ 0)
  let common := fun p : ℝ×ℝ => (C*(2*M+Lip))*errorSourceProfile small wide d |direction p-t|
  let source := fun b p => if active b p then common p else 0
  have hA : 0 ≤ C*(2*M+Lip) := mul_nonneg hC (by linarith)
  have hcommon0 (p : ℝ×ℝ) : 0 ≤ common p :=
    mul_nonneg hA (errorSourceProfile_nonneg _ _ _ _ hd (abs_nonneg _))
  have hcommon : Measurable common := by
    apply Measurable.const_mul
    apply errorSourceProfile_measurable
    simpa only [Real.norm_eq_abs] using (hdirection.sub_const t).norm
  have hcommonB (p : ℝ×ℝ) : common p ≤ (C*(2*M+Lip))*(1+small) :=
    mul_le_mul_of_nonneg_left (errorSourceProfile_bound _ _ _ _ hsmall hd (abs_nonneg _)) hA
  have hsource0 (b : Λ) (p : ℝ×ℝ) : 0 ≤ source b p := by
    dsimp [source]
    split_ifs
    · exact hcommon0 p
    · exact le_rfl
  have hsourceMeas (b : Λ) : Measurable (source b) := by
    have ha : MeasurableSet {p : ℝ×ℝ | ∃ k, selector b k (direction p) ≠ 0} := by
      have heq : {p : ℝ×ℝ | ∃ k, selector b k (direction p) ≠ 0} =
          ⋃ k : κ, {p | selector b k (direction p) ≠ 0} := by ext p; simp
      rw [heq]
      exact MeasurableSet.iUnion fun k =>
        (measurableSet_eq_fun ((hselector b k).comp hdirection) measurable_const).compl
    have hb : MeasurableSet {p : ℝ×ℝ | ∃ k, selector b k t ≠ 0} := by
      by_cases hb : ∃ k, selector b k t ≠ 0 <;> simp [hb]
    exact Measurable.ite (ha.union hb) hcommon measurable_const
  have hoverlap (p : ℝ×ℝ) : (∑ b, source b p) ≤ (2*((2*K+1)*H):ℕ)*common p := by
    let U := SourceSlopeLabels.active Finset.univ selector (direction p) ∪
      SourceSlopeLabels.active Finset.univ selector t
    have hmem (b : Λ) : active b p ↔ b ∈ U := by
      simp only [active,U,SourceSlopeLabels.active,Finset.mem_union,Finset.mem_filter,
        Finset.mem_univ,true_and]
    have hsum : (∑ b, source b p) = (U.card:ℝ)*common p := by
      simp only [source,hmem]
      rw [← Finset.sum_filter]
      have heq : Finset.univ.filter (fun b => b ∈ U) = U := by ext b; simp
      rw [heq]
      simp only [Finset.sum_const,nsmul_eq_mul]
    rw [hsum]
    apply mul_le_mul_of_nonneg_right _ (hcommon0 p)
    exact_mod_cast SourceSlopeLabels.active_union_card_le Finset.univ slope selector
      hd hlocal hK (fun b _ k s => hsupport b k s)
  have hbound (b : Λ) (i : ι b) (k : κ) (p : ℝ×ℝ) :
      ‖angularErrorWave (fun _ k => selector b k) (wave b) direction t d i k p‖ ≤
        tileEnvelope (originX b+l*(site b i).1) (originY b+W*(site b i).2) l W 6 p*source b p := by
    by_cases ha : active b p
    · have he := multiplierError_bound (selector b k) t d small wide M Lip (direction p)
        hd hsmall hsmall1 hwide hM hLip (hselectorBound b k)
        (hnear b k (direction p)) (hfar b k (direction p))
      rw [angularErrorWave,norm_mul]
      have hm := mul_le_mul he (hwaveBound b i k p) (norm_nonneg _)
        (mul_nonneg (by linarith) (errorSourceProfile_nonneg _ _ _ _ hd (abs_nonneg _)))
      convert hm using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [source,common]
      rw [ite_eq_left ha]
      ring
    · have hu : selector b k (direction p) = 0 := by
        by_contra hu
        exact ha (Or.inl ⟨k,hu⟩)
      have ht : selector b k t = 0 := by
        by_contra ht
        exact ha (Or.inr ⟨k,ht⟩)
      simp only [angularErrorWave,multiplierError,hu,ht,ite_self,sub_self,zero_mul,norm_zero]
      exact mul_nonneg (tileEnvelope_nonneg _ _ _ _ _ _) (hsource0 b p)
  have hB : 0 ≤ (C*(2*M+Lip))*(1+small) := mul_nonneg hA (by linarith)
  have hfb (b : Λ) (p : ℝ×ℝ) : ‖source b p‖ ≤ (C*(2*M+Lip))*(1+small) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hsource0 b p)]
    dsimp [source]
    split_ifs
    · exact hcommonB p
    · exact hB
  calc
    _ ≤ ∑ b, (64*(4*Real.pi)^2)*planarPositiveConvolution l W (source b) z.1 z.2 := by
      apply Finset.sum_le_sum
      intro b _
      exact lattice_coefficient_convolution (site b) (hinj b) (originX b) (originY b) l W
        hl hW (source b) (hsourceMeas b) (hsource0 b) (hfb b)
        _ (angularErrorWave_measurable _ _ _ _ _ (fun i k => hselector b k) (hwave b) hdirection)
        (hbound b) g hg hg1 z
    _ = (64*(4*Real.pi)^2)*∑ b, planarPositiveConvolution l W (source b) z.1 z.2 :=
      (Finset.mul_sum ..).symm
    _ ≤ (64*(4*Real.pi)^2)*((2*((2*K+1)*H):ℕ)*planarPositiveConvolution l W common z.1 z.2) :=
      mul_le_mul_of_nonneg_left
        (sum_planarPositiveConvolution_le_source source hsourceMeas hsource0 common hcommon hcommon0
          hl hW (by positivity) hB hcommonB hoverlap z.1 z.2) (by positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledErrorFamily
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic angular errors on translated lattices with bounded local
multiplicity of slope labels. The common source is counted before integration. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

namespace LabeledAngularErrorFamily
variable {N : ℕ} {Λ : Fin N → Type} {κ : Type} {ι : ∀ j, Λ j → Type}
  [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]

theorem scaleError_le (P : LabeledAngularErrorFamily N Λ κ ι) (j : Fin N) (y x : ℝ) :
    P.scaleError j y x ≤ (P.sources y).term j x := by
  have h := source_labeled_error_convolution (ι j) (P.site j) (P.site_injective j)
    (P.originX j) (P.originY j) (P.slope j)
    (div_pos P.topLength_pos (pow_pos (by norm_num) _)) P.width_pos
    (mul_pos P.angleBase_pos (pow_pos (by norm_num) _))
    P.packetBound_nonneg P.multiplierBound_nonneg P.multiplierLip_nonneg
    P.smallRatio_pos P.smallRatio_le P.wideRatio_ge (P.localMultiplicity j) P.radius_le
    (P.multiplier j) (P.multiplier_measurable j) (P.multiplier_bounded j)
    (P.multiplier_support j) P.direction P.direction_measurable P.referenceSlope
    (P.multiplier_near j) (P.multiplier_far j) (P.wave j) (P.wave_measurable j)
    (P.wave_bound j) P.test P.test_measurable P.test_bound (x,y)
  change P.scaleError j y x ≤ _ at h
  apply h.trans_eq
  rw [sources,actualErrorSources_term_eq]
  rw [← planarPositiveConvolution_const_mul]
  congr 1
  funext z
  unfold sourceAmplitude
  ring

theorem scaleError_nonneg (P : LabeledAngularErrorFamily N Λ κ ι) (j : Fin N) (y x : ℝ) :
    0 ≤ P.scaleError j y x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (norm_nonneg _) (tileEnvelope_nonneg _ _ _ _ _ _)

theorem error_nonneg (P : LabeledAngularErrorFamily N Λ κ ι) (y x : ℝ) :
    0 ≤ P.error y x := Finset.sum_nonneg fun j _ => P.scaleError_nonneg j y x

theorem sources_log_budget (P : LabeledAngularErrorFamily N Λ κ ι) (y : ℝ) :
    (P.sources y).sumBound =
      (P.sourceAmplitude*((P.wideExponent+1:ℕ)+4*P.smallRatio+
        (4/Real.log 2)*Real.log ((2:ℝ)^P.exponent)))*Real.pi :=
  actualErrorSources_log_sumBound P.wideExponent P.exponent P.direction P.direction_measurable
    P.referenceSlope P.angleBase P.smallRatio P.wideConstant P.sourceAmplitude P.topLength P.width y
    P.angleBase_pos P.smallRatio_pos P.sourceAmplitude_nonneg P.wideConstant_le P.topLength_pos P.width_pos

end LabeledAngularErrorFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledErrorTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded active-label overlap gives the same logarithmic dyadic
source budget and exponential error tail, with no total-label count. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert

namespace LabeledAngularErrorFamily
variable {N : ℕ} {Λ : Fin N → Type} {κ : Type} {ι : ∀ j, Λ j → Type}
  [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]

/-- Every actual packet is short, even if the original index horizon
contains empty longer scales. -/
theorem error_le_restricted_majorant (P : LabeledAngularErrorFamily N Λ κ ι) (H : ℝ)
    (hshort : ∀ j b (_u : ι j b), P.length j ≤ H) (y x : ℝ) :
    P.error y x ≤ ((P.sources y).restrictLength H).majorant x := by
  apply Finset.sum_le_sum
  intro j _
  rw [LineErrorSources.restrictLength_term_eq]
  change P.scaleError j y x ≤ if P.length j ≤ H then (P.sources y).term j x else 0
  by_cases h : P.length j ≤ H
  · rw [ite_eq_left h]
    exact P.scaleError_le j y x
  · rw [ite_eq_right h]
    have heq : P.scaleError j y x = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      apply Finset.sum_eq_zero
      intro u _
      exact False.elim (h (hshort j b u))
    exact le_of_eq heq

/-- The exact dyadic source branching gives polynomial error-source
budgets without any dependence on the wide carrier constant. -/
theorem eventually_source_error_budgets (p : ℝ) (J₀ : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (Λ : Fin N → Type) (κ : Type) (ι : ∀ j, Λ j → Type)
      [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)] (P : LabeledAngularErrorFamily N Λ κ ι),
      P.sourceAmplitude ≤ L^p → P.wideExponent ≤ J₀ →
      P.exponent = SourceParameters.stepExponent L*SourceParameters.blockCount L →
      ∀ y, (P.sources y).sourceBound ≤ L^(p+3) ∧ (P.sources y).sumBound ≤ L^(p+3) := by
  let c : ℝ := (J₀+1:ℕ)+4+4/Real.log 2
  have hc : 0 < c := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [c]
    positivity
  filter_upwards [SourceParameters.eventually_branching_separation,
    eventually_ge_atTop (max 1 (max (2*Real.pi) (c*Real.pi)))] with L hsep hlarge
  have hL : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hpi : 2*Real.pi ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hcpi : c*Real.pi ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hlogB : Real.log (SourceParameters.branching L) ≤ L := by
    have h := Real.log_le_log (pow_pos (SourceParameters.branching_pos L) 100) hsep
    rw [Real.log_pow,Real.log_exp] at h
    have hpow : L^(9/10:ℝ) ≤ L := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL
        (by norm_num : (9/10:ℝ) ≤ 1)
    norm_num only [Nat.cast_ofNat] at h
    linarith
  intro N Λ κ ι _ _ _ P hP hJ hE y
  have hAmp := P.sourceAmplitude_nonneg
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : (P.sources y).sourceBound ≤ 2*Real.pi*L^p := by
    change (P.sourceAmplitude*(1+P.smallRatio))*Real.pi ≤ _
    have h := mul_le_mul hP (add_le_add_left P.smallRatio_le 1)
      (by linarith [P.smallRatio_pos]) (Real.rpow_nonneg hL0.le p)
    calc
      _ = (P.sourceAmplitude*(P.smallRatio+1))*Real.pi := by ring
      _ ≤ (L^p*(1+1))*Real.pi := mul_le_mul_of_nonneg_right h Real.pi_pos.le
      _ = _ := by ring
  have hwide : ((P.wideExponent+1:ℕ):ℝ)+4*P.smallRatio+
      (4/Real.log 2)*Real.log ((2:ℝ)^P.exponent) ≤ c*L := by
    have hJ' : ((P.wideExponent+1:ℕ):ℝ) ≤ (J₀+1:ℕ) := by exact_mod_cast Nat.add_le_add_right hJ 1
    have hlog : Real.log ((2:ℝ)^P.exponent) ≤ L := by
      rw [hE,← source_branching_eq_two_pow]
      exact hlogB
    have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 4/Real.log 2)
    have hsmall := P.smallRatio_le
    have hconstant := mul_le_mul_of_nonneg_left hL
      (show 0 ≤ ((J₀+1:ℕ):ℝ)+4 by positivity)
    dsimp [c]
    nlinarith
  have hsmall0 := P.smallRatio_pos.le
  have hlog0 : 0 ≤ Real.log ((2:ℝ)^P.exponent) :=
    Real.log_nonneg (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hsum : (P.sources y).sumBound ≤ c*Real.pi*L^(p+1) := by
    rw [P.sources_log_budget]
    calc
      _ ≤ (L^p*(c*L))*Real.pi := by gcongr
      _ = _ := by rw [Real.rpow_add hL0,Real.rpow_one]; ring
  have hpow : L^(p+2) ≤ L^(p+3) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  constructor
  · apply hs.trans
    calc
      _ ≤ L*L^p := mul_le_mul_of_nonneg_right hpi (Real.rpow_nonneg hL0.le _)
      _ = L^(p+1) := by rw [Real.rpow_add hL0,Real.rpow_one]; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  · apply hsum.trans
    calc
      _ ≤ L*L^(p+1) := mul_le_mul_of_nonneg_right hcpi (Real.rpow_nonneg hL0.le _)
      _ = L^((p+1)+1) := by
        conv_rhs => rw [Real.rpow_add hL0,Real.rpow_one]
        ring
      _ = L^(p+2) := by congr 1; ring
      _ ≤ _ := hpow

end LabeledAngularErrorFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledRawEnvelope
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Carrier-free raw bounds for the original labeled lattices, before
any bound on the total number of labels is imposed. -/

noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem raw_eq_physical_slice (i : Fin 3) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (y t : ℝ) :
    P.raw i j l u k y = planarSchwartzSlice
      (planarCovariantJet (P.physicalPacket t j l u k) (P.frequency k) P.scale i) y t := by
  have h := physicalPlanarPacket_jet_slice (P.profile j l u k) (P.actualX j l u)
    (P.actualZ j l u+t*P.actualX j l u) (P.length j) P.width
    (t+P.rowSlope j l) (P.frequency k) P.scale y t (P.length_pos j).ne' P.width_pos.ne' i
  have hc : P.actualZ j l u+t*P.actualX j l u-t*P.actualX j l u = P.actualZ j l u := by ring
  have hd : t-(t+P.rowSlope j l) = -P.rowSlope j l := by ring
  simpa only [hc,hd,raw,physicalPacket] using h.symm

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceLabeledAngularErrorData
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The labeled dyadic error family formed from the original physical
packets and selectors, with an exact measure-preserving coefficient identity. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item) (horder : 6 ≤ P.order)
  (t a c Cwide M Lip radius : ℝ) (E J K H : ℕ)
  (ha : 0 < a) (hc : 0 < c) (hc1 : c ≤ 1)
  (hC : Cwide ≤ c*(2:ℝ)^J) (hwide : 1 ≤ Cwide*((2:ℝ)^E)^4)
  (hM : 0 ≤ M) (hLip : 0 ≤ Lip) (hradius : radius ≤ K)
  (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
    (fun l => t+P.rowSlope j l) (a*(2:ℝ)^j.val) H)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (hb : ∀ j l k, Measurable (b j l k))
  (hbM : ∀ j l k s, ‖b j l k s‖ ≤ M)
  (hsupport : ∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius*(a*(2:ℝ)^j.val))
  (hnear : ∀ j l k s, |s-t| ≤ c*(a*(2:ℝ)^j.val) →
    ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(a*(2:ℝ)^j.val)))
  (hfar : ∀ j l k s, (Cwide*((2:ℝ)^E)^4)*(a*(2:ℝ)^j.val) < |s-t| → b j l k s = 0)
  (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

theorem angularErrorFamily_coefficient (j : Fin N) (l : P.labels j) (u : Item j l) :
    (P.angularErrorFamily horder t a c Cwide M Lip radius E J K H ha hc hc1 hC hwide
      hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1).coefficient j l u =
      P.physicalAngularErrorCoefficient t a b v g j l u := by
  ext k
  simp only [LabeledAngularErrorFamily.coefficient,physicalAngularErrorCoefficient,analyzingCoefficient,
    WithLp.ofLp_toLp]
  change ((↑(P.length j*P.width):ℂ)⁻¹)*
    (∫ z, g (slopeShear t z) k * conj
      (multiplierError (b j l k) t (a*(2:ℝ)^j.val) (v (slopeShear t z))*P.raw 0 j l u k z.2 z.1)
        ∂volume.prod volume) = _
  have hw (z : ℝ×ℝ) : P.raw 0 j l u k z.2 z.1 = P.physicalPacket t j l u k (slopeShear t z) := by
    have h := congrArg (fun f : SchwartzMap ℝ ℂ => f z.1)
      (P.raw_eq_physical_slice 0 j l u k z.2 t)
    exact h
  simp_rw [hw]
  congr 1
  exact (slopeShear_measurePreserving t).integral_comp (slopeShear t).measurableEmbedding
    (fun z => g z k * conj
      (multiplierError (b j l k) t (a*(2:ℝ)^j.val) (v z)*P.physicalPacket t j l u k z))

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlottedCoefficient
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of selected analyzing integrals and cross-profile
packet sums through the finite slope-label splitting. These are algebraic
identities and require no concentration or integrability assumptions. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LipschitzHilbert.SourceLabeledLattice

attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (P : SourceLabeledLattice N κ Label Item)

variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
  (hAlt : ∀ j l u k,
    planarProfileConstant (alt j l u k) (2 * P.order) ≤ P.profileBound)

omit alt hAlt hcard in
theorem rawInterval_scaled_covariant
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (lower upper : ℕ) (x y : ℝ) :
    P.scale • covariantSignal P.frequency
      (fun k t => P.rawInterval coeff 0 lower upper x t k) y =
        P.rawInterval coeff 1 lower upper x y := by
  unfold rawInterval
  apply planarPacketInterval_scaled_covariant_eq
  · intro j p k t
    exact modulatedPlanarJet_differentiable (P.profile j p.1 p.2 k) (P.actualX j p.1 p.2)
      (P.actualZ j p.1 p.2) (P.length j) P.width (-P.rowSlope j p.1) (P.frequency k)
      P.scale t (P.length_pos j).ne' 0 x
  · intro j p k
    exact modulatedPlanarJet_covariant_zero (P.profile j p.1 p.2 k) (P.actualX j p.1 p.2)
      (P.actualZ j p.1 p.2) (P.length j) P.width (-P.rowSlope j p.1) (P.frequency k)
      P.scale y (P.length_pos j).ne' x

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledGoodQuantities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint measurability of the actual reference quantities is needed
before weighted bad-path sets are integrated over the physical plane. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem lineEnvelope_continuous (a l : ℝ) (n : ℕ) : Continuous (lineEnvelope a l n) := by
  apply Continuous.inv₀
  · fun_prop
  · intro x
    positivity

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSelectorConcentrationErrorMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Natural moments of the actual labeled positive error on arbitrary
binary intervals. The constant depends on the source size and logarithmic
source sum, never on the number of available slope labels. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

theorem selectorErrorMomentBase_pos {B : ℝ} (hB : 0 ≤ B) :
    0 < selectorErrorMomentBase B := by
  have : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  unfold selectorErrorMomentBase
  positivity

namespace LabeledAngularErrorFamily
variable {N : ℕ} {Λ : Fin N → Type} {κ : Type} {ι : ∀ j, Λ j → Type}
  [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]

theorem error_joint_continuous (P : LabeledAngularErrorFamily N Λ κ ι) :
    Continuous (fun z : ℝ×ℝ => P.error z.1 z.2) := by
  apply continuous_finsetSum
  intro j _
  apply continuous_finsetSum
  intro b _
  apply continuous_finsetSum
  intro i _
  apply Continuous.mul continuous_const
  exact ((lineEnvelope_continuous _ _ _).comp continuous_snd).mul
    ((lineEnvelope_continuous _ _ _).comp continuous_fst)

/-- Every source family has the same polynomial moment bound on every
binary interval longer than its retained scales. -/
theorem error_moment_uniform (P : LabeledAngularErrorFamily N Λ κ ι)
    (B : ℝ) (_hB : 0 ≤ B)
    (hs : ∀ y, (P.sources y).sourceBound ≤ B)
    (ht : ∀ y, (P.sources y).sumBound ≤ B)
    (grid : FiniteLineGrid) (hg : grid.branching = 2)
    (hshort : ∀ j b (_u : ι j b), P.length j ≤ grid.width)
    (y : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (∫⁻ x, (ENNReal.ofReal (P.error y x))^n ∂grid.lineMeasure) ≤
      (ENNReal.ofReal (selectorErrorMomentBase B*(n:ℝ)))^n*grid.lineMeasure univ := by
  let Q := (P.sources y).restrictLength grid.width
  have hbase : Q.momentBase grid ≤ selectorErrorMomentBase B := by
    have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
    have hQs : Q.sourceBound ≤ B := hs y
    have hQt : Q.sumBound ≤ B := ht y
    unfold LineErrorSources.momentBase LineErrorSources.meanConstant
      LineErrorSources.oscillationConstant selectorErrorMomentBase
    rw [hg]
    norm_num only [Nat.cast_ofNat]
    gcongr
  have hm := Q.majorant_moment_natural grid (by omega)
    ((P.sources y).restrictLength_source_zero grid.width) n hn
  have hdom : (∫⁻ x, (ENNReal.ofReal (P.error y x))^n ∂grid.lineMeasure) ≤
      (∫⁻ x, (ENNReal.ofReal (Q.majorant x))^n ∂grid.lineMeasure) :=
    lintegral_mono fun x => pow_le_pow_left' (ENNReal.ofReal_le_ofReal
      (P.error_le_restricted_majorant grid.width hshort y x)) n
  apply hdom.trans (hm.trans _)
  rw [ENNReal.ofReal_pow (mul_nonneg (Q.momentBase_pos grid).le (Nat.cast_nonneg n))]
  exact mul_le_mul' (pow_le_pow_left' (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hbase (Nat.cast_nonneg n))) n) le_rfl

end LabeledAngularErrorFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSelectorConcentrationErrorBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted error moment constant costs only a fixed polynomial.
All thresholds are chosen before the packet family and geometric scales. -/

noncomputable section
namespace LipschitzHilbert

theorem selectorErrorMomentBase_affine (B : ℝ) :
    selectorErrorMomentBase B = selectorErrorMomentBase 0+
      (selectorErrorMomentBase 1-selectorErrorMomentBase 0)*B := by
  unfold selectorErrorMomentBase
  ring

theorem selectorErrorMomentBase_slope_nonneg :
    0 ≤ selectorErrorMomentBase 1-selectorErrorMomentBase 0 := by
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  have heq : selectorErrorMomentBase 1-selectorErrorMomentBase 0 =
      16*((4*(2*(1024*Real.pi^2)+240*Real.pi))/Real.log (3/2)+1024*Real.pi^2) := by
    unfold selectorErrorMomentBase
    ring
  rw [heq]
  positivity

theorem selectorErrorMomentBase_le_power {B L p : ℝ} (hL : 1 ≤ L)
    (hp : 0 ≤ p) (hB : B ≤ L^p) :
    selectorErrorMomentBase B ≤ selectorErrorMomentBase 1*L^p := by
  have hLp : 1 ≤ L^p := Real.one_le_rpow hL hp
  rw [selectorErrorMomentBase_affine B]
  have h0 := selectorErrorMomentBase_pos (B := 0) (by norm_num)
  have hs := selectorErrorMomentBase_slope_nonneg
  calc
    _ ≤ selectorErrorMomentBase 0*L^p+
        (selectorErrorMomentBase 1-selectorErrorMomentBase 0)*L^p :=
      add_le_add (by nlinarith) (mul_le_mul_of_nonneg_left hB hs)
    _ = _ := by ring

theorem exists_selector_error_top_threshold (J a p : ℝ) (D : ℕ)
    (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ C B : ℝ,
      0 ≤ C → 0 ≤ B → C ≤ L^p → B ≤ L^(p+4) →
      256^(8*D+1)*(16*topPairConstant C (8*D+1)*selectorErrorMomentBase B)*
        (topExceptionMoment (topAreaPrefactor (L^a)) J L:ℝ)*5^(8*D) ≤ L^(2*p+6) := by
  let m : ℝ := (J+Real.log (topAreaPrefactor 1)+2*a)/Real.log 4+2
  let A : ℝ := 256^(8*D+1)*(16*topPairConstant 1 (8*D+1)*selectorErrorMomentBase 1)*m*5^(8*D)
  have hm : 0 < m := by
    have hlog := Real.log_nonneg topAreaPrefactor_one_le
    have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    dsimp [m]
    positivity
  have hA : 0 < A := by
    have ht := topPairConstant_pos 1 (8*D+1) (by norm_num)
    have he := selectorErrorMomentBase_pos (B := 1) (by norm_num)
    dsimp [A]
    positivity
  refine ⟨max 1 A,le_max_left _ _,?_⟩
  intro L hLL C B _hC hB0 hCb hB
  have hL : 1 ≤ L := (le_max_left _ _).trans hLL
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hAL : A ≤ L := (le_max_right _ _).trans hLL
  have htop : topPairConstant C (8*D+1) = topPairConstant 1 (8*D+1)*C := by
    unfold topPairConstant
    ring
  have he := selectorErrorMomentBase_le_power hL (by linarith : 0 ≤ p+4) hB
  have hn := topExceptionMoment_power_le J a L hJ ha hL
  change (topExceptionMoment (topAreaPrefactor (L^a)) J L:ℝ) ≤ m*L at hn
  have htpos := topPairConstant_pos 1 (8*D+1) (by norm_num)
  have hepos := selectorErrorMomentBase_pos (B := 1) (by norm_num)
  have hCmul : 16*(topPairConstant 1 (8*D+1)*C) ≤
      16*topPairConstant 1 (8*D+1)*L^p := by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hCb (show 0 ≤ 16*topPairConstant 1 (8*D+1) by positivity)
  have hcoeff : 256^(8*D+1)*(16*topPairConstant C (8*D+1)*selectorErrorMomentBase B) ≤
      256^(8*D+1)*(16*topPairConstant 1 (8*D+1)*L^p*
        (selectorErrorMomentBase 1*L^(p+4))) := by
    rw [htop]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul hCmul he
      (selectorErrorMomentBase_pos hB0).le
      (by positivity)
  calc
    _ ≤ (256^(8*D+1)*(16*topPairConstant 1 (8*D+1)*L^p*
        (selectorErrorMomentBase 1*L^(p+4))))*(m*L)*5^(8*D) := by
      have hleft := mul_le_mul hcoeff hn (Nat.cast_nonneg _)
        (by positivity : 0 ≤ 256^(8*D+1)*(16*topPairConstant 1 (8*D+1)*L^p*
          (selectorErrorMomentBase 1*L^(p+4))))
      exact mul_le_mul_of_nonneg_right hleft (by positivity)
    _ = A*L^(2*p+5) := by
      have hpowers : L^p*L^(p+4)*L = L^(2*p+5) := by
        calc
          _ = L^(p+(p+4))*L^1 := by rw [Real.rpow_add hL0 p (p+4),Real.rpow_one]
          _ = L^((p+(p+4))+1) := (Real.rpow_add hL0 _ _).symm
          _ = _ := by congr 1; ring
      calc
        _ = A*(L^p*L^(p+4)*L) := by dsimp [A]; ring
        _ = _ := by rw [hpowers]
    _ ≤ L*L^(2*p+5) := mul_le_mul_of_nonneg_right hAL (Real.rpow_nonneg hL0.le _)
    _ = L^(2*p+6) := by
      calc
        _ = L^1*L^(2*p+5) := by rw [Real.rpow_one]
        _ = L^(1+(2*p+5)) := (Real.rpow_add hL0 _ _).symm
        _ = _ := by congr 1; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSelectorConcentrationErrorNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive angular-error moments control covariant vertical
neighborhoods of polynomially weighted packet sums. There is no Fourier
or martingale hypothesis in this step. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.LabeledAngularErrorFamily
variable {N : ℕ} {Λ : Fin N → Type} {κ : Type} {ι : ∀ j, Λ j → Type}
  [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]

theorem error_global_neighborhood {α : Type*}
    (P : LabeledAngularErrorFamily N Λ κ ι)
    (B C a b r R : ℝ) (hB : 0 ≤ B) (hC : 0 < C) (hr : 0 < r) (hR : 0 < R)
    (hs : ∀ y, (P.sources y).sourceBound ≤ B)
    (ht : ∀ y, (P.sources y).sumBound ≤ B)
    (hshort : ∀ j l (_u : ι j l), P.length j ≤ r)
    (frequency : κ → ℝ) (f : α → κ → ℝ → ℝ → ℂ)
    (F : α → ℝ → ℝ → EuclideanSpace ℂ κ)
    (q n : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n)
    (hdiff : ∀ i k x y, DifferentiableAt ℝ (f i k x) y)
    (hmem : ∀ (p : ℤ×ℤ) i x, MemLp (covariantSignal frequency (fun k => f i k x)) 2
      (volume.restrict (Icc (b+R*p.2-2*R) (b+R*p.2+2*R))))
    (hbV : ∀ i x y, ‖(WithLp.toLp 2 (fun k => f i k x y) : EuclideanSpace ℂ κ)‖ ≤
      C*P.error y x)
    (hbD : ∀ i x y, 4*R*‖covariantSignal frequency (fun k => f i k x) y‖ ≤
      C*P.error y x)
    (hweighted : ∀ i x y,
      ‖(WithLp.toLp 2 (fun k => f i k x y) : EuclideanSpace ℂ κ)‖ =
        (polynomialWeight a r q x*polynomialWeight b R q y)*‖F i x y‖) :
    ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ (1/4:ℝ≥0∞)^n*
        (2*ENNReal.ofReal r*ENNReal.ofReal (2*R))*ENNReal.ofReal ((4*Real.pi)^2) ∧
      ∀ i x z v, |v| ≤ R → (x,z) ∉ bad →
        ‖F i x (z+v)‖ ≤
          256^q*(8*C*selectorErrorMomentBase B*(n:ℝ))*
            boxVariationWeight (packetBoxIndex a b r R x z)^(q-1) := by
  let V : ℝ×ℝ → ℝ := fun z => C*P.error z.1 z.2
  let D : ℝ×ℝ → ℝ := fun z => V z/(4*R)
  let A := C*selectorErrorMomentBase B*(2*n:ℕ)
  have hV : Continuous V := continuous_const.mul P.error_joint_continuous
  have hD : Continuous D := hV.div_const _
  have hn0 : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hA : 0 < A := by
    have := selectorErrorMomentBase_pos hB
    dsimp [A]
    positivity
  have hscale (y x : ℝ) : 4*R*D (y,x) = V (y,x) := by
    dsimp [D]
    field_simp
  have hVnonneg (z : ℝ×ℝ) : 0 ≤ V z := mul_nonneg hC.le (P.error_nonneg z.1 z.2)
  have hline (p : ℤ×ℤ) (y : ℝ) :
      (∫⁻ x in Ico (a+r*p.1) (a+r*((p.1:ℝ)+1)),
        ENNReal.ofReal (V (y,x)^(2*n)+(4*R*D (y,x))^(2*n))) ≤
          2*(ENNReal.ofReal A)^(2*n)*ENNReal.ofReal r := by
    let grid : FiniteLineGrid := {
      branching := 2, branching_pos := by decide, origin := a+r*p.1,
      width := r, width_pos := hr, depth := 0 }
    have hroot : grid.root = Ico (a+r*p.1) (a+r*((p.1:ℝ)+1)) := by
      unfold FiniteLineGrid.root
      dsimp [grid]
      congr 1
      ring
    have hmass : grid.lineMeasure univ = ENNReal.ofReal r := by
      rw [FiniteLineGrid.lineMeasure,Measure.restrict_apply_univ,hroot,Real.volume_Ico]
      congr 1
      ring
    have hm := P.error_moment_uniform B hB hs ht grid rfl hshort y (2*n) (by omega)
    have hpow (x : ℝ) : ENNReal.ofReal (V (y,x)^(2*n)) =
        (ENNReal.ofReal C)^(2*n)*(ENNReal.ofReal (P.error y x))^(2*n) := by
      rw [ENNReal.ofReal_pow (hVnonneg (y,x))]
      change (ENNReal.ofReal (C*P.error y x))^(2*n) = _
      rw [ENNReal.ofReal_mul hC.le,mul_pow]
    have hsum (x : ℝ) : ENNReal.ofReal (V (y,x)^(2*n)+V (y,x)^(2*n)) =
        ENNReal.ofReal (V (y,x)^(2*n))+ENNReal.ofReal (V (y,x)^(2*n)) :=
      ENNReal.ofReal_add (pow_nonneg (hVnonneg (y,x)) _) (pow_nonneg (hVnonneg (y,x)) _)
    simp_rw [hscale,hsum,hpow]
    have he : Measurable (fun x : ℝ => P.error y x) :=
      (P.error_joint_continuous.comp
        ((continuous_const : Continuous (fun _ : ℝ => y)).prodMk continuous_id)).measurable
    rw [lintegral_add_left ((he.ennreal_ofReal.pow_const (2*n)).const_mul
      ((ENNReal.ofReal C)^(2*n)))]
    have hsingle : (∫⁻ x in Ico (a+r*p.1) (a+r*((p.1:ℝ)+1)),
        (ENNReal.ofReal C)^(2*n)*(ENNReal.ofReal (P.error y x))^(2*n)) ≤
          (ENNReal.ofReal A)^(2*n)*ENNReal.ofReal r := by
      rw [lintegral_const_mul' _ _ (by finiteness)]
      have h := mul_le_mul_right hm ((ENNReal.ofReal C)^(2*n))
      rw [hmass] at h
      rw [FiniteLineGrid.lineMeasure,hroot] at h
      apply h.trans_eq
      have hfactor : ENNReal.ofReal A = ENNReal.ofReal C*
          ENNReal.ofReal (selectorErrorMomentBase B*(2*n:ℕ)) := by
        dsimp [A]
        rw [show C*selectorErrorMomentBase B*(2*n:ℕ) =
          C*(selectorErrorMomentBase B*(2*n:ℕ)) by ring,ENNReal.ofReal_mul hC.le]
      rw [hfactor,mul_pow]
      ring
    calc
      _ ≤ ((ENNReal.ofReal A)^(2*n)*ENNReal.ofReal r)+
          ((ENNReal.ofReal A)^(2*n)*ENNReal.ofReal r) := add_le_add hsingle hsingle
      _ = _ := by ring
  obtain ⟨bad,hbad,harea,hpoint⟩ := global_top_neighborhood frequency f F V D hV hD
    a b r R A hr hR hA n q hn hq hline hdiff hmem hbV (by
      intro i x y
      apply (le_div_iff₀ (show 0 < 4*R by positivity)).mpr
      simpa only [mul_comm] using hbD i x y) hweighted
  refine ⟨bad,hbad,harea,?_⟩
  intro i x z v hv hout
  have h := hpoint i x z v hv hout
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [A]
  push_cast
  ring

end LipschitzHilbert.LabeledAngularErrorFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSelectorConcentrationErrorSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original angular-error coefficients may synthesize a different
profile. Polynomially weighting the two raw covariant jets leaves their
sixth-order positive envelope, so the preceding moment theorem applies. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.LabeledAngularErrorFamily
variable {N : ℕ} {Λ : Fin N → Type} {κ : Type} {ι : ∀ j, Λ j → Type}
  [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]

theorem error_interval_norm_le (P : LabeledAngularErrorFamily N Λ κ ι)
    (wave : ∀ j, (Σ l : Λ j, ι j l) → κ → ℝ → ℝ → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ j l u k y x, ‖wave j ⟨l,u⟩ k y x‖ ≤ C*
      tileEnvelope (P.originX j l+P.length j*(P.site j l u).1)
        (P.originY j l+P.width*(P.site j l u).2) (P.length j) P.width 6 (x,y))
    (lower upper : ℕ) (x y : ℝ) :
    ‖planarPacketInterval (fun j p => P.coefficient j p.1 p.2) wave lower upper x y‖ ≤
      2*C*P.error y x := by
  let band := fun j => diagonalSynthesis
    (fun p k (z : ℝ×ℝ) => wave j p k z.2 z.1)
    (fun p => P.coefficient j p.1 p.2) (x,y)
  have hb j : ‖band j‖ ≤ C*P.scaleError j y x := by
    have h := norm_diagonalSynthesis_le
      (fun p k (z : ℝ×ℝ) => wave j p k z.2 z.1)
      (fun p => P.coefficient j p.1 p.2)
      (fun p => tileEnvelope (P.originX j p.1+P.length j*(P.site j p.1 p.2).1)
        (P.originY j p.1+P.width*(P.site j p.1 p.2).2) (P.length j) P.width 6 (x,y))
      (x,y) hC (fun _ => tileEnvelope_nonneg _ _ _ _ _ _)
      (fun p k => hw j p.1 p.2 k y x)
    simpa only [band,scaleError,Fintype.sum_sigma] using h
  have hp n : (WithLp.toLp 2 (fun k => scalarBandPartial
      (fun j => planarPacketBand (fun j p => P.coefficient j p.1 p.2) wave j k x) n y) :
        EuclideanSpace ℂ κ) = ∑ j, if j.val < n then band j else 0 := by
    ext k
    simp only [WithLp.ofLp_sum,Finset.sum_apply,scalarBandPartial]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp only [band,diagonalSynthesis,planarPacketBand,WithLp.ofLp_toLp,
      PiLp.zero_apply]
  have hpartial n : ‖(WithLp.toLp 2 (fun k => scalarBandPartial
      (fun j => planarPacketBand (fun j p => P.coefficient j p.1 p.2) wave j k x) n y) :
        EuclideanSpace ℂ κ)‖ ≤ C*P.error y x := by
    rw [hp]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j, C*P.scaleError j y x := Finset.sum_le_sum fun j _ => by
        split_ifs
        · exact hb j
        · simpa only [norm_zero] using mul_nonneg hC (P.scaleError_nonneg j y x)
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have heq : planarPacketInterval (fun j p => P.coefficient j p.1 p.2) wave lower upper x y =
      (WithLp.toLp 2 (fun k => scalarBandPartial
        (fun j => planarPacketBand (fun j p => P.coefficient j p.1 p.2) wave j k x) upper y) :
          EuclideanSpace ℂ κ)-
      WithLp.toLp 2 (fun k => scalarBandPartial
        (fun j => planarPacketBand (fun j p => P.coefficient j p.1 p.2) wave j k x) lower y) := by
    ext k
    rfl
  rw [heq]
  exact (norm_sub_le _ _).trans ((add_le_add (hpartial upper) (hpartial lower)).trans_eq (by ring))

end LipschitzHilbert.LabeledAngularErrorFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSelectorConcentrationErrorRaw
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-order carrier-free decay and the actual top geometry survive
snapping the translated labeled lattice. These are the raw hypotheses
used in the weighted angular-error concentration theorem. -/

noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem raw_absolute_snapped_order (i : Fin 3) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (y x : ℝ) :
    ‖P.raw i j l u k y x‖ ≤ P.absoluteConstant*
      (lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) P.order x*
        lineEnvelope (P.width*(P.snappedSite j l u).2) P.width P.order y) := by
  have hs := snappedLatticeSite_envelope (P.originX j l) (P.originZ j l) (P.length j)
    P.width (P.rowSlope j l) x y (P.length_pos j) P.width_pos (P.site j l u) P.order P.order
  have hA : 0 ≤ (2^P.order*P.profileBound)*P.ratioBound^2 := by
    have := P.profileBound_pos
    positivity
  have h := (P.raw_absolute_envelope i j l u k y x).trans
    (mul_le_mul_of_nonneg_left hs hA)
  have hp : (3:ℝ)^P.order*3^P.order = 3^(2*P.order) := by
    rw [← pow_add]
    congr 1
    omega
  simpa only [absoluteConstant,snappedSite,hp,mul_assoc] using h

theorem raw_absolute_snapped_decay (m : ℕ) (hm : m ≤ P.order)
    (i : Fin 3) (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ) (y x : ℝ) :
    ‖P.raw i j l u k y x‖ ≤ P.absoluteConstant*
      (lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) m x*
        lineEnvelope (P.width*(P.snappedSite j l u).2) P.width m y) := by
  apply (P.raw_absolute_snapped_order i j l u k y x).trans
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (lineEnvelope_antitone _ _ _ hm) (lineEnvelope_antitone _ _ _ hm)
      (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)) P.absoluteConstant_pos.le

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledErrorBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed profile order, geometric bounds, and selector multiplicity give
polynomial source constants without a factor counting the available labels. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

namespace LabeledAngularErrorFamily

theorem eventually_sourceAmplitude_le (K H : ℕ) (M D p : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (Λ : Fin N → Type) (κ : Type)
      (ι : ∀ j, Λ j → Type) [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]
      (P : LabeledAngularErrorFamily N Λ κ ι),
      P.radiusBound ≤ K → P.multiplicity ≤ H →
      P.multiplierBound ≤ M → P.multiplierLip ≤ D → P.packetBound ≤ L^p →
      P.sourceAmplitude ≤ L^(p+1) := by
  let C : ℝ := ((64*(4*Real.pi)^2)*(2*((2*K+1)*H):ℕ))*(2*M+D)
  filter_upwards [eventually_ge_atTop (max 1 C)] with L hlarge
  have hL : 0 < L := zero_lt_one.trans_le ((le_max_left _ _).trans hlarge)
  have hC : C ≤ L := (le_max_right _ _).trans hlarge
  intro N Λ κ ι _ _ _ P hK hH hPM hPD hP
  have hn : 2*((2*P.radiusBound+1)*P.multiplicity) ≤ 2*((2*K+1)*H) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hK) 1) hH)
  have hn' : (2*((2*P.radiusBound+1)*P.multiplicity):ℕ) ≤
      (2*((2*K+1)*H):ℕ) := hn
  have hr : ((2*((2*P.radiusBound+1)*P.multiplicity):ℕ):ℝ) ≤
      (2*((2*K+1)*H):ℕ) := by exact_mod_cast hn'
  have hB : 0 ≤ 2*P.multiplierBound+P.multiplierLip := by
    linarith [P.multiplierBound_nonneg,P.multiplierLip_nonneg]
  calc
    P.sourceAmplitude ≤ ((64*(4*Real.pi)^2)*(2*((2*K+1)*H):ℕ))*(L^p*(2*M+D)) := by
      unfold sourceAmplitude
      exact mul_le_mul (mul_le_mul_of_nonneg_left hr (by positivity))
        (mul_le_mul hP (by linarith) hB (Real.rpow_nonneg hL.le _))
        (mul_nonneg P.packetBound_nonneg hB) (by positivity)
    _ = C*L^p := by dsimp [C]; ring
    _ ≤ L*L^p := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hL.le _)
    _ = L^(p+1) := by rw [Real.rpow_add hL,Real.rpow_one]; ring

end LabeledAngularErrorFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedErrorSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.LabeledAngularErrorFamily
variable {N : ℕ} {Λ : Fin N → Type} {κ : Type} {ι : ∀ j, Λ j → Type}
  [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]

theorem error_synthesis_global_neighborhood_of_supported
    (P : LabeledAngularErrorFamily N Λ κ ι)
    (B C a b r R : ℝ) (hB : 0 ≤ B) (hC : 0 < C) (hr : 0 < r) (hR : 0 < R)
    (hs : ∀ y, (P.sources y).sourceBound ≤ B)
    (ht : ∀ y, (P.sources y).sumBound ≤ B)
    (hshort : ∀ j l (_u : ι j l), P.length j ≤ r) (hwidth : P.width ≤ R)
    (hx : ∀ j l u, |P.originX j l+P.length j*(P.site j l u).1-a| ≤ r)
    (hy : ∀ j l u, |P.originY j l+P.width*(P.site j l u).2-b| ≤ R)
    (raw : Fin 2 → ∀ j, (Σ l : Λ j, ι j l) → κ → ℝ → SchwartzMap ℝ ℂ)
    (frequency : κ → ℝ) (q n : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n)
    (hraw : ∀ i j l u k y x, ‖raw i j ⟨l,u⟩ k y x‖ ≤ C*
      (lineEnvelope (P.originX j l+P.length j*(P.site j l u).1) (P.length j) (6+2*q) x*
        lineEnvelope (P.originY j l+P.width*(P.site j l u).2) P.width (6+2*q) y))
    (hcov : ∀ j p k x y, (4*R:ℂ)*(deriv (fun yy => raw 0 j p k yy x) y-
      (frequency k:ℂ)*Complex.I*raw 0 j p k y x) = raw 1 j p k y x)
    (hcont : ∀ i j p k, Continuous (fun z : ℝ×ℝ => raw i j p k z.1 z.2))
    (hdiff : ∀ j p k x y, DifferentiableAt ℝ (fun yy => raw 0 j p k yy x) y) :
    ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ (1/4:ℝ≥0∞)^n*
        (2*ENNReal.ofReal r*ENNReal.ofReal (2*R))*ENNReal.ofReal ((4*Real.pi)^2) ∧
      ∀ lower upper x z v, |v| ≤ R → (x,z) ∉ bad →
        ‖planarPacketInterval (fun j p => P.coefficient j p.1 p.2)
          (fun j p k y x => raw 0 j p k y x) lower upper x (z+v)‖ ≤
          256^q*(16*topPairConstant C q*selectorErrorMomentBase B*(n:ℝ))*
            boxVariationWeight (packetBoxIndex a b r R x z)^(q-1) := by
  let coeff := fun j (p : Σ l : Λ j, ι j l) => P.coefficient j p.1 p.2
  let synth := fun i j p k y => topWeightedPair (fun e => raw e j p k y) a r b R y q i
  let wave := fun j p k y x => synth 0 j p k y x
  let A := ℕ×ℕ
  let f : A → κ → ℝ → ℝ → ℂ := fun ab k x y =>
    planarPacketInterval coeff wave ab.1 ab.2 x y k
  let F : A → ℝ → ℝ → EuclideanSpace ℂ κ := fun ab x y =>
    planarPacketInterval coeff (fun j p k y x => raw 0 j p k y x) ab.1 ab.2 x y
  have hCpair := topPairConstant_pos C q hC
  have hbound i j l u k y x : ‖synth i j ⟨l,u⟩ k y x‖ ≤ topPairConstant C q*
      tileEnvelope (P.originX j l+P.length j*(P.site j l u).1)
        (P.originY j l+P.width*(P.site j l u).2) (P.length j) P.width 6 (x,y) := by
    exact topWeightedPair_bound (fun e => raw e j ⟨l,u⟩ k y) a r b R y _ _ _ _ C q 6 6
      (div_pos P.topLength_pos (pow_pos (by norm_num) _)) hr P.width_pos hR
      (hshort j l u)
      hwidth (hx j l u) (hy j l u) hC.le (fun e => hraw e j l u k y) i x
  have hc j p k x y : (4*R:ℂ)*(deriv (fun yy => wave j p k yy x) y-
      (frequency k:ℂ)*Complex.I*wave j p k y x) = synth 1 j p k y x := by
    simpa [wave,synth,topWeightedPair] using topWeightedWave_covariant
      (raw 0 j p k) (raw 1 j p k) a r b R y (frequency k) x q
      (hdiff j p k x y) (hcov j p k x y)
  have hdiffw j p k x y : DifferentiableAt ℝ (fun yy => wave j p k yy x) y := by
    simpa only [wave,synth,topWeightedPair,ite_eq_left rfl] using
      topWeightedWave_vertical_differentiable (raw 0 j p k) a r b R x y q (hdiff j p k x y)
  have hDw j p k : Continuous (fun z : ℝ×ℝ =>
      deriv (fun yy => wave j p k yy z.2) z.1-
        (frequency k:ℂ)*Complex.I*wave j p k z.1 z.2) := by
    simpa only [wave,synth,topWeightedPair,ite_eq_left rfl] using
      topWeightedWave_covariant_continuous (raw 0 j p k) (raw 1 j p k)
        a r b R (frequency k) q hR (hcont 0 j p k) (hcont 1 j p k)
        (hdiff j p k) (hcov j p k)
  have hnorm ab x y : ‖(WithLp.toLp 2 (fun k => f ab k x y) : EuclideanSpace ℂ κ)‖ ≤
      (2*topPairConstant C q)*P.error y x := by
    change ‖planarPacketInterval coeff wave ab.1 ab.2 x y‖ ≤ _
    exact P.error_interval_norm_le wave _ hCpair.le (hbound 0) _ _ x y
  have hDnorm ab x y : 4*R*‖covariantSignal frequency (fun k => f ab k x) y‖ ≤
      (2*topPairConstant C q)*P.error y x := by
    have heq : (4*R) • covariantSignal frequency (fun k => f ab k x) y =
        planarPacketInterval coeff (fun j p k y x => synth 1 j p k y x) ab.1 ab.2 x y := by
      rw [show covariantSignal frequency (fun k => f ab k x) y =
        planarPacketInterval coeff (fun j p k y x => deriv (fun yy => wave j p k yy x) y-
          (frequency k:ℂ)*Complex.I*wave j p k y x) ab.1 ab.2 x y from
            planarPacketInterval_covariant coeff wave frequency _ _ _ _ (fun j p k => hdiffw j p k x)]
      rw [← planarPacketInterval_smul]
      congr 1
      funext j p k y x
      simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using hc j p k x y
    have hn := congrArg norm heq
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 4*R)] at hn
    rw [hn]
    exact P.error_interval_norm_le _ _ hCpair.le (hbound 1) _ _ x y
  obtain ⟨bad,hbad,harea,hpoint⟩ := P.error_global_neighborhood B (2*topPairConstant C q)
    a b r R hB (by positivity) hr hR hs ht
    hshort
    frequency f F q n hq hn
    (fun ab k x y => planarPacketInterval_component_differentiable coeff wave _ _ x y k
      (fun j p => hdiffw j p k x y))
    (fun p ab x => planarPacketInterval_covariant_memLp coeff wave frequency hdiffw hDw
      _ _ x _ _) hnorm hDnorm (by
        intro ab x y
        change ‖planarPacketInterval coeff wave ab.1 ab.2 x y‖ = _
        simpa only [wave,synth,topWeightedPair,ite_eq_left rfl] using
          planarPacketInterval_topWeighted_norm coeff (fun j p k y => raw 0 j p k y)
            a r b R q ab.1 ab.2 x y)
  refine ⟨bad,hbad,harea,?_⟩
  intro lower upper x z v hv hout
  have h := hpoint (lower,upper) x z v hv hout
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end LipschitzHilbert.LabeledAngularErrorFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedErrorRaw
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem snapped_supported_top_horizontal {T : SlopeBox} {K : ℝ} {D : ℕ}
    (G : SourceSupportedLabeledTopGeometry P T K D) (j : Fin N) (l : P.labels j) (u : Item j l) :
    |P.length j*(P.snappedSite j l u).1-T.x| ≤ K*T.length := by
  have hs := snappedLatticeSite_horizontal (P.originX j l) (P.originZ j l)
    (P.length j) P.width (P.rowSlope j l) (P.length_pos j) (P.site j l u)
  change |P.actualX j l u-P.length j*(P.snappedSite j l u).1| ≤ P.length j at hs
  have ht := abs_sub_le (P.length j*(P.snappedSite j l u).1) (P.actualX j l u) T.x
  rw [abs_sub_comm (P.actualX j l u)] at hs
  have hg := G.centerX_le j l u
  linarith

theorem snapped_supported_top_vertical {T : SlopeBox} {K : ℝ} {D : ℕ}
    (G : SourceSupportedLabeledTopGeometry P T K D) (j : Fin N) (l : P.labels j) (u : Item j l) :
    |P.width*(P.snappedSite j l u).2-(T.y-T.slope*T.x)| ≤ K*T.width := by
  have hs := snappedLatticeSite_vertical (P.originX j l) (P.originZ j l)
    (P.length j) P.width (P.rowSlope j l) P.width_pos (P.site j l u)
  change |P.actualZ j l u-P.width*(P.snappedSite j l u).2| ≤ P.width at hs
  have ht := abs_sub_le (P.width*(P.snappedSite j l u).2) (P.actualZ j l u) (T.y-T.slope*T.x)
  rw [abs_sub_comm (P.actualZ j l u)] at hs
  have hg := G.centerZ_le j l u
  linarith

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedErrorPhysical
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item) (horder : 6 ≤ P.order)
  (t a c Cwide M Lip radius : ℝ) (E J K H : ℕ)
  (ha : 0 < a) (hc : 0 < c) (hc1 : c ≤ 1)
  (hC : Cwide ≤ c*(2:ℝ)^J) (hwide : 1 ≤ Cwide*((2:ℝ)^E)^4)
  (hM : 0 ≤ M) (hLip : 0 ≤ Lip) (hradius : radius ≤ K)
  (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
    (fun l => t+P.rowSlope j l) (a*(2:ℝ)^j.val) H)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (hb : ∀ j l k, Measurable (b j l k))
  (hbM : ∀ j l k s, ‖b j l k s‖ ≤ M)
  (hsupport : ∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius*(a*(2:ℝ)^j.val))
  (hnear : ∀ j l k s, |s-t| ≤ c*(a*(2:ℝ)^j.val) →
    ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(a*(2:ℝ)^j.val)))
  (hfar : ∀ j l k s, (Cwide*((2:ℝ)^E)^4)*(a*(2:ℝ)^j.val) < |s-t| → b j l k s = 0)
  (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

theorem selector_error_top_neighborhood_of_supported
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (T : SlopeBox) (Kw : ℝ) (D : ℕ) (hKw : 0 < Kw)
    (G : SourceSupportedLabeledTopGeometry P T Kw D) (ht : T.slope = t)
    (hdecay : 6+2*(8*D+1) ≤ P.order) (B : ℝ) (hB : 0 ≤ B)
    (i : Fin 2) (rate L : ℝ) :
    let Err := P.angularErrorFamily horder t a c Cwide M Lip radius E J K H
      ha hc hc1 hC hwide hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1
    (∀ y, (Err.sources y).sourceBound ≤ B) →
    (∀ y, (Err.sources y).sumBound ≤ B) →
    ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-rate*L)*T.area) ∧
      ∀ lower upper z shift, |shift| ≤ Kw*T.width → z ∉ bad →
        ‖(P.withProfile alt hAlt).rawInterval (P.physicalAngularErrorCoefficient t a b v g)
          (i.castLE (by decide)) lower upper z.1 (z.2-t*z.1+shift)‖ ≤
          (256^(8*D+1)*(16*topPairConstant P.absoluteConstant (8*D+1)*
            selectorErrorMomentBase B)*(topExceptionMoment (topAreaPrefactor Kw) rate L:ℝ)*
              5^(8*D))*(T.weight Kw (D:ℝ) z)^8 := by
  dsimp only
  intro hsource hsum
  let Err := P.angularErrorFamily horder t a c Cwide M Lip radius E J K H
    ha hc hc1 hC hwide hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1
  let Q := P.withProfile alt hAlt
  let raw := fun (e : Fin 2) j (p : Σ l : P.labels j, Item j l) k y =>
    Q.raw (⟨i.val+e.val,by omega⟩ : Fin 3) j p.1 p.2 k y
  let F := fun ab : ℕ×ℕ => fun x y => Q.rawInterval
    (P.physicalAngularErrorCoefficient t a b v g) (i.castLE (by decide)) ab.1 ab.2 x y
  have hcoeff (j : Fin N) (p : Σ l : P.labels j, Item j l) :
      Err.coefficient j p.1 p.2 = P.physicalAngularErrorCoefficient t a b v g j p.1 p.2 :=
    P.angularErrorFamily_coefficient horder t a c Cwide M Lip radius E J K H
      ha hc hc1 hC hwide hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1 _ _ _
  have hraw0 j p k y x : raw 0 j p k y x = Q.raw (i.castLE (by decide)) j p.1 p.2 k y x := by
    congr 2
  obtain ⟨bad,hbad,harea,hpoint⟩ := slope_top_neighborhood T Kw
    (256^(8*D+1)*(16*topPairConstant P.absoluteConstant (8*D+1)*selectorErrorMomentBase B))
    rate L D hKw (by
      have := topPairConstant_pos P.absoluteConstant (8*D+1) P.absoluteConstant_pos
      have := selectorErrorMomentBase_pos hB
      positivity) F (by
        intro n hn
        obtain ⟨bad,hbad,harea,hpoint⟩ := Err.error_synthesis_global_neighborhood_of_supported B
          P.absoluteConstant T.x (T.y-T.slope*T.x) (Kw*T.length) (Kw*T.width)
          hB P.absoluteConstant_pos (mul_pos hKw T.length_pos) (mul_pos hKw T.width_pos)
          hsource hsum G.length_le G.width_le
          (by
            intro j l u
            simp only [Err,angularErrorFamily,zero_add]
            change |P.length j*(P.snappedSite j l u).1-T.x| ≤ Kw*T.length
            exact P.snapped_supported_top_horizontal G j l u)
          (by
            intro j l u
            simp only [Err,angularErrorFamily,zero_add]
            exact P.snapped_supported_top_vertical G j l u)
          raw P.frequency (8*D+1) n (by omega) hn
          (by
            intro e j l u k y x
            simp only [Err,angularErrorFamily,zero_add]
            change ‖Q.raw ⟨i.val+e.val,by omega⟩ j l u k y x‖ ≤ Q.absoluteConstant*
              (lineEnvelope (Q.length j*(Q.snappedSite j l u).1) (Q.length j)
                (6+2*(8*D+1)) x *
               lineEnvelope (Q.width*(Q.snappedSite j l u).2) Q.width (6+2*(8*D+1)) y)
            exact Q.raw_absolute_snapped_decay (6+2*(8*D+1)) hdecay
              ⟨i.val+e.val,by omega⟩ j l u k y x)
          (by
            intro j p k x y
            have hs : (4:ℂ)*(↑(Kw*T.width):ℂ) = (P.scale:ℂ) := by
              rw [G.scale_eq]
              push_cast
              ring
            rw [hs]
            fin_cases i
            · exact modulatedPlanarJet_covariant_zero (alt j p.1 p.2 k)
                (P.actualX j p.1 p.2) (P.actualZ j p.1 p.2) (P.length j) P.width
                (-P.rowSlope j p.1) (P.frequency k) P.scale y (P.length_pos j).ne' x
            · exact modulatedPlanarJet_covariant_one (alt j p.1 p.2 k)
                (P.actualX j p.1 p.2) (P.actualZ j p.1 p.2) (P.length j) P.width
                (-P.rowSlope j p.1) (P.frequency k) P.scale y (P.length_pos j).ne' x)
          (by
            intro e j p k
            exact modulatedPlanarJet_continuous (alt j p.1 p.2 k)
              (P.actualX j p.1 p.2) (P.actualZ j p.1 p.2) (P.length j) P.width
              (-P.rowSlope j p.1) (P.frequency k) P.scale (P.length_pos j).ne' _)
          (by
            intro j p k x y
            exact modulatedPlanarJet_differentiable (alt j p.1 p.2 k)
              (P.actualX j p.1 p.2) (P.actualZ j p.1 p.2) (P.length j) P.width
              (-P.rowSlope j p.1) (P.frequency k) P.scale y (P.length_pos j).ne' _ x)
        refine ⟨bad,hbad,harea,?_⟩
        intro ab x z shift hshift hout
        have h := hpoint ab.1 ab.2 x z shift hshift hout
        simp only [hcoeff,hraw0] at h
        simpa only [F,rawInterval,Nat.add_sub_cancel,mul_assoc] using h)
  refine ⟨bad,hbad,harea,?_⟩
  intro lower upper z shift hshift hout
  simpa only [F,ht] using hpoint (lower,upper) z shift hshift hout

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedErrorFamily
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace LipschitzHilbert.SourceLabeledLattice

theorem eventually_selector_error_family_concentration_of_supported_oai
    (rate aWeight p M Lip : ℝ) (D K H J₀ : ℕ)
    (hrate : 0 ≤ rate) (haWeight : 0 ≤ aWeight) (hp : 0 ≤ p)
    (hM : 0 ≤ M) (hLip : 0 ≤ Lip) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : τ → ℕ) (Label : ∀ top, Fin (N top) → Type)
      (Item : ∀ top j, Label top j → Type) [∀ top j l, Fintype (Item top j l)]
      (P : ∀ top, SourceLabeledLattice (N top) κ (Label top) (Item top)),
      (∀ top, (P top).absoluteConstant ≤ L^p) →
      (∀ top, 6+2*(8*D+1) ≤ (P top).order) →
    ∀ (alt : ∀ top j (l : (P top).labels j), Item top j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ top j l u k,
        planarProfileConstant (alt top j l u k) (2*(P top).order) ≤ (P top).profileBound)
      (T : τ → SlopeBox),
      (∀ top, SourceSupportedLabeledTopGeometry (P top) (T top) (L^aWeight) D) →
    ∀ (angle : τ → ℝ) (small wide radius : ℝ) (E J : ℕ),
      (∀ top, 0 < angle top) → 0 < small → small ≤ 1 →
      wide ≤ small*(2:ℝ)^J → 1 ≤ wide*((2:ℝ)^E)^4 → radius ≤ K →
      (∀ top j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l => (T top).slope+(P top).rowSlope j l) (angle top*(2:ℝ)^j.val) H) →
    ∀ (b : ∀ top j, (P top).labels j → κ → ℝ → ℂ),
      (∀ top j l k, Measurable (b top j l k)) →
      (∀ top j l k s, ‖b top j l k s‖ ≤ M) →
      (∀ top j l k s, b top j l k s ≠ 0 →
        |s-((T top).slope+(P top).rowSlope j l)| ≤ radius*(angle top*(2:ℝ)^j.val)) →
      (∀ top j l k s, |s-(T top).slope| ≤ small*(angle top*(2:ℝ)^j.val) →
        ‖b top j l k s-b top j l k (T top).slope‖ ≤
          Lip*(|s-(T top).slope|/(angle top*(2:ℝ)^j.val))) →
      (∀ top j l k s, (wide*((2:ℝ)^E)^4)*(angle top*(2:ℝ)^j.val) < |s-(T top).slope| →
        b top j l k s = 0) →
    ∀ (v : τ → ℝ×ℝ → ℝ), (∀ top, Measurable (v top)) →
    ∀ (g : τ → ℝ×ℝ → EuclideanSpace ℂ κ), (∀ top, Measurable (g top)) →
      (∀ top z, ‖g top z‖ ≤ 1) →
      J ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
    ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-rate*L)*(∑ top, (T top).area)) ∧
      ∀ top lower upper z shift, |shift| ≤ (T top).width → z ∉ bad →
        let F := fun x y => ((P top).withProfile (alt top) (hAlt top)).rawInterval
          ((P top).physicalAngularErrorCoefficient (T top).slope (angle top) (b top) (v top) (g top))
          0 lower upper x y
        ‖F z.1 (z.2-(T top).slope*z.1+shift)‖+(T top).width*
          ‖covariantSignal (P top).frequency (fun k y => F z.1 y k)
            (z.2-(T top).slope*z.1+shift)‖ ≤
              L^(2*p+7)*((T top).weight (L^aWeight) (D:ℝ) z)^8 := by
  obtain ⟨Lt,_hLt,hthreshold⟩ := exists_selector_error_top_threshold
    (rate+1) aWeight p D (by linarith) haWeight hp
  filter_upwards [LabeledAngularErrorFamily.eventually_sourceAmplitude_le K H M Lip p,
    LabeledAngularErrorFamily.eventually_source_error_budgets (p+1) J₀,
    eventually_ge_atTop (max 2 Lt)] with L hAmp hBudget hlarge
  have hL : 2 ≤ L := (le_max_left _ _).trans hlarge
  have hLpos : 0 < L := by linarith
  have hKw : 0 < L^aWeight := Real.rpow_pos_of_pos hLpos _
  have hKw1 : 1 ≤ L^aWeight := Real.one_le_rpow (by linarith) haWeight
  intro τ κ _ _ N Label Item _ P hP horder alt hAlt T G angle small wide radius E J
    hangle hsmall hsmall1 hwide hwide1 hradius hlocal b hb hbM hsupport hnear hfar v hv
    g hg hg1 hJ hE
  classical
  let Err := fun top => (P top).angularErrorFamily (by have := horder top; omega)
    (T top).slope (angle top) small wide M Lip radius E J K H
    (hangle top) hsmall hsmall1 hwide hwide1 hM hLip hradius (hlocal top)
    (b top) (hb top) (hbM top) (hsupport top) (hnear top) (hfar top)
    (v top) (hv top) (g top) (hg top) (hg1 top)
  have hsource (top : τ) (y : ℝ) :
      ((Err top).sources y).sourceBound ≤ L^(p+4) ∧
      ((Err top).sources y).sumBound ≤ L^(p+4) := by
    have hA : (Err top).sourceAmplitude ≤ L^(p+1) :=
      hAmp (N top) (fun j => (P top).labels j) κ (fun j l => Item top j l) (Err top)
        le_rfl le_rfl le_rfl le_rfl (hP top)
    simpa only [show (p+1)+3 = p+4 by ring] using
      hBudget (N top) (fun j => (P top).labels j) κ (fun j l => Item top j l)
        (Err top) hA hJ hE y
  have hexists (top : τ) (i : Fin 2) : ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-(rate+1)*L)*(T top).area) ∧
      ∀ lower upper z shift, |shift| ≤ (T top).width → z ∉ bad →
        ‖((P top).withProfile (alt top) (hAlt top)).rawInterval
          ((P top).physicalAngularErrorCoefficient (T top).slope (angle top) (b top) (v top) (g top))
          (i.castLE (by decide)) lower upper z.1 (z.2-(T top).slope*z.1+shift)‖ ≤
            L^(2*p+6)*((T top).weight (L^aWeight) (D:ℝ) z)^8 := by
    obtain ⟨B,hB,harea,hpoint⟩ := (P top).selector_error_top_neighborhood_of_supported
      (by have := horder top; omega) (T top).slope (angle top) small wide M Lip radius E J K H
      (hangle top) hsmall hsmall1 hwide hwide1 hM hLip hradius (hlocal top)
      (b top) (hb top) (hbM top) (hsupport top) (hnear top) (hfar top)
      (v top) (hv top) (g top) (hg top) (hg1 top) (alt top) (hAlt top)
      (T top) (L^aWeight) D hKw (G top) rfl (horder top) (L^(p+4))
      (Real.rpow_nonneg hLpos.le _) i (rate+1) L
      (fun y => (hsource top y).1) (fun y => (hsource top y).2)
    refine ⟨B,hB,harea,?_⟩
    intro lower upper z shift hs hz
    apply (hpoint lower upper z shift
      (hs.trans (le_mul_of_one_le_left (T top).width_pos.le hKw1)) hz).trans
    exact mul_le_mul_of_nonneg_right
      (hthreshold L ((le_max_right _ _).trans hlarge) (P top).absoluteConstant (L^(p+4))
        (P top).absoluteConstant_pos.le (Real.rpow_nonneg hLpos.le _) (hP top) le_rfl)
      (pow_nonneg ((T top).weight_pos hKw (D:ℝ) z).le _)
  choose bad hbad using hexists
  let exceptional := ⋃ top, ⋃ i, bad top i
  have hexceptional : MeasurableSet exceptional :=
    MeasurableSet.iUnion fun top => MeasurableSet.iUnion fun i => (hbad top i).1
  refine ⟨exceptional,hexceptional,?_,?_⟩
  · have hm := measure_iUnion_fintype_le (volume.prod volume) (fun top => ⋃ i, bad top i)
    apply hm.trans
    calc
      _ ≤ ∑ top, ∑ i : Fin 2, (volume.prod volume) (bad top i) :=
        Finset.sum_le_sum fun top _ => measure_iUnion_fintype_le (volume.prod volume) _
      _ ≤ ∑ top, ∑ _i : Fin 2,
          ENNReal.ofReal (Real.exp (-(rate+1)*L)*(T top).area) :=
        Finset.sum_le_sum fun top _ => Finset.sum_le_sum fun i _ => (hbad top i).2.1
      _ = ENNReal.ofReal (2*Real.exp (-(rate+1)*L)*(∑ top, (T top).area)) := by
        simp only [Fin.sum_univ_two]
        simp_rw [← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le (T _).area_pos.le)
          (mul_nonneg (Real.exp_pos _).le (T _).area_pos.le)]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun top _ =>
          add_nonneg (mul_nonneg (Real.exp_pos _).le (T top).area_pos.le)
            (mul_nonneg (Real.exp_pos _).le (T top).area_pos.le))]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have he : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
        have hs : 0 ≤ ∑ top : τ, (T top).area :=
          Finset.sum_nonneg (fun top _ => (T top).area_pos.le)
        have hexp : 2*Real.exp (-(rate+1)*L) ≤ Real.exp (-rate*L) := by
          calc
            _ ≤ Real.exp L*Real.exp (-(rate+1)*L) :=
              mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
            _ = _ := by rw [← Real.exp_add]; congr 1; ring
        exact mul_le_mul_of_nonneg_right hexp hs
  · intro top lower upper z shift hs hout
    dsimp only
    let Q := (P top).withProfile (alt top) (hAlt top)
    let coeff := (P top).physicalAngularErrorCoefficient
      (T top).slope (angle top) (b top) (v top) (g top)
    let y := z.2-(T top).slope*z.1+shift
    have hjet (i : Fin 2) : ‖Q.rawInterval coeff (i.castLE (by decide)) lower upper z.1 y‖ ≤
        L^(2*p+6)*((T top).weight (L^aWeight) (D:ℝ) z)^8 :=
      (hbad top i).2.2 lower upper z shift hs (fun hi => hout
        (mem_iUnion.mpr ⟨top,mem_iUnion.mpr ⟨i,hi⟩⟩))
    have hscale : (T top).width ≤ |Q.scale| := by
      change (T top).width ≤ |(P top).scale|
      rw [(G top).scale_eq,abs_of_pos (mul_pos (by norm_num : (0:ℝ)<4)
        (mul_pos hKw (T top).width_pos))]
      nlinarith [(T top).width_pos]
    have hc := congrArg norm (Q.rawInterval_scaled_covariant coeff lower upper z.1 y)
    rw [norm_smul,Real.norm_eq_abs] at hc
    have hd : (T top).width*‖covariantSignal (P top).frequency
        (fun k yy => Q.rawInterval coeff 0 lower upper z.1 yy k) y‖ ≤
          L^(2*p+6)*((T top).weight (L^aWeight) (D:ℝ) z)^8 := by
      calc
        _ ≤ |Q.scale| * ‖covariantSignal Q.frequency
            (fun k yy => Q.rawInterval coeff 0 lower upper z.1 yy k) y‖ :=
          mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
        _ = _ := hc
        _ ≤ _ := hjet 1
    apply (add_le_add (hjet 0) hd).trans
    have hpow : 2*L^(2*p+6) ≤ L^(2*p+7) := by
      calc
        _ ≤ L*L^(2*p+6) := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hLpos.le _)
        _ = L^(1:ℝ)*L^(2*p+6) := by rw [Real.rpow_one]
        _ = L^(1+(2*p+6)) := (Real.rpow_add hLpos _ _).symm
        _ = _ := by congr 1; ring
    nlinarith [pow_nonneg ((T top).weight_pos hKw (D:ℝ) z).le 8,
      mul_le_mul_of_nonneg_right hpow (pow_nonneg ((T top).weight_pos hKw (D:ℝ) z).le 8)]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.SourceLabeledLattice.eventually_selector_error_family_concentration_of_supported_oai := @OAI.LipschitzHilbert.SourceLabeledLattice.eventually_selector_error_family_concentration_of_supported_oai
