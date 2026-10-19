-- Prove2me | solution 1 for OAI.StrictInverseFirstPower.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:20:39.65298+00:00
-- url     : https://prove2.me/submissions/b3f80bc6-6184-439c-8022-84e4aeeb4a96

import Mathlib
import Definitions.Def_StrictMeans
import Definitions.Def_OAIQWSIFP000
import Theorems.Thm_OAI_StrictInverseFirstPower_ae_bad_base_positive_zero
import Theorems.Thm_OAI_StrictInverseFirstPower_ae_base_positive_le_weighted

section
-- module Solutions.OAIQW_StrictInverseFirstPower.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.RectangleLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Complex
open scoped ENNReal Topology
namespace StrictInverseFirstPower
noncomputable section

lemma measurableSet_complexBox (S a b : ℝ) : MeasurableSet (complexBox S a b) :=
  ((isClosed_le Complex.continuous_re.abs continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le Complex.continuous_im continuous_const))).measurableSet

lemma lintegral_inv_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ y in Icc a b, ENNReal.ofReal (y⁻¹)) = ENNReal.ofReal (Real.log b-Real.log a) := by
  have hc : ContinuousOn (fun y : ℝ=>y⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ (fun y hy=>(ha.trans_le hy.1).ne')
  have hi : IntegrableOn (fun y : ℝ=>y⁻¹) (Icc a b) := hc.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact inv_nonneg.mpr (ha.le.trans hy.1)),integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab,integral_inv (notMem_uIcc_of_lt ha (ha.trans_le hab)),
    Real.log_div (ha.trans_le hab).ne' ha.ne']

lemma lintegral_complexBox_inv {S a b : ℝ} (_hS : 0 ≤ S) (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ z in complexBox S a b, ENNReal.ofReal (z.im⁻¹)) =
      ENNReal.ofReal (2*S*(Real.log b-Real.log a)) := by
  let E := Complex.measurableEquivRealProd
  let R : Set (ℝ × ℝ) := Icc (-S) S ×ˢ Icc a b
  have hR : MeasurableSet R := measurableSet_Icc.prod measurableSet_Icc
  have he : E ⁻¹' R = complexBox S a b := by
    ext z
    simp [E,R,complexBox,abs_le,and_assoc,and_left_comm,and_comm]
  have hm : Measurable (fun p : ℝ × ℝ=>ENNReal.ofReal (p.2⁻¹)) :=
    measurable_snd.inv.ennreal_ofReal
  have hi := Complex.volume_preserving_equiv_real_prod.lintegral_comp (hm.indicator hR)
  rw [← lintegral_indicator (measurableSet_complexBox S a b)]
  have hp : (fun z : ℂ=>(complexBox S a b).indicator
      (fun z=>ENNReal.ofReal (z.im⁻¹)) z) =
      (fun z=>(R.indicator (fun p=>ENNReal.ofReal (p.2⁻¹))) (E z)) := by
    funext z
    rw [← he]
    rfl
  rw [hp,hi,lintegral_indicator hR,Measure.volume_eq_prod,← Measure.prod_restrict]
  rw [lintegral_prod _ (hm.aemeasurable)]
  dsimp only
  rw [lintegral_inv_Icc ha hab,lintegral_const,
    Measure.restrict_apply_univ,Real.volume_Icc,← ENNReal.ofReal_mul]
  · congr 1
    ring
  · exact sub_nonneg.mpr (Real.log_le_log ha hab)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.HalfPlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma affineAt_assoc (z w : UpperHalfPlane) (u : ℂ) :
    affineAt z (affineAt w u) = affineAt (affineProduct z w) u := by
  change (z.re : ℂ) + (z.im : ℂ) * ((w.re : ℂ) + (w.im : ℂ) * u) =
    ((affineAt z w).re : ℂ) + ((affineAt z w).im : ℂ) * u
  rw [affineAt_re, affineAt_im]
  change (z.re : ℂ) + (z.im : ℂ) * ((w.re : ℂ) + (w.im : ℂ) * u) =
    ((z.re + z.im * w.re : ℝ) : ℂ) + ((z.im * w.im : ℝ) : ℂ) * u
  push_cast
  ring

end
end StrictInverseFirstPower

open Set Filter Metric Complex Function
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.Rebasing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma rebase_one (f : DiskFamily) : rebase f UpperHalfPlane.I = f := by
  apply diskFamily_ext
  intro w
  rw [halfPlaneFunction_rebase f _ w.im_pos]
  simp

lemma rebase_assoc (f : DiskFamily) (z w : UpperHalfPlane) :
    rebase (rebase f z) w = rebase f (affineProduct z w) := by
  apply diskFamily_ext
  intro u
  rw [halfPlaneFunction_rebase (rebase f z) w u.im_pos,
    halfPlaneFunction_rebase f z (affineAt_mapsTo w u.im_pos),
    halfPlaneFunction_rebase f z w.im_pos,
    halfPlaneFunction_rebase_deriv,
    halfPlaneFunction_rebase f (affineProduct z w) u.im_pos]
  rw [affineAt_assoc, show (affineProduct z w).im = z.im * w.im from affineAt_im z w]
  push_cast
  simp only [coe_affineProduct]
  field_simp [halfPlaneFunction_deriv_ne_zero f z.im_pos]
  ring

lemma halfPlaneQ_ne_zero (f : DiskFamily) (z : UpperHalfPlane) : halfPlaneQ f z ≠ 0 :=
  inv_ne_zero (halfPlaneFunction_deriv_ne_zero f z.im_pos)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.TransferOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma affineOperator_monotone (z : UpperHalfPlane) : Monotone (affineOperator z) := by
  intro φ ψ h f
  change ‖halfPlaneQ f z‖ * φ (rebase f z) ≤ ‖halfPlaneQ f z‖ * ψ (rebase f z)
  exact mul_le_mul_of_nonneg_left (h (rebase f z)) (norm_nonneg _)

lemma affineOperator_mul (z w : UpperHalfPlane) :
    affineOperator z * affineOperator w = affineOperator (affineProduct z w) := by
  ext φ f
  simp only [mul_apply_eq_comp, affineOperator_apply, rebase_assoc, halfPlaneQ_rebase,
    norm_div]
  field_simp [norm_ne_zero_iff.mpr (halfPlaneQ_ne_zero f z)]

@[simp] lemma affineOperator_one : affineOperator UpperHalfPlane.I = 1 := by
  ext φ f
  simp [rebase_one]

lemma dyadicOperator_monotone : Monotone dyadicOperator := by
  intro φ ψ h f
  change (1 / 2 : ℝ) * _ ≤ (1 / 2 : ℝ) * _
  exact mul_le_mul_of_nonneg_left
    (add_le_add (affineOperator_monotone dyadicLeft h f)
      (affineOperator_monotone dyadicRight h f)) (by norm_num)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.DyadicBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma cayleyToDisk_norm_relation (z : UpperHalfPlane) :
    (1 - ‖cayleyToDisk z‖ ^ 2) * ‖(z : ℂ) + I‖ ^ 2 = 4 * z.im := by
  have hd : ‖(z : ℂ) + I‖ ≠ 0 := norm_ne_zero_iff.mpr (add_I_ne_zero z.im_pos)
  rw [cayleyToDisk, norm_div, div_pow]
  field_simp
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, add_re, I_re, add_zero, add_im, I_im,
    sub_re, sub_zero, sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

lemma halfPlaneQ_norm (f : DiskFamily) (z : UpperHalfPlane) :
    ‖halfPlaneQ f z‖ = ‖(z : ℂ) + I‖ ^ 2 /
      (4 * ‖deriv (diskExtension f.val) (cayleyToDisk z)‖) := by
  rw [halfPlaneQ, norm_inv, halfPlaneFunction_deriv f z.im_pos]
  simp only [norm_mul, norm_ofNat, norm_I, mul_one, norm_div, norm_pow]
  field_simp
  ring

lemma halfPlaneQ_strip_bound (f : DiskFamily) (z : UpperHalfPlane)
    (hx : |z.re| ≤ 2) (hy : z.im ≤ 1) : ‖halfPlaneQ f z‖ ≤ 64 / z.im := by
  let r := ‖cayleyToDisk z‖
  let d := ‖deriv (diskExtension f.val) (cayleyToDisk z)‖
  let D := ‖(z : ℂ) + I‖ ^ 2
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr : r < 1 := by
    simpa only [mem_ball, dist_zero_right] using cayleyToDisk_mem z.im_pos
  have hD0 : 0 ≤ D := sq_nonneg _
  have hD : D ≤ 8 := by
    dsimp only [D]
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, add_re, add_im, I_re, I_im, add_zero,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    have ha := abs_le.mp hx
    nlinarith [z.im_pos]
  have hd0 : 0 < d := norm_pos_iff.mpr
    (diskFamily_derivative_ne_zero f ⟨_, cayleyToDisk_mem z.im_pos⟩)
  have hrel : (1 - r) * (1 + r) * D = 4 * z.im := by
    have hh := cayleyToDisk_norm_relation z
    dsimp only [r, D]
    nlinarith [hh]
  have hylo : z.im ≤ 4 * (1 - r) := by
    have h := mul_le_mul_of_nonneg_left hD (mul_nonneg (by linarith) (by linarith))
    have h' := mul_le_mul_of_nonneg_left (show 1 + r ≤ 2 by linarith)
      (show 0 ≤ 8 * (1 - r) by positivity)
    nlinarith
  have hd := (derivative_distortion_disk f.property.1 f.property.2.1 f.property.2.2.2 hr).1
  change (1 - r) / (1 + r) ^ 3 ≤ d at hd
  have hp : 0 < (1 + r) ^ 3 := pow_pos (by linarith) _
  have hd' := (div_le_iff₀ hp).mp hd
  have hc : (1 + r) ^ 3 ≤ 8 := by
    simpa only [show (2 : ℝ)^3 = 8 by norm_num] using pow_le_pow_left₀ (show 0 ≤ 1 + r by linarith)
      (show 1 + r ≤ 2 by linarith) 3
  have hds : z.im ≤ 32 * d := by
    have hh := mul_le_mul_of_nonneg_left hc hd0.le
    nlinarith
  rw [halfPlaneQ_norm, div_le_div_iff₀ (mul_pos (by norm_num) hd0) z.im_pos]
  change D * z.im ≤ 64 * (4 * d)
  have hh := mul_le_mul_of_nonneg_right hD z.im_pos.le
  nlinarith

end
end StrictInverseFirstPower

open Set Filter Metric Complex Function MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma affineProduct_xyPoint (x y s t : ℝ) (hy : 0 < y) (ht : 0 < t) :
    affineProduct (xyPoint x y hy) (xyPoint s t ht) =
      xyPoint (x + y * s) (y * t) (mul_pos hy ht) := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, xyPoint]
  ring

lemma dyadicHeight_le_one (n : ℕ) : dyadicHeight n ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)
lemma dyadicHeight_succ (n : ℕ) : dyadicHeight (n + 1) = dyadicHeight n / 2 := by
  simp [dyadicHeight, pow_succ, div_eq_mul_inv]

lemma dyadicLeft_gridStart (n : ℕ) : affineProduct dyadicLeft (gridStart n) = gridStart (n + 1) := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, dyadicLeft, gridStart, xyPoint, dyadicHeight_succ]
  ring
lemma dyadicRight_gridEnd (n : ℕ) : affineProduct dyadicRight (gridEnd n) = gridEnd (n + 1) := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, dyadicRight, gridEnd, xyPoint, dyadicHeight_succ]
  ring
lemma dyadic_gridMiddle (n : ℕ) :
    affineProduct dyadicLeft (gridEnd n) = affineProduct dyadicRight (gridStart n) := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, dyadicLeft, dyadicRight, gridStart, gridEnd, xyPoint]
  ring

lemma dyadic_shift (n : ℕ) :
    dyadicOperator ^ n * affineOperator (horizontalPoint 2) - dyadicOperator ^ n =
      dyadicHeight n • (affineOperator (gridEnd n) - affineOperator (gridStart n)) := by
  induction n with
  | zero =>
    have hs : gridStart 0 = UpperHalfPlane.I := by apply UpperHalfPlane.ext; simp [gridStart, dyadicHeight, xyPoint]
    have he : gridEnd 0 = horizontalPoint 2 := by apply UpperHalfPlane.ext; norm_num [gridEnd, horizontalPoint, dyadicHeight, xyPoint]
    simp [hs, he, dyadicHeight]
  | succ n ih =>
    rw [pow_succ', mul_assoc, ← mul_sub, ih, mul_smul_comm,
      dyadicOperator, smul_mul_assoc, smul_smul, mul_sub, add_mul, add_mul,
      affineOperator_mul, affineOperator_mul, affineOperator_mul, affineOperator_mul,
      dyadicLeft_gridStart, dyadicRight_gridEnd, dyadic_gridMiddle]
    have hc (a b c : C(DiskFamily, ℝ) →L[ℝ] C(DiskFamily, ℝ)) :
        (c + a) - (b + c) = a - b := by abel
    rw [hc]
    congr 1

lemma affineOperator_strip_norm (z : UpperHalfPlane) (hx : |z.re| ≤ 2) (hy : z.im ≤ 1) :
    ‖affineOperator z‖ ≤ 64 / z.im :=
  affineOperator_norm_bound (by positivity) (fun f => halfPlaneQ_strip_bound f z hx hy)

lemma dyadic_shift_norm_le (n : ℕ) :
    ‖dyadicOperator ^ n * affineOperator (horizontalPoint 2) - dyadicOperator ^ n‖ ≤ 128 := by
  have hv := dyadicHeight_pos n
  have hv1 := dyadicHeight_le_one n
  have hs := affineOperator_strip_norm (gridStart n)
    (by simp only [gridStart, xyPoint_re]; rw [abs_le]; constructor <;> linarith)
    (by simpa only [gridStart, xyPoint_im] using hv1)
  have he := affineOperator_strip_norm (gridEnd n)
    (by simp only [gridEnd, xyPoint_re]; rw [abs_le]; constructor <;> linarith)
    (by simpa only [gridEnd, xyPoint_im] using hv1)
  simp only [gridEnd, gridStart, xyPoint_im] at hs he
  rw [dyadic_shift]
  calc
    _ ≤ ‖dyadicHeight n‖ * ‖affineOperator (gridEnd n) - affineOperator (gridStart n)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ dyadicHeight n * (‖affineOperator (gridEnd n)‖ + ‖affineOperator (gridStart n)‖) := by
      rw [Real.norm_of_nonneg hv.le]
      apply mul_le_mul_of_nonneg_left _ hv.le
      exact norm_sub_le (affineOperator (gridEnd n)) (affineOperator (gridStart n))
    _ ≤ dyadicHeight n * (64 / dyadicHeight n + 64 / dyadicHeight n) :=
      mul_le_mul_of_nonneg_left (add_le_add he hs) hv.le
    _ = 128 := by field_simp; ring

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.SpectralGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology

open Set Filter
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

variable {A : Type*} [NormedRing A]

lemma logNormPower_div_bddBelow (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖) :
    BddBelow (range (fun n : ℕ => Real.log ‖a ^ n‖ / n)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact div_nonneg (Real.log_nonneg (h n)) (Nat.cast_nonneg n)

lemma tendsto_logNormGrowth (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖) :
    Tendsto (fun n : ℕ => Real.log ‖a ^ n‖ / n) atTop (𝓝 (logNormGrowth a h)) :=
  (logNormPower_subadditive a h).tendsto_lim (logNormPower_div_bddBelow a h)

lemma logNormGrowth_nonneg (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖) :
    0 ≤ logNormGrowth a h :=
  ge_of_tendsto (tendsto_logNormGrowth a h) (Eventually.of_forall fun n =>
    div_nonneg (Real.log_nonneg (h n)) (Nat.cast_nonneg n))

lemma normPower_eventually_le_exp (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖)
    {b : ℝ} (hb : logNormGrowth a h < b) :
    ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ Real.exp (b * n) := by
  filter_upwards [(tendsto_logNormGrowth a h).eventually (gt_mem_nhds hb),
    eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have he : Real.log ‖a ^ n‖ < b * n := (div_lt_iff₀ hnpos).mp hn
  exact (Real.log_lt_iff_lt_exp (lt_of_lt_of_le zero_lt_one (h n))).mp he |>.le

lemma logNormGrowth_le_of_power_bound (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖)
    {M r : ℝ} (hM : 0 < M) (hr : 0 < r) (hb : ∀ n : ℕ, ‖a ^ n‖ ≤ M * r ^ n) :
    logNormGrowth a h ≤ Real.log r := by
  have hlim : Tendsto (fun n : ℕ => Real.log M / n + Real.log r) atTop (𝓝 (Real.log r)) := by
    simpa using (tendsto_natCast_atTop_atTop.const_div_atTop (Real.log M)).add_const (Real.log r)
  apply le_of_tendsto_of_tendsto (tendsto_logNormGrowth a h) hlim
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hh := Real.log_le_log (lt_of_lt_of_le zero_lt_one (h n)) (hb n)
  rw [Real.log_mul hM.ne' (pow_pos hr n).ne', Real.log_pow] at hh
  rw [div_le_iff₀ hn0]
  calc
    Real.log ‖a ^ n‖ ≤ Real.log M + n * Real.log r := hh
    _ = (Real.log M / n + Real.log r) * n := by field_simp

variable [NormedAlgebra ℝ A] [CompleteSpace A]

lemma summable_resolventPower (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖)
    {τ : ℝ} (hτ : 0 < τ) (hg : logNormGrowth a h < Real.log τ) :
    Summable (fun n : ℕ => (τ⁻¹) ^ n • a ^ n) := by
  obtain ⟨b, hb, hbτ⟩ := exists_between hg
  let r := Real.exp b / τ
  have hr0 : 0 ≤ r := (div_pos (Real.exp_pos b) hτ).le
  have hr1 : r < 1 := by
    apply (div_lt_one hτ).mpr
    exact (Real.exp_lt_exp.mpr hbτ).trans_eq (Real.exp_log hτ)
  have hs : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [normPower_eventually_le_exp a h hb] with n hn
  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hτ.le) n)]
  calc
    τ⁻¹ ^ n * ‖a ^ n‖ ≤ τ⁻¹ ^ n * Real.exp (b * n) :=
      mul_le_mul_of_nonneg_left hn (pow_nonneg (inv_nonneg.mpr hτ.le) n)
    _ = r ^ n := by
      rw [mul_comm b (n : ℝ), Real.exp_nat_mul]
      simp [r, div_eq_mul_inv, mul_pow, mul_comm]

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.PositiveFunctionals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology

open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

lemma continuousMap_order_bound (f : C(X, ℝ)) :
    -(‖f‖ • (1 : C(X, ℝ))) ≤ f ∧ f ≤ ‖f‖ • (1 : C(X, ℝ)) := by
  constructor <;> intro x
  · have h := (abs_le.mp (f.norm_coe_le_norm x)).1
    simpa using h
  · have h := (abs_le.mp (f.norm_coe_le_norm x)).2
    simpa using h

omit [CompactSpace X] in
lemma positiveOperator_unit_nonneg (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hL : Monotone L) :
    0 ≤ L 1 := by
  simpa only [map_zero] using hL (show (0 : C(X, ℝ)) ≤ 1 by intro x; simp)

lemma positiveOperator_apply_abs_le (L : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hL : Monotone L) (f : C(X, ℝ)) (x : X) :
    |L f x| ≤ ‖f‖ * L 1 x := by
  have hlo := hL (continuousMap_order_bound f).1
  have hhi := hL (continuousMap_order_bound f).2
  rw [map_neg, map_smul] at hlo
  rw [map_smul] at hhi
  exact abs_le.mpr ⟨by simpa using hlo x, by simpa using hhi x⟩

lemma positiveOperator_norm [Nonempty X] (L : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hL : Monotone L) : ‖L‖ = ‖L 1‖ := by
  apply le_antisymm
  · apply L.opNorm_le_bound (norm_nonneg _)
    intro f
    apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    intro x
    rw [Real.norm_eq_abs]
    calc
      |L f x| ≤ ‖f‖ * L 1 x := positiveOperator_apply_abs_le L hL f x
      _ ≤ ‖f‖ * ‖L 1‖ := mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans ((L 1).norm_coe_le_norm x)) (norm_nonneg _)
      _ = _ := mul_comm _ _
  · simpa only [norm_one, mul_one] using L.le_opNorm (1 : C(X, ℝ))

lemma positiveOperator_pow_monotone (L : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hL : Monotone L) (n : ℕ) : Monotone (L ^ n) := by
  induction n with
  | zero => simpa using (monotone_id : Monotone (id : C(X, ℝ) → C(X, ℝ)))
  | succ n ih =>
    rw [pow_succ']
    intro f g h
    exact hL (ih h)

lemma positiveOperator_pow_norm [Nonempty X] (L : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hL : Monotone L) (n : ℕ) : ‖L ^ n‖ = ‖(L ^ n) 1‖ :=
  positiveOperator_norm (L ^ n) (positiveOperator_pow_monotone L hL n)

lemma positiveOperator_iterate_bound [Nonempty X]
    (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hL : Monotone L)
    (g : C(X, ℝ)) {a M : ℝ} (ha : 0 ≤ a)
    (hg : (1 : C(X, ℝ)) ≤ g) (hM : g ≤ M • (1 : C(X, ℝ)))
    (hsuper : L g ≤ a • g) (n : ℕ) : ‖L ^ n‖ ≤ M * a ^ n := by
  have hM0 : 0 ≤ M := by
    obtain ⟨x⟩ := ‹Nonempty X›
    have hh := (hg.trans hM) x
    have : (1 : ℝ) ≤ M := by simpa using hh
    linarith
  have hp : (L ^ n) g ≤ a ^ n • g := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      change L ((L ^ n) g) ≤ a ^ (n + 1) • g
      calc
        L ((L ^ n) g) ≤ L (a ^ n • g) := hL ih
        _ = a ^ n • L g := L.map_smul _ _
        _ ≤ a ^ n • (a • g) := smul_le_smul_of_nonneg_left hsuper (pow_nonneg ha n)
        _ = a ^ (n + 1) • g := by rw [smul_smul, pow_succ]
  rw [positiveOperator_pow_norm L hL n]
  apply (ContinuousMap.norm_le _ (mul_nonneg hM0 (pow_nonneg ha n))).mpr
  intro x
  have hn := positiveOperator_unit_nonneg (L ^ n) (positiveOperator_pow_monotone L hL n) x
  change (0 : ℝ) ≤ ((L ^ n) 1) x at hn
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  have h1 := positiveOperator_pow_monotone L hL n hg x
  have h2 := hp x
  have h3 := hM x
  change ((L ^ n) 1) x ≤ ((L ^ n) g) x at h1
  change ((L ^ n) g) x ≤ a ^ n * g x at h2
  change g x ≤ M * 1 at h3
  calc
    ((L ^ n) 1) x ≤ a ^ n * g x := h1.trans h2
    _ ≤ a ^ n * M := mul_le_mul_of_nonneg_left (by simpa using h3) (pow_nonneg ha n)
    _ = M * a ^ n := mul_comm _ _

variable [T2Space X] [MeasurableSpace X] [BorelSpace X]

lemma exists_probabilityMeasure_of_positiveFunctional
    (Λ : C(X, ℝ) →L[ℝ] ℝ) (hΛ : Monotone Λ) (h1 : Λ 1 = 1) :
    ∃ μ : ProbabilityMeasure X, ∀ f : C(X, ℝ), ∫ x, f x ∂(μ : Measure X) = Λ f := by
  let Λc := compactTestFunctional Λ hΛ
  let μ := RealRMK.rieszMeasure Λc
  have he (f : C(X, ℝ)) : ∫ x, f x ∂μ = Λ f := by
    let fc : CompactlySupportedContinuousMap X ℝ :=
      { toContinuousMap := f
        hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
    exact RealRMK.integral_rieszMeasure Λc fc
  have hμ : IsProbabilityMeasure μ := by
    constructor
    apply (ENNReal.toReal_eq_one_iff _).mp
    change μ.real univ = 1
    have hh := he (1 : C(X, ℝ))
    simpa only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one, h1] using hh
  exact ⟨⟨μ, hμ⟩, he⟩

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.Eigenmeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

omit [CompleteSpace A] in
lemma scaled_power (a : A) (t : ℝ) (n : ℕ) : (t • a) ^ n = t ^ n • a ^ n :=
  smul_pow t a n

lemma summable_growthResolvent (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖)
    {τ : ℝ} (hτ : 0 < τ) (hg : logNormGrowth a h < Real.log τ) :
    Summable (fun n : ℕ => (τ⁻¹ • a) ^ n) := by
  simpa only [smul_pow] using summable_resolventPower a h hτ hg

lemma growthResolvent_mul (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖)
    {τ : ℝ} (hτ : 0 < τ) (hg : logNormGrowth a h < Real.log τ) :
    growthResolvent a τ * a = τ • (growthResolvent a τ - 1) := by
  have hh := (summable_growthResolvent a h hτ hg).tsum_pow_mul_one_sub
  change growthResolvent a τ * (1 - τ⁻¹ • a) = 1 at hh
  rw [mul_sub, mul_one, mul_smul_comm] at hh
  have he : τ⁻¹ • (growthResolvent a τ * a) = growthResolvent a τ - 1 := by
    exact (sub_eq_iff_eq_add.mp hh).symm |> eq_sub_of_add_eq'
  calc
    growthResolvent a τ * a = τ • (τ⁻¹ • (growthResolvent a τ * a)) := by
      rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
    _ = τ • (growthResolvent a τ - 1) := congrArg (τ • ·) he

lemma mul_growthResolvent (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖)
    {τ : ℝ} (hτ : 0 < τ) (hg : logNormGrowth a h < Real.log τ) :
    a * growthResolvent a τ = τ • (growthResolvent a τ - 1) := by
  have hh := (summable_growthResolvent a h hτ hg).one_sub_mul_tsum_pow
  change (1 - τ⁻¹ • a) * growthResolvent a τ = 1 at hh
  rw [sub_mul, one_mul, smul_mul_assoc] at hh
  have he : τ⁻¹ • (a * growthResolvent a τ) = growthResolvent a τ - 1 := by
    exact (sub_eq_iff_eq_add.mp hh).symm |> eq_sub_of_add_eq'
  calc
    a * growthResolvent a τ = τ • (τ⁻¹ • (a * growthResolvent a τ)) := by
      rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
    _ = τ • (growthResolvent a τ - 1) := congrArg (τ • ·) he

section Positive
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

lemma growthResolvent_apply_series (L : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (h : ∀ n : ℕ, 1 ≤ ‖L ^ n‖) {τ : ℝ} (hτ : 0 < τ)
    (hg : logNormGrowth L h < Real.log τ) (f : C(X, ℝ)) (x : X) :
    growthResolvent L τ f x = ∑' n : ℕ, τ⁻¹ ^ n * ((L ^ n) f) x := by
  let e := (ContinuousMap.evalCLM ℝ x).comp (ContinuousLinearMap.apply ℝ C(X, ℝ) f)
  have he := e.map_tsum (summable_growthResolvent L h hτ hg)
  change growthResolvent L τ f x = _ at he
  rw [he]
  apply tsum_congr
  intro n
  rw [scaled_power]
  simp [e]

lemma growthResolvent_monotone (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hL : Monotone L)
    (h : ∀ n : ℕ, 1 ≤ ‖L ^ n‖) {τ : ℝ} (hτ : 0 < τ)
    (hg : logNormGrowth L h < Real.log τ) : Monotone (growthResolvent L τ : C(X, ℝ) →L[ℝ] C(X, ℝ)) := by
  have hp : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ growthResolvent L τ f := by
    intro f hf x
    change (0 : ℝ) ≤ growthResolvent L τ f x
    rw [growthResolvent_apply_series L h hτ hg]
    apply tsum_nonneg
    intro n
    apply mul_nonneg (pow_nonneg (inv_nonneg.mpr hτ.le) n)
    have hh := positiveOperator_pow_monotone L hL n hf x
    change ((L ^ n) 0) x ≤ ((L ^ n) f) x at hh
    simpa only [map_zero, ContinuousMap.zero_apply] using hh
  intro f g hfg
  rw [← sub_nonneg, ← map_sub]
  exact hp (g - f) (sub_nonneg.mpr hfg)

lemma growthResolvent_unit_ge_one (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hL : Monotone L)
    (h : ∀ n : ℕ, 1 ≤ ‖L ^ n‖) {τ : ℝ} (hτ : 0 < τ)
    (hg : logNormGrowth L h < Real.log τ) : (1 : C(X, ℝ)) ≤ growthResolvent L τ 1 := by
  intro x
  let e := (ContinuousMap.evalCLM ℝ x).comp (ContinuousLinearMap.apply ℝ C(X, ℝ) (1 : C(X, ℝ)))
  have hs := e.summable (summable_growthResolvent L h hτ hg)
  have hh := hs.le_tsum 0 (fun n _ => show 0 ≤ e ((τ⁻¹ • L) ^ n) from by
    rw [scaled_power L τ⁻¹ n]
    change 0 ≤ τ⁻¹ ^ n * ((L ^ n) 1) x
    exact mul_nonneg (pow_nonneg (inv_nonneg.mpr hτ.le) n)
      (positiveOperator_unit_nonneg (L ^ n) (positiveOperator_pow_monotone L hL n) x))
  have he := e.map_tsum (summable_growthResolvent L h hτ hg)
  rw [← he] at hh
  simpa [e, growthResolvent] using hh

end Positive

end
end StrictInverseFirstPower

namespace StrictInverseFirstPower
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [T2Space X] [MeasurableSpace X] [BorelSpace X]

lemma exists_approximate_eigenprobability
    (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hL : Monotone L)
    (h : ∀ n : ℕ, 1 ≤ ‖L ^ n‖) {τ : ℝ} (hτ : 0 < τ)
    (hg : logNormGrowth L h < Real.log τ) :
    ∃ μ : ProbabilityMeasure X, ∀ f : C(X, ℝ),
      |(∫ x, L f x ∂(μ : Measure X)) - τ * ∫ x, f x ∂(μ : Measure X)| ≤
        (τ - Real.exp (logNormGrowth L h)) * ‖f‖ := by
  let R := growthResolvent L τ
  let g := R (1 : C(X, ℝ))
  have hR : Monotone R := growthResolvent_monotone L hL h hτ hg
  have hg1 : (1 : C(X, ℝ)) ≤ g := growthResolvent_unit_ge_one L hL h hτ hg
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn (univ_nonempty : (univ : Set X).Nonempty)
    g.continuous.continuousOn
  let M := g x
  have hM1 : 1 ≤ M := hg1 x
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hM : g ≤ M • (1 : C(X, ℝ)) := by
    intro y
    change g y ≤ M * 1
    rw [mul_one]
    exact hx (mem_univ y)
  have hMi : M⁻¹ ≤ 1 := by
    rw [inv_eq_one_div, div_le_one hMpos]
    exact hM1
  let a := τ * (1 - M⁻¹)
  have ha : 0 ≤ a := mul_nonneg hτ.le (sub_nonneg.mpr hMi)
  have hLg : L g = τ • (g - 1) := by
    have hh := congrArg (fun S : C(X, ℝ) →L[ℝ] C(X, ℝ) => S 1)
      (mul_growthResolvent L h hτ hg)
    exact hh
  have hsuper : L g ≤ a • g := by
    rw [hLg]
    intro y
    change τ * (g y - 1) ≤ a * g y
    have hi : M⁻¹ * g y ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_left (hx (mem_univ y)) (inv_nonneg.mpr hMpos.le)
      change M⁻¹ * g y ≤ M⁻¹ * M at hh
      simpa only [inv_mul_cancel₀ hMpos.ne'] using hh
    dsimp [a]
    nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr hi)]
  have hiter (n : ℕ) : ‖L ^ n‖ ≤ M * a ^ n :=
    positiveOperator_iterate_bound L hL g ha hg1 hM hsuper n
  have hapos : 0 < a := by
    have hh := (h 1).trans (hiter 1)
    simp only [pow_one] at hh
    by_contra hn
    have hz : a = 0 := le_antisymm (le_of_not_gt hn) ha
    norm_num [hz] at hh
  have hρ : Real.exp (logNormGrowth L h) ≤ a := by
    calc
      Real.exp (logNormGrowth L h) ≤ Real.exp (Real.log a) :=
        Real.exp_le_exp.mpr (logNormGrowth_le_of_power_bound L h hMpos hapos hiter)
      _ = a := Real.exp_log hapos
  have herr : τ / M ≤ τ - Real.exp (logNormGrowth L h) := by
    dsimp [a] at hρ
    rw [div_eq_mul_inv]
    nlinarith
  have herr0 : 0 ≤ τ / M := (div_pos hτ hMpos).le
  let Λ : C(X, ℝ) →L[ℝ] ℝ := M⁻¹ • ((ContinuousMap.evalCLM ℝ x).comp R)
  have hΛ : Monotone Λ := by
    intro f₁ f₂ hf
    change M⁻¹ * R f₁ x ≤ M⁻¹ * R f₂ x
    exact mul_le_mul_of_nonneg_left (hR hf x) (inv_nonneg.mpr hMpos.le)
  have hΛ1 : Λ 1 = 1 := by
    change M⁻¹ * M = 1
    exact inv_mul_cancel₀ hMpos.ne'
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_of_positiveFunctional Λ hΛ hΛ1
  refine ⟨μ, fun f => ?_⟩
  rw [hμ (L f), hμ f]
  change |M⁻¹ * R (L f) x - τ * (M⁻¹ * R f x)| ≤ _
  have hh := congrArg (fun S : C(X, ℝ) →L[ℝ] C(X, ℝ) => S f x)
    (growthResolvent_mul L h hτ hg)
  change R (L f) x = τ * (R f x - f x) at hh
  rw [hh]
  have hid : M⁻¹ * (τ * (R f x - f x)) - τ * (M⁻¹ * R f x) = -(τ / M * f x) := by
    rw [div_eq_mul_inv]
    ring
  rw [hid, abs_neg, abs_mul, abs_of_nonneg herr0]
  exact (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) herr0).trans
    (mul_le_mul_of_nonneg_right herr (norm_nonneg f))

theorem exists_exact_eigenprobability [TopologicalSpace.MetrizableSpace X]
    (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hL : Monotone L)
    (h : ∀ n : ℕ, 1 ≤ ‖L ^ n‖) :
    ∃ μ : ProbabilityMeasure X, ∀ f : C(X, ℝ),
      (∫ x, L f x ∂(μ : Measure X)) =
        Real.exp (logNormGrowth L h) * ∫ x, f x ∂(μ : Measure X) := by
  classical
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let ρ := Real.exp (logNormGrowth L h)
  have hρ : 0 < ρ := Real.exp_pos _
  let τ (n : ℕ) := ρ + 1 / ((n : ℝ) + 1)
  have hτgt (n : ℕ) : ρ < τ n := by
    dsimp [τ]
    have hn : (0 : ℝ) < n + 1 := by positivity
    exact lt_add_of_pos_right _ (one_div_pos.mpr hn)
  have hτ (n : ℕ) : 0 < τ n := hρ.trans (hτgt n)
  have hg (n : ℕ) : logNormGrowth L h < Real.log (τ n) := by
    calc
      logNormGrowth L h = Real.log ρ := (Real.log_exp _).symm
      _ < Real.log (τ n) := Real.log_lt_log hρ (hτgt n)
  choose μ hμ using fun n => exists_approximate_eigenprobability L hL h (hτ n) (hg n)
  obtain ⟨ν, φ, hφ, hν⟩ := CompactSpace.tendsto_subseq μ
  refine ⟨ν, fun f => ?_⟩
  have hτlim : Tendsto τ atTop (𝓝 ρ) := by
    simpa only [add_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_add ρ
  have hτφ : Tendsto (τ ∘ φ) atTop (𝓝 ρ) := hτlim.comp hφ.tendsto_atTop
  have hf := (ProbabilityMeasure.continuous_integral_continuousMap f).tendsto ν |>.comp hν
  have hLf := (ProbabilityMeasure.continuous_integral_continuousMap (L f)).tendsto ν |>.comp hν
  have habs := (hLf.sub (hτφ.mul hf)).abs
  have hzero : Tendsto (fun n => (τ (φ n) - ρ) * ‖f‖) atTop (𝓝 0) := by
    convert! (hτφ.sub_const ρ).mul_const ‖f‖ using 1; simp only [sub_self, zero_mul]
  have hh : |(∫ x, L f x ∂(ν : Measure X)) - ρ * ∫ x, f x ∂(ν : Measure X)| ≤ 0 :=
    le_of_tendsto_of_tendsto habs hzero (Eventually.of_forall fun n => hμ (φ n) f)
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.HorizontalAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology

open Set Filter Function MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma probabilityFunctional_monotone (μ : ProbabilityMeasure X) : Monotone (probabilityFunctional μ) :=
  fun f g h => integral_mono (compactTest_integrable _ f) (compactTest_integrable _ g) h

lemma eigenfunctional_power {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E) (Λ : E →L[ℝ] ℝ) (ρ : ℝ)
    (h : ∀ f, Λ (L f) = ρ * Λ f) (n : ℕ) (f : E) :
    Λ ((L ^ n) f) = ρ ^ n * Λ f := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_apply_eq_comp, h, ih, pow_succ]; ring

lemma dyadicLogGrowth_nonneg : 0 ≤ dyadicLogGrowth :=
  logNormGrowth_nonneg _ _
lemma dyadicExponent_nonneg : 0 ≤ dyadicExponent :=
  div_nonneg dyadicLogGrowth_nonneg (Real.log_nonneg (by norm_num))

theorem exists_dyadic_eigenfunctional :
    ∃ Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ, Monotone Λ ∧ Λ 1 = 1 ∧
      ∀ φ : C(DiskFamily, ℝ), Λ (dyadicOperator φ) = dyadicRadius * Λ φ := by
  obtain ⟨μ, hμ⟩ := exists_exact_eigenprobability dyadicOperator
    dyadicOperator_monotone dyadicOperator_pow_norm_ge_one
  exact ⟨probabilityFunctional μ, probabilityFunctional_monotone μ,
    probabilityFunctional_one μ, hμ⟩

lemma eigenfunctional_horizontal_period (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ)
    (ρ : ℝ) (hρ : 1 < ρ)
    (hΛ : ∀ φ : C(DiskFamily, ℝ), Λ (dyadicOperator φ) = ρ * Λ φ) :
    ∀ φ : C(DiskFamily, ℝ), Λ (affineOperator (horizontalPoint 2) φ) = Λ φ := by
  intro φ
  let d := |Λ (affineOperator (horizontalPoint 2) φ) - Λ φ|
  have hp (n : ℕ) : ρ ^ n * d ≤ ‖Λ‖ * (128 * ‖φ‖) := by
    have he : ρ ^ n * (Λ (affineOperator (horizontalPoint 2) φ) - Λ φ) =
        Λ ((dyadicOperator ^ n * affineOperator (horizontalPoint 2) - dyadicOperator ^ n) φ) := by
      rw [sub_apply, mul_apply_eq_comp, map_sub,
        eigenfunctional_power dyadicOperator Λ ρ hΛ n,
        eigenfunctional_power dyadicOperator Λ ρ hΛ n]
      ring
    calc
      ρ ^ n * d = |ρ ^ n * (Λ (affineOperator (horizontalPoint 2) φ) - Λ φ)| := by
        rw [abs_mul, abs_of_pos (pow_pos (lt_trans zero_lt_one hρ) n)]
      _ = ‖Λ ((dyadicOperator ^ n * affineOperator (horizontalPoint 2) - dyadicOperator ^ n) φ)‖ :=
        congrArg abs he
      _ ≤ ‖Λ‖ * ‖(dyadicOperator ^ n * affineOperator (horizontalPoint 2) - dyadicOperator ^ n) φ‖ := Λ.le_opNorm _
      _ ≤ ‖Λ‖ * (128 * ‖φ‖) := mul_le_mul_of_nonneg_left
        (((dyadicOperator ^ n * affineOperator (horizontalPoint 2) - dyadicOperator ^ n).le_opNorm φ).trans
          (mul_le_mul_of_nonneg_right (dyadic_shift_norm_le n) (norm_nonneg φ))) (norm_nonneg Λ)
  have hb (n : ℕ) : d ≤ (ρ ^ n)⁻¹ * (‖Λ‖ * (128 * ‖φ‖)) := by
    apply (le_inv_mul_iff₀ (pow_pos (lt_trans zero_lt_one hρ) n)).mpr
    exact hp n
  have ht := (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hρ)).mul_const
    (‖Λ‖ * (128 * ‖φ‖))
  have hd : d ≤ 0 := by simpa only [zero_mul] using ge_of_tendsto' ht hb
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hd)

end
end StrictInverseFirstPower

open Set Filter Function MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma affineProduct_horizontal (x s : ℝ) :
    affineProduct (horizontalPoint x) (horizontalPoint s) = horizontalPoint (x + s) := by
  simp [horizontalPoint, affineProduct_xyPoint]

lemma affineProduct_horizontal_xy (x s t : ℝ) (ht : 0 < t) :
    affineProduct (horizontalPoint x) (xyPoint s t ht) = xyPoint (x + s) t ht := by
  simp [horizontalPoint, affineProduct_xyPoint]

lemma continuous_functional_affine (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (φ : C(DiskFamily, ℝ)) :
    Continuous (fun z => Λ (affineOperator z φ)) :=
  Λ.continuous.comp (continuous_affineOperator_strong φ)

lemma functional_horizontal_periodic (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ)
    (hΛ : ∀ φ, Λ (affineOperator (horizontalPoint 2) φ) = Λ φ)
    (y : ℝ) (hy : 0 < y) (φ : C(DiskFamily, ℝ)) :
    Periodic (fun x => Λ (affineOperator (xyPoint x y hy) φ)) 2 := by
  intro x
  change Λ (affineOperator (xyPoint (x + 2) y hy) φ) = Λ (affineOperator (xyPoint x y hy) φ)
  have he : xyPoint (x + 2) y hy = affineProduct (horizontalPoint 2) (xyPoint x y hy) := by
    rw [affineProduct_horizontal_xy, add_comm]
  rw [he, ← affineOperator_mul, mul_apply_eq_comp, hΛ]

lemma horizontalAverage_invariant (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ)
    (hΛ : ∀ φ, Λ (affineOperator (horizontalPoint 2) φ) = Λ φ)
    (s : ℝ) (φ : C(DiskFamily, ℝ)) :
    horizontalAverage Λ (affineOperator (horizontalPoint s) φ) = horizontalAverage Λ φ := by
  simp only [horizontalAverage_apply]
  have he (x : ℝ) : affineOperator (horizontalPoint x) (affineOperator (horizontalPoint s) φ) =
      affineOperator (horizontalPoint (x + s)) φ := by
    rw [← mul_apply_eq_comp, affineOperator_mul, affineProduct_horizontal]
  simp_rw [he]
  rw [intervalIntegral.integral_comp_add_right (fun x => Λ (affineOperator (horizontalPoint x) φ)) s]
  have hp : Periodic (fun x => Λ (affineOperator (horizontalPoint x) φ)) 2 :=
    functional_horizontal_periodic Λ hΛ 1 zero_lt_one φ
  rw [show 0 + s = s by ring, show (2 : ℝ) + s = s + 2 by ring]
  rw [hp.intervalIntegral_add_eq s 0]
  simp only [zero_add]

end
end StrictInverseFirstPower

open Set Filter Function MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma dyadicLeft_eq_horizontal_scale :
    dyadicLeft = affineProduct (horizontalPoint (-1 / 2)) halfScalePoint := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, dyadicLeft, horizontalPoint, halfScalePoint, xyPoint]
  ring

lemma dyadicRight_eq_horizontal_scale :
    dyadicRight = affineProduct (horizontalPoint (1 / 2)) halfScalePoint := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, dyadicRight, horizontalPoint, halfScalePoint, xyPoint]
  ring

lemma horizontal_dyadicLeft (x : ℝ) :
    affineProduct (horizontalPoint x) dyadicLeft =
      affineProduct dyadicLeft (horizontalPoint (2 * x)) := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, dyadicLeft, horizontalPoint, xyPoint]
  ring

lemma horizontal_dyadicRight (x : ℝ) :
    affineProduct (horizontalPoint x) dyadicRight =
      affineProduct dyadicRight (horizontalPoint (2 * x)) := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, dyadicRight, horizontalPoint, xyPoint]
  ring

lemma affineOperator_horizontal_dyadic (x : ℝ) :
    affineOperator (horizontalPoint x) * dyadicOperator =
      dyadicOperator * affineOperator (horizontalPoint (2 * x)) := by
  rw [dyadicOperator, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
    affineOperator_mul, affineOperator_mul, affineOperator_mul, affineOperator_mul,
    horizontal_dyadicLeft, horizontal_dyadicRight]

lemma periodic_integral_double {g : ℝ → ℝ} (hg : Continuous g) (hp : Periodic g 2) :
    (∫ x in (0 : ℝ)..2, g (2 * x)) = ∫ x in (0 : ℝ)..2, g x := by
  rw [intervalIntegral.integral_comp_mul_left g (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num only [mul_zero, show (2 : ℝ) * 2 = 4 by norm_num, smul_eq_mul]
  have he : (∫ x in (2 : ℝ)..4, g x) = ∫ x in (0 : ℝ)..2, g x := by
    convert hp.intervalIntegral_add_eq 2 0 using 1 <;> norm_num
  have hh := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable (0 : ℝ) 2) (hg.intervalIntegrable (2 : ℝ) 4)
  rw [← hh, he]
  ring

lemma horizontalAverage_eigen (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (ρ : ℝ)
    (hperiod : ∀ φ, Λ (affineOperator (horizontalPoint 2) φ) = Λ φ)
    (heigen : ∀ φ, Λ (dyadicOperator φ) = ρ * Λ φ)
    (φ : C(DiskFamily, ℝ)) :
    horizontalAverage Λ (dyadicOperator φ) = ρ * horizontalAverage Λ φ := by
  have he (x : ℝ) : Λ (affineOperator (horizontalPoint x) (dyadicOperator φ)) =
      ρ * Λ (affineOperator (horizontalPoint (2 * x)) φ) := by
    rw [← mul_apply_eq_comp, affineOperator_horizontal_dyadic, mul_apply_eq_comp, heigen]
  simp only [horizontalAverage_apply]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  have hp : Periodic (fun x => Λ (affineOperator (horizontalPoint x) φ)) 2 :=
    functional_horizontal_periodic Λ hperiod 1 zero_lt_one φ
  have hg : Continuous (fun x => Λ (affineOperator (horizontalPoint x) φ)) :=
    (continuous_functional_affine Λ φ).comp continuous_horizontalPoint
  rw [periodic_integral_double hg hp]
  ring

lemma horizontally_invariant_dyadic (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ)
    (hΛ : ∀ x φ, Λ (affineOperator (horizontalPoint x) φ) = Λ φ)
    (φ : C(DiskFamily, ℝ)) : Λ (dyadicOperator φ) = Λ (affineOperator halfScalePoint φ) := by
  change Λ ((1 / 2 : ℝ) • (affineOperator dyadicLeft φ + affineOperator dyadicRight φ)) = _
  rw [map_smul, map_add, dyadicLeft_eq_horizontal_scale, dyadicRight_eq_horizontal_scale,
    ← affineOperator_mul, ← affineOperator_mul, mul_apply_eq_comp, mul_apply_eq_comp, hΛ, hΛ]
  simp only [smul_eq_mul]
  ring

lemma horizontalAverage_halfScale (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (ρ : ℝ)
    (hperiod : ∀ φ, Λ (affineOperator (horizontalPoint 2) φ) = Λ φ)
    (heigen : ∀ φ, Λ (dyadicOperator φ) = ρ * Λ φ)
    (φ : C(DiskFamily, ℝ)) :
    horizontalAverage Λ (affineOperator halfScalePoint φ) = ρ * horizontalAverage Λ φ := by
  rw [← horizontally_invariant_dyadic (horizontalAverage Λ)
    (horizontalAverage_invariant Λ hperiod)]
  exact horizontalAverage_eigen Λ ρ hperiod heigen φ

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.AffineAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology

open Set Filter Function MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma affineProduct_expScale (s t : ℝ) :
    affineProduct (expScalePoint s) (expScalePoint t) = expScalePoint (s + t) := by
  simp [expScalePoint, affineProduct_xyPoint, Real.exp_add]

lemma halfScale_expScale (t : ℝ) :
    affineProduct halfScalePoint (expScalePoint (t + Real.log 2)) = expScalePoint t := by
  have he : Real.exp (t + Real.log 2) = Real.exp t * 2 := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  simp [halfScalePoint, expScalePoint, affineProduct_xyPoint, he]
  congr 1
  ring

lemma expScale_horizontal (t s : ℝ) :
    affineProduct (expScalePoint t) (horizontalPoint s) =
      affineProduct (horizontalPoint (Real.exp t * s)) (expScalePoint t) := by
  simp [expScalePoint, horizontalPoint, affineProduct_xyPoint]

lemma weighted_scale_periodic (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (β ρ : ℝ)
    (hpower : Real.exp (β * Real.log 2) = ρ)
    (hscale : ∀ φ, Λ (affineOperator halfScalePoint φ) = ρ * Λ φ)
    (φ : C(DiskFamily, ℝ)) :
    Periodic (fun t => Real.exp (β * t) * Λ (affineOperator (expScalePoint t) φ)) (Real.log 2) := by
  intro t
  have hs := hscale (affineOperator (expScalePoint (t + Real.log 2)) φ)
  rw [← mul_apply_eq_comp, affineOperator_mul, halfScale_expScale] at hs
  change Real.exp (β * (t + Real.log 2)) * _ = _
  rw [mul_add, Real.exp_add, hpower, mul_assoc, ← hs]

lemma scaleAverage_horizontal (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (β s : ℝ)
    (hΛ : ∀ x φ, Λ (affineOperator (horizontalPoint x) φ) = Λ φ)
    (φ : C(DiskFamily, ℝ)) :
    scaleAverage Λ β (affineOperator (horizontalPoint s) φ) = scaleAverage Λ β φ := by
  simp only [scaleAverage_apply]
  congr 1
  ext t
  rw [← mul_apply_eq_comp, affineOperator_mul, expScale_horizontal, ← affineOperator_mul,
    mul_apply_eq_comp, hΛ]

lemma scaleAverage_scale (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (β ρ s : ℝ)
    (hpower : Real.exp (β * Real.log 2) = ρ)
    (hscale : ∀ φ, Λ (affineOperator halfScalePoint φ) = ρ * Λ φ)
    (φ : C(DiskFamily, ℝ)) :
    scaleAverage Λ β (affineOperator (expScalePoint s) φ) =
      Real.exp (-β * s) * scaleAverage Λ β φ := by
  simp only [scaleAverage_apply]
  have he (t : ℝ) : Real.exp (β * t) *
      Λ (affineOperator (expScalePoint t) (affineOperator (expScalePoint s) φ)) =
      Real.exp (-β * s) * (Real.exp (β * (t + s)) *
        Λ (affineOperator (expScalePoint (t + s)) φ)) := by
    rw [← mul_apply_eq_comp, affineOperator_mul, affineProduct_expScale,
      ← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  have hp := weighted_scale_periodic Λ β ρ hpower hscale φ
  have hi := intervalIntegral.integral_comp_add_right
    (fun t => Real.exp (β * t) * Λ (affineOperator (expScalePoint t) φ)) s
    (a := 0) (b := Real.log 2)
  rw [hi, zero_add, add_comm (Real.log 2) s, hp.intervalIntegral_add_eq s 0, zero_add]

lemma scaleAverage_affine (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (β ρ : ℝ)
    (hpower : Real.exp (β * Real.log 2) = ρ)
    (hscale : ∀ φ, Λ (affineOperator halfScalePoint φ) = ρ * Λ φ)
    (hΛ : ∀ x φ, Λ (affineOperator (horizontalPoint x) φ) = Λ φ)
    (z : UpperHalfPlane) (φ : C(DiskFamily, ℝ)) :
    scaleAverage Λ β (affineOperator z φ) = z.im ^ (-β) * scaleAverage Λ β φ := by
  have he : z = affineProduct (horizontalPoint z.re) (expScalePoint (Real.log z.im)) := by
    apply UpperHalfPlane.ext
    simp [coe_affineProduct, affineAt, horizontalPoint, expScalePoint, xyPoint,
      Real.exp_log z.im_pos]
    exact (Complex.re_add_im (z : ℂ)).symm
  conv_lhs => rw [he]
  rw [← affineOperator_mul, mul_apply_eq_comp,
    scaleAverage_horizontal Λ β z.re hΛ, scaleAverage_scale Λ β ρ _ hpower hscale]
  congr 1
  rw [Real.rpow_def_of_pos z.im_pos]
  congr 1
  ring

end
end StrictInverseFirstPower

open Set Filter Function MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma positiveFunctional_strict (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (hΛ : Monotone Λ)
    (h1 : 0 < Λ 1) (φ : C(DiskFamily, ℝ)) (hφ : ∀ f, 0 < φ f) : 0 < Λ φ := by
  obtain ⟨f, _, hf⟩ := isCompact_univ.exists_isMinOn (univ_nonempty : (univ : Set DiskFamily).Nonempty)
    φ.continuous.continuousOn
  have hle : φ f • (1 : C(DiskFamily, ℝ)) ≤ φ := by
    intro g
    change φ f * 1 ≤ φ g
    rw [mul_one]
    exact hf (mem_univ g)
  have hh := hΛ hle
  rw [map_smul, smul_eq_mul] at hh
  exact lt_of_lt_of_le (mul_pos (hφ f) h1) hh

lemma positiveFunctional_affine_one (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (hΛ : Monotone Λ)
    (h1 : 0 < Λ 1) (z : UpperHalfPlane) : 0 < Λ (affineOperator z 1) := by
  apply positiveFunctional_strict Λ hΛ h1
  intro f
  simpa using norm_pos_iff.mpr (halfPlaneQ_ne_zero f z)

lemma horizontalAverage_monotone (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (hΛ : Monotone Λ) :
    Monotone (horizontalAverage Λ) := by
  intro φ ψ h
  simp only [horizontalAverage_apply]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply intervalIntegral.integral_mono (by norm_num)
    (((continuous_functional_affine Λ φ).comp continuous_horizontalPoint).intervalIntegrable _ _)
    (((continuous_functional_affine Λ ψ).comp continuous_horizontalPoint).intervalIntegrable _ _)
  intro t
  exact hΛ (affineOperator_monotone _ h)

lemma horizontalAverage_one_pos (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (hΛ : Monotone Λ)
    (h1 : 0 < Λ 1) : 0 < horizontalAverage Λ 1 := by
  rw [horizontalAverage_apply]
  apply mul_pos (by norm_num)
  apply intervalIntegral.intervalIntegral_pos_of_pos
    (((continuous_functional_affine Λ 1).comp continuous_horizontalPoint).intervalIntegrable _ _)
    (fun t => positiveFunctional_affine_one Λ hΛ h1 _) (by norm_num)

lemma scaleAverage_monotone (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (hΛ : Monotone Λ) (β : ℝ) :
    Monotone (scaleAverage Λ β) := by
  intro φ ψ h
  simp only [scaleAverage_apply]
  have hc (φ : C(DiskFamily, ℝ)) : Continuous
      (fun t => Real.exp (β * t) * Λ (affineOperator (expScalePoint t) φ)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((continuous_functional_affine Λ φ).comp continuous_expScalePoint)
  apply intervalIntegral.integral_mono (Real.log_nonneg (by norm_num))
    ((hc φ).intervalIntegrable _ _) ((hc ψ).intervalIntegrable _ _)
  intro t
  exact mul_le_mul_of_nonneg_left (hΛ (affineOperator_monotone _ h)) (Real.exp_pos _).le

lemma scaleAverage_one_pos (Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ) (hΛ : Monotone Λ)
    (h1 : 0 < Λ 1) (β : ℝ) : 0 < scaleAverage Λ β 1 := by
  rw [scaleAverage_apply]
  have hc : Continuous (fun t => Real.exp (β * t) * Λ (affineOperator (expScalePoint t) 1)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((continuous_functional_affine Λ 1).comp continuous_expScalePoint)
  exact intervalIntegral.intervalIntegral_pos_of_pos (hc.intervalIntegrable _ _)
    (fun t => mul_pos (Real.exp_pos _) (positiveFunctional_affine_one Λ hΛ h1 _))
    (Real.log_pos (by norm_num))

lemma dyadicExponent_power : Real.exp (dyadicExponent * Real.log 2) = dyadicRadius := by
  unfold dyadicExponent dyadicRadius
  rw [div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]

lemma dyadicExponent_pos_iff : 0 < dyadicExponent ↔ 1 < dyadicRadius := by
  rw [dyadicExponent, dyadicRadius, Real.one_lt_exp_iff, div_pos_iff_of_pos_right
    (Real.log_pos (by norm_num))]

theorem exists_exact_affine_functional (hβ : 0 < dyadicExponent) :
    ∃ Λ : C(DiskFamily, ℝ) →L[ℝ] ℝ, Monotone Λ ∧ Λ 1 = 1 ∧
      ∀ (z : UpperHalfPlane) (φ : C(DiskFamily, ℝ)),
        Λ (affineOperator z φ) = z.im ^ (-dyadicExponent) * Λ φ := by
  obtain ⟨Λ, hΛ, h1, heigen⟩ := exists_dyadic_eigenfunctional
  have hper := eigenfunctional_horizontal_period Λ dyadicRadius
    (dyadicExponent_pos_iff.mp hβ) heigen
  let Λh := horizontalAverage Λ
  have hΛh : Monotone Λh := horizontalAverage_monotone Λ hΛ
  have hh1 : 0 < Λh 1 := horizontalAverage_one_pos Λ hΛ (by rw [h1]; norm_num)
  let ν := scaleAverage Λh dyadicExponent
  have hν : Monotone ν := scaleAverage_monotone Λh hΛh _
  have hν1 : 0 < ν 1 := scaleAverage_one_pos Λh hΛh hh1 _
  refine ⟨(ν 1)⁻¹ • ν, ?_, ?_, ?_⟩
  · intro φ ψ h
    exact mul_le_mul_of_nonneg_left (hν h) (inv_nonneg.mpr hν1.le)
  · change (ν 1)⁻¹ * ν 1 = 1
    exact inv_mul_cancel₀ hν1.ne'
  · intro z φ
    change (ν 1)⁻¹ * ν (affineOperator z φ) = z.im ^ (-dyadicExponent) * ((ν 1)⁻¹ * ν φ)
    rw [show ν (affineOperator z φ) = z.im ^ (-dyadicExponent) * ν φ from
      scaleAverage_affine Λh dyadicExponent dyadicRadius dyadicExponent_power
        (horizontalAverage_halfScale Λ dyadicRadius hper heigen)
        (horizontalAverage_invariant Λ hper) z φ]
    ring

theorem exists_exact_affine_probability_continuous (hβ : 0 < dyadicExponent) :
    ∃ μ : ProbabilityMeasure DiskFamily, ∀ (z : UpperHalfPlane) (φ : C(DiskFamily, ℝ)),
      (∫ f, ‖halfPlaneQ f z‖ * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
        z.im ^ (-dyadicExponent) * ∫ f, φ f ∂(μ : Measure DiskFamily) := by
  obtain ⟨Λ, hΛ, h1, hlaw⟩ := exists_exact_affine_functional hβ
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_of_positiveFunctional Λ hΛ h1
  refine ⟨μ, fun z φ => ?_⟩
  change (∫ f, affineOperator z φ f ∂(μ : Measure DiskFamily)) = _
  rw [hμ, hμ, hlaw]

end
end StrictInverseFirstPower

open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal

namespace StrictInverseFirstPower
noncomputable section

lemma measurable_rebase_fixed (z : UpperHalfPlane) : Measurable (fun f => rebase f z) :=
  (continuous_rebase.comp (continuous_id.prodMk continuous_const)).measurable

lemma measurable_Qnorm_fixed (z : UpperHalfPlane) : Measurable (fun f => ‖halfPlaneQ f z‖₊) :=
  ((continuous_halfPlaneQ.comp (continuous_id.prodMk continuous_const)).nnnorm).measurable

lemma weightedRebaseMeasure_integral (μ : Measure DiskFamily) (z : UpperHalfPlane)
    (φ : C(DiskFamily, ℝ)) :
    (∫ f, φ f ∂weightedRebaseMeasure μ z) = ∫ f, affineOperator z φ f ∂μ := by
  rw [weightedRebaseMeasure, integral_map (measurable_rebase_fixed z).aemeasurable
    φ.continuous.aestronglyMeasurable, integral_withDensity_eq_integral_smul (measurable_Qnorm_fixed z)]
  rfl

lemma weightedRebaseMeasure_lintegral (μ : Measure DiskFamily) (z : UpperHalfPlane)
    (φ : DiskFamily → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ f, φ f ∂weightedRebaseMeasure μ z) =
      ∫⁻ f, (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * φ (rebase f z) ∂μ := by
  rw [weightedRebaseMeasure, lintegral_map hφ (measurable_rebase_fixed z)]
  exact lintegral_withDensity_eq_lintegral_mul _ (measurable_Qnorm_fixed z).coe_nnreal_ennreal
    (hφ.comp (measurable_rebase_fixed z))

lemma weightedRebaseMeasure_eq_smul (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : ∀ (z : UpperHalfPlane) (φ : C(DiskFamily, ℝ)),
      (∫ f, affineOperator z φ f ∂(μ : Measure DiskFamily)) =
        z.im ^ (-β) * ∫ f, φ f ∂(μ : Measure DiskFamily)) (z : UpperHalfPlane) :
    weightedRebaseMeasure (μ : Measure DiskFamily) z =
      ENNReal.ofReal (z.im ^ (-β)) • (μ : Measure DiskFamily) := by
  have : IsFiniteMeasure (ENNReal.ofReal (z.im ^ (-β)) • (μ : Measure DiskFamily)) :=
    ⟨by simp [Measure.smul_apply]⟩
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  change (∫ f, φ.toContinuousMap f ∂weightedRebaseMeasure (μ : Measure DiskFamily) z) =
    ∫ f, φ.toContinuousMap f ∂ENNReal.ofReal (z.im ^ (-β)) • (μ : Measure DiskFamily)
  rw [weightedRebaseMeasure_integral _ _ φ.toContinuousMap, hlaw]
  rw [integral_smul_measure, ENNReal.toReal_ofReal (Real.rpow_nonneg z.im_pos.le _)]
  rfl

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.FamilyDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

lemma continuous_holomorphicFamily_deriv {X : Type*} [TopologicalSpace X] {U : Set ℂ}
    (hU : IsOpen U) (F : X → ℂ → ℂ)
    (hF : Continuous (fun p : X × U => F p.1 p.2))
    (hd : ∀ x, DifferentiableOn ℂ (F x) U) :
    Continuous (fun p : X × U => deriv (F p.1) p.2) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let g : X → C(U, ℂ) := fun x => ⟨fun z => F x z,
    hF.comp (continuous_const.prodMk continuous_id)⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g hF
  let g' : X → C(U, ℂ) := fun x => ⟨fun z => deriv (F x) z,
    ((hd x).deriv hU).continuousOn.comp_continuous continuous_subtype_val (fun z => z.property)⟩
  have hg' : Continuous g' := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, ContinuousMap.tendsto_iff_tendstoLocallyUniformly]
    have hh : TendstoLocallyUniformlyOn F (F x) (𝓝 x) U := by
      rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
      exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp (hg.tendsto x)
    have hh' := hh.deriv (Eventually.of_forall hd) hU
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe] at hh'
    exact hh'
  exact hg'.comp continuous_fst |>.eval continuous_snd

lemma complex_path_norm_hasDerivAt {g : ℝ → ℂ} {b : ℂ} {x : ℝ}
    (hg : HasDerivAt g b x) (hne : g x ≠ 0) :
    HasDerivAt (fun t => ‖g t‖) ((conj (g x) * b).re / ‖g x‖) x := by
  have hn := hg.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
  simp only [Real.sqrt_sq (norm_nonneg _)] at hn
  have hi : inner ℝ (g x) b = (conj (g x) * b).re := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
    change (b * conj (g x)).re = _
    rw [mul_comm]
  rw [hi] at hn
  convert hn using 1
  ring

lemma complex_path_normFirst_hasDerivAt {g g' : ℝ → ℂ} {b c : ℂ} {x : ℝ}
    (hg : HasDerivAt g b x) (hg' : HasDerivAt g' c x) (hb : g' x = b)
    (hne : g x ≠ 0) :
    HasDerivAt (fun t => (conj (g t) * g' t).re / ‖g t‖)
      (((conj b * b + conj (g x) * c).re) / ‖g x‖ -
        ((conj (g x) * b).re) ^ 2 / ‖g x‖ ^ 3) x := by
  have hconj : HasDerivAt (fun t => conj (g t)) (conj b) x :=
    Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x hg
  have htop := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hconj.mul hg')
  have hnorm := complex_path_norm_hasDerivAt hg hne
  have he := htop.div hnorm (norm_ne_zero_iff.mpr hne)
  have he' : HasDerivAt (fun t => (conj (g t) * g' t).re / ‖g t‖)
      (((conj b * b + conj (g x) * c).re * ‖g x‖ -
        (conj (g x) * b).re * ((conj (g x) * b).re / ‖g x‖)) / ‖g x‖ ^ 2) x := by
    simpa only [Function.comp_apply, Complex.reCLM_apply, Pi.mul_apply, Pi.div_apply, hb] using! he
  convert he' using 1
  field_simp

lemma complex_normSecond_at_one (b c : ℂ) :
    ((conj b * b + conj (1 : ℂ) * c).re) / ‖(1 : ℂ)‖ -
        ((conj (1 : ℂ) * b).re) ^ 2 / ‖(1 : ℂ)‖ ^ 3 = c.re + b.im ^ 2 := by
  simp only [map_one, one_mul, norm_one, div_one, one_pow, add_re, mul_re, conj_re, conj_im]
  ring

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma compactFamily_hasDerivAt_integral {X E : Type*} [TopologicalSpace X]
    [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) [IsFiniteMeasure μ] {F G : ℝ → X → E}
    {s : Set ℝ} {t₀ : ℝ} (hs : IsCompact s) (ht : s ∈ 𝓝 t₀)
    (hF : Continuous (fun p : X × s => F p.2 p.1))
    (hG : Continuous (fun p : X × s => G p.2 p.1))
    (hd : ∀ x t, t ∈ s → HasDerivAt (fun t => F t x) (G t x) t) :
    HasDerivAt (fun t => ∫ x, F t x ∂μ) (∫ x, G t₀ x ∂μ) t₀ := by
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  have ht₀ : t₀ ∈ s := mem_of_mem_nhds ht
  have hcF (t : ℝ) (hts : t ∈ s) : Continuous (F t) :=
    hF.comp (continuous_id.prodMk (continuous_const (y := (⟨t, hts⟩ : s))))
  have hcG (t : ℝ) (hts : t ∈ s) : Continuous (G t) :=
    hG.comp (continuous_id.prodMk (continuous_const (y := (⟨t, hts⟩ : s))))
  obtain ⟨C, hC⟩ := isCompact_range hG |>.isBounded.exists_norm_le
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le ht
    (F := F) (F' := G) (bound := fun _ => C) ?_ ?_ ?_ ?_ (integrable_const C) ?_).2
  · filter_upwards [ht] with t hts using (hcF t hts).aestronglyMeasurable
  · exact (hcF t₀ ht₀).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (hcG t₀ ht₀).aestronglyMeasurable
  · exact Eventually.of_forall fun x t hts => hC _ ⟨(x, ⟨t, hts⟩), rfl⟩
  · exact Eventually.of_forall hd

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.ReciprocalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

lemma continuous_reciprocalFunction :
    Continuous (fun p : DiskFamily × HalfPlaneSet => reciprocalFunction p.1 p.2) := by
  have hc : Continuous (fun z : HalfPlaneSet => (⟨z, z.property⟩ : UpperHalfPlane)) :=
    continuous_subtype_val.upperHalfPlaneMk (fun z => z.property)
  change Continuous (fun p : DiskFamily × HalfPlaneSet => halfPlaneQ p.1 ⟨p.2, p.2.property⟩)
  have hmap : Continuous (fun p : DiskFamily × HalfPlaneSet =>
      (p.1, (⟨p.2, p.2.property⟩ : UpperHalfPlane))) :=
    continuous_fst.prodMk (hc.comp continuous_snd)
  have hh := continuous_halfPlaneQ.comp hmap
  exact hh

lemma continuous_reciprocalFunction_deriv :
    Continuous (fun p : DiskFamily × HalfPlaneSet => deriv (reciprocalFunction p.1) p.2) :=
  continuous_holomorphicFamily_deriv isOpen_halfPlane _ continuous_reciprocalFunction
    reciprocalFunction_differentiableOn

lemma continuous_reciprocalFunction_deriv₂ :
    Continuous (fun p : DiskFamily × HalfPlaneSet => deriv (deriv (reciprocalFunction p.1)) p.2) :=
  continuous_holomorphicFamily_deriv isOpen_halfPlane _ continuous_reciprocalFunction_deriv
    (fun f => (reciprocalFunction_differentiableOn f).deriv isOpen_halfPlane)

lemma sourcePath_mem (v : ℂ) (hv : |v.im| ≤ 1) {t : ℝ} (ht : t ∈ MomentInterval) :
    0 < (sourcePath v t).im := by
  have ht' : |t| ≤ 1 / 2 := abs_le.mpr ht
  have hm : |t * v.im| ≤ 1 / 2 := by
    rw [abs_mul]
    calc |t| * |v.im| ≤ (1 / 2) * 1 := mul_le_mul ht' hv (abs_nonneg _) (by norm_num)
         _ = 1 / 2 := by ring
  have hh := (abs_le.mp hm).1
  simp only [sourcePath, add_im, mul_im, I_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  linarith

lemma sourcePath_hasDerivAt (v : ℂ) (t : ℝ) : HasDerivAt (sourcePath v) v t := by
  have hf : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using! Complex.ofRealCLM.hasDerivAt (x := t)
  change HasDerivAt (fun s : ℝ => I + (s : ℂ) * v) v t
  simpa only [one_mul] using (hf.mul_const v).const_add I

lemma continuous_sourcePath (v : ℂ) : Continuous (sourcePath v) := by
  unfold sourcePath
  fun_prop

lemma reciprocalPath_hasDerivAt (f : DiskFamily) (v : ℂ) {t : ℝ}
    (ht : 0 < (sourcePath v t).im) :
    HasDerivAt (fun t => reciprocalFunction f (sourcePath v t))
      (deriv (reciprocalFunction f) (sourcePath v t) * v) t := by
  have h := ((reciprocalFunction_differentiableOn f).differentiableAt
    (isOpen_halfPlane.mem_nhds ht)).hasDerivAt.scomp t (sourcePath_hasDerivAt v t)
  simpa only [smul_eq_mul, mul_comm] using! h

lemma reciprocalPath_deriv_hasDerivAt (f : DiskFamily) (v : ℂ) {t : ℝ}
    (ht : 0 < (sourcePath v t).im) :
    HasDerivAt (fun t => deriv (reciprocalFunction f) (sourcePath v t) * v)
      (deriv (deriv (reciprocalFunction f)) (sourcePath v t) * v ^ 2) t := by
  have h := (((reciprocalFunction_differentiableOn f).deriv isOpen_halfPlane).differentiableAt
    (isOpen_halfPlane.mem_nhds ht)).hasDerivAt.scomp t (sourcePath_hasDerivAt v t)
  have hh : HasDerivAt (fun t => deriv (reciprocalFunction f) (sourcePath v t) * v)
      ((v * deriv (deriv (reciprocalFunction f)) (sourcePath v t)) * v) t := by
    simpa only [Function.comp_def, smul_eq_mul] using! h.mul_const v
  convert hh using 1
  ring

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

lemma normPath_hasDerivAt (f : DiskFamily) (v : ℂ) {t : ℝ}
    (ht : 0 < (sourcePath v t).im) :
    HasDerivAt (fun t => ‖reciprocalFunction f (sourcePath v t)‖) (normPathFirst f v t) t :=
  complex_path_norm_hasDerivAt (reciprocalPath_hasDerivAt f v ht)
    (reciprocalFunction_ne_zero f ht)

lemma normPathFirst_hasDerivAt (f : DiskFamily) (v : ℂ) {t : ℝ}
    (ht : 0 < (sourcePath v t).im) :
    HasDerivAt (normPathFirst f v) (normPathSecond f v t) t :=
  complex_path_normFirst_hasDerivAt (reciprocalPath_hasDerivAt f v ht)
    (reciprocalPath_deriv_hasDerivAt f v ht) rfl (reciprocalFunction_ne_zero f ht)

lemma continuous_normPath_on_interval (v : ℂ) (hv : |v.im| ≤ 1) :
    Continuous (fun p : DiskFamily × MomentInterval =>
      ‖reciprocalFunction p.1 (sourcePath v p.2)‖) ∧
    Continuous (fun p : DiskFamily × MomentInterval => normPathFirst p.1 v p.2) ∧
    Continuous (fun p : DiskFamily × MomentInterval => normPathSecond p.1 v p.2) := by
  let m : DiskFamily × MomentInterval → DiskFamily × HalfPlaneSet :=
    fun p => (p.1, ⟨sourcePath v p.2, sourcePath_mem v hv p.2.property⟩)
  have hm : Continuous m := continuous_fst.prodMk
    (((continuous_sourcePath v).comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _)
  have h₀ := continuous_reciprocalFunction.comp hm
  have h₁ := (continuous_reciprocalFunction_deriv.comp hm).mul_const v
  have h₂ := (continuous_reciprocalFunction_deriv₂.comp hm).mul_const (v ^ 2)
  have hn : ∀ p : DiskFamily × MomentInterval,
      ‖reciprocalFunction p.1 (sourcePath v p.2)‖ ≠ 0 :=
    fun p => norm_ne_zero_iff.mpr (reciprocalFunction_ne_zero _ (sourcePath_mem v hv p.2.property))
  refine ⟨h₀.norm, ?_, ?_⟩
  · exact (Complex.continuous_re.comp ((Complex.continuous_conj.comp h₀).mul h₁)).div h₀.norm hn
  · exact (Complex.continuous_re.comp (((Complex.continuous_conj.comp h₁).mul h₁).add ((Complex.continuous_conj.comp h₀).mul h₂))).div h₀.norm hn |>.sub
      (((Complex.continuous_re.comp ((Complex.continuous_conj.comp h₀).mul h₁)).pow 2).div (h₀.norm.pow 3) (fun p => pow_ne_zero _ (hn p)))

@[simp] lemma normPathSecond_zero (f : DiskFamily) (v : ℂ) :
    normPathSecond f v 0 = (deriv (deriv (reciprocalFunction f)) I * v ^ 2).re +
      (deriv (reciprocalFunction f) I * v).im ^ 2 := by
  unfold normPathSecond
  rw [sourcePath_zero, reciprocalFunction_I]
  exact complex_normSecond_at_one _ _

lemma normPathSecond_add_axes (f : DiskFamily) :
    normPathSecond f 1 0 + normPathSecond f I 0 = ‖deriv (reciprocalFunction f) I‖ ^ 2 := by
  rw [normPathSecond_zero, normPathSecond_zero, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, mul_im, Complex.I_sq]
  ring

lemma normPath_integral_hasDerivAt (μ : Measure DiskFamily) [IsFiniteMeasure μ]
    (v : ℂ) (hv : |v.im| ≤ 1) {t : ℝ} (ht : t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    HasDerivAt (fun t => ∫ f, ‖reciprocalFunction f (sourcePath v t)‖ ∂μ)
      (∫ f, normPathFirst f v t ∂μ) t := by
  have hc := continuous_normPath_on_interval v hv
  exact compactFamily_hasDerivAt_integral μ isCompact_Icc (Icc_mem_nhds ht.1 ht.2) hc.1 hc.2.1
    (fun f t htt => normPath_hasDerivAt f v (sourcePath_mem v hv htt))

lemma normPathFirst_integral_hasDerivAt (μ : Measure DiskFamily) [IsFiniteMeasure μ]
    (v : ℂ) (hv : |v.im| ≤ 1) {t : ℝ} (ht : t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    HasDerivAt (fun t => ∫ f, normPathFirst f v t ∂μ)
      (∫ f, normPathSecond f v t ∂μ) t := by
  have hc := continuous_normPath_on_interval v hv
  exact compactFamily_hasDerivAt_integral μ isCompact_Icc (Icc_mem_nhds ht.1 ht.2) hc.2.1 hc.2.2
    (fun f t htt => normPathFirst_hasDerivAt f v (sourcePath_mem v hv htt))

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

lemma affine_real_law_mean_law (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : ∀ (z : UpperHalfPlane) (φ : C(DiskFamily, ℝ)),
      (∫ f, affineOperator z φ f ∂(μ : Measure DiskFamily)) =
        z.im ^ (-β) * ∫ f, φ f ∂(μ : Measure DiskFamily)) :
    ReciprocalMeanLaw (μ : Measure DiskFamily) β := by
  intro z
  have h := hlaw z 1
  simpa [affineOperator_apply, reciprocalFunction, halfPlaneQ] using h

lemma normPath_integral_eq_rpow (μ : Measure DiskFamily) (β : ℝ)
    (hlaw : ReciprocalMeanLaw μ β) (v : ℂ) (hv : |v.im| ≤ 1)
    {t : ℝ} (ht : t ∈ MomentInterval) :
    (∫ f, ‖reciprocalFunction f (sourcePath v t)‖ ∂μ) = (1 + t * v.im) ^ (-β) := by
  have h := hlaw ⟨sourcePath v t, sourcePath_mem v hv ht⟩
  simpa [UpperHalfPlane.im, sourcePath] using h

lemma normPathFirst_integral_eq (μ : Measure DiskFamily) [IsFiniteMeasure μ] (β : ℝ)
    (hlaw : ReciprocalMeanLaw μ β) (v : ℂ) (hv : |v.im| ≤ 1)
    {t : ℝ} (ht : t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    (∫ f, normPathFirst f v t ∂μ) = v.im * (-β) * (1 + t * v.im) ^ (-β - 1) := by
  have hp : 0 < 1 + t * v.im := by
    simpa [sourcePath] using sourcePath_mem v hv (show t ∈ MomentInterval from ⟨ht.1.le, ht.2.le⟩)
  have hh := normPath_integral_hasDerivAt μ v hv ht
  have he : (fun t => (1 + t * v.im) ^ (-β)) =ᶠ[𝓝 t]
      (fun t => ∫ f, ‖reciprocalFunction f (sourcePath v t)‖ ∂μ) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact (normPath_integral_eq_rpow μ β hlaw v hv hs).symm
  have hp' := (((hasDerivAt_id t).mul_const v.im).const_add 1).rpow_const (p := -β) (Or.inl hp.ne')
  have hpow : HasDerivAt (fun s => (1 + s * v.im) ^ (-β))
      (v.im * (-β) * (1 + t * v.im) ^ (-β - 1)) t := by
    simpa only [one_mul, id_eq] using! hp'
  exact (hh.congr_of_eventuallyEq he).unique hpow

lemma normPathFirst_integral_zero (μ : Measure DiskFamily) [IsFiniteMeasure μ] (β : ℝ)
    (hlaw : ReciprocalMeanLaw μ β) (v : ℂ) (hv : |v.im| ≤ 1) :
    (∫ f, (deriv (reciprocalFunction f) I * v).re ∂μ) = -β * v.im := by
  simpa [mul_comm] using normPathFirst_integral_eq μ β hlaw v hv (t := 0) (by norm_num)

lemma normPathSecond_integral_zero (μ : Measure DiskFamily) [IsFiniteMeasure μ] (β : ℝ)
    (hlaw : ReciprocalMeanLaw μ β) (v : ℂ) (hv : |v.im| ≤ 1) :
    (∫ f, normPathSecond f v 0 ∂μ) = v.im ^ 2 * β * (β + 1) := by
  have hh := normPathFirst_integral_hasDerivAt μ v hv (t := 0) (by norm_num)
  have he : (fun t => v.im * (-β) * (1 + t * v.im) ^ (-β - 1)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => ∫ f, normPathFirst f v t ∂μ) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : -(1 / 2 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1 / 2)] with t ht
    exact (normPathFirst_integral_eq μ β hlaw v hv ht).symm
  have hp := (((hasDerivAt_id (0 : ℝ)).mul_const v.im).const_add 1).rpow_const
    (p := -β - 1) (Or.inl (by norm_num))
  have hp' := hp.const_mul (v.im * (-β))
  have hpow : HasDerivAt (fun t => v.im * (-β) * (1 + t * v.im) ^ (-β - 1))
      (v.im ^ 2 * β * (β + 1)) 0 := by
    convert! hp' using 1
    simp only [id_eq, one_mul, zero_mul, add_zero, Real.one_rpow, mul_one]
    ring
  exact (hh.congr_of_eventuallyEq he).unique hpow

lemma normPathSecond_integrable_zero (μ : Measure DiskFamily) [IsFiniteMeasure μ]
    (v : ℂ) (hv : |v.im| ≤ 1) : Integrable (fun f => normPathSecond f v 0) μ := by
  have hc := (continuous_normPath_on_interval v hv).2.2.comp
    (continuous_id.prodMk (continuous_const (y := (⟨0, by norm_num⟩ : MomentInterval))))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma reciprocal_deriv_norm_sq_moment (μ : Measure DiskFamily) [IsFiniteMeasure μ] (β : ℝ)
    (hlaw : ReciprocalMeanLaw μ β) :
    (∫ f, ‖deriv (reciprocalFunction f) I‖ ^ 2 ∂μ) = β * (β + 1) := by
  simp_rw [← normPathSecond_add_axes]
  rw [integral_add (normPathSecond_integrable_zero μ 1 (by simp))
    (normPathSecond_integrable_zero μ I (by simp)),
    normPathSecond_integral_zero μ β hlaw 1 (by simp),
    normPathSecond_integral_zero μ β hlaw I (by simp)]
  simp

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.JacobianMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

open Set Filter Complex
open scoped Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

lemma reciprocalFunction_deriv_I (f : DiskFamily) :
    deriv (reciprocalFunction f) I = -deriv (deriv (halfPlaneFunction f)) I := by
  have h := (((halfPlaneFunction_differentiableOn f).deriv isOpen_halfPlane).differentiableAt
    (isOpen_halfPlane.mem_nhds (show (I : ℂ).im > 0 by simp))).hasDerivAt
  have hn : deriv (halfPlaneFunction f) I ≠ 0 := by simp
  change deriv (fun z => (deriv (halfPlaneFunction f) z)⁻¹) I = _
  simpa using! (h.inv hn).deriv

lemma logarithmicDerivative_I_eq (f : DiskFamily) :
    logarithmicDerivative (halfPlaneFunction f) I = deriv (reciprocalFunction f) I * I := by
  rw [reciprocalFunction_deriv_I]
  simp [logarithmicDerivative, mul_comm]

lemma continuous_logarithmicDerivative_I :
    Continuous (fun f : DiskFamily => logarithmicDerivative (halfPlaneFunction f) I) := by
  simp_rw [logarithmicDerivative_I_eq]
  exact (continuous_reciprocalFunction_deriv.comp
    (continuous_id.prodMk (continuous_const (y := (⟨I, by simp⟩ : HalfPlaneSet))))).mul_const I

lemma logarithmicDerivative_real_moment (μ : Measure DiskFamily) [IsFiniteMeasure μ] (β : ℝ)
    (hlaw : ReciprocalMeanLaw μ β) :
    (∫ f, (logarithmicDerivative (halfPlaneFunction f) I).re ∂μ) = -β := by
  simpa [logarithmicDerivative_I_eq] using
    normPathFirst_integral_zero μ β hlaw I (by simp)

lemma logarithmicDerivative_norm_sq_moment (μ : Measure DiskFamily) [IsFiniteMeasure μ] (β : ℝ)
    (hlaw : ReciprocalMeanLaw μ β) :
    (∫ f, ‖logarithmicDerivative (halfPlaneFunction f) I‖ ^ 2 ∂μ) = β * (β + 1) := by
  simpa [logarithmicDerivative_I_eq, norm_mul] using
    reciprocal_deriv_norm_sq_moment μ β hlaw

lemma halfPlaneFunction_normalizedJacobian_I (f : DiskFamily) {k : ℝ} (hk : k ≠ 0) :
    normalizedJacobian k (halfPlaneFunction f) I = jacobianExpression k (halfPlaneFunction f) I :=
  normalizedJacobian_eq hk ((halfPlaneFunction_differentiableOn f).differentiableAt
    (isOpen_halfPlane.mem_nhds (by simp)))
    (((halfPlaneFunction_differentiableOn f).deriv isOpen_halfPlane).differentiableAt
    (isOpen_halfPlane.mem_nhds (by simp))) (by simp)

lemma expected_normalizedJacobian (μ : ProbabilityMeasure DiskFamily) (β k : ℝ)
    (hk : k ≠ 0) (hlaw : ReciprocalMeanLaw (μ : Measure DiskFamily) β) :
    k ^ 2 * (∫ f, normalizedJacobian k (halfPlaneFunction f) I ∂(μ : Measure DiskFamily)) =
      k * (k - 1) - (2 * k - 1) * β + β * (β + 1) := by
  have hq := continuous_logarithmicDerivative_I
  have h₁ : Integrable (fun f : DiskFamily => (2 * k - 1) *
      (logarithmicDerivative (halfPlaneFunction f) I).re) (μ : Measure DiskFamily) :=
    ((Complex.continuous_re.comp hq).const_mul _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h₂ : Integrable (fun f : DiskFamily => ‖logarithmicDerivative (halfPlaneFunction f) I‖ ^ 2) (μ : Measure DiskFamily) :=
    (hq.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h₀₁ : Integrable (fun f : DiskFamily => k * (k - 1) +
      (2 * k - 1) * (logarithmicDerivative (halfPlaneFunction f) I).re) (μ : Measure DiskFamily) :=
    (integrable_const _).add h₁
  have hadd := integral_add h₀₁ h₂
  have hadd₁ := integral_add (integrable_const (k * (k - 1))) h₁
  simp_rw [halfPlaneFunction_normalizedJacobian_I _ hk, jacobianExpression]
  rw [integral_div, hadd, hadd₁, integral_const_mul (2 * k - 1),
    logarithmicDerivative_real_moment _ β hlaw, logarithmicDerivative_norm_sq_moment _ β hlaw]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  field_simp
  ring

theorem expected_normalizedJacobian_at_source_k (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hβ : 1 / 4 ≤ β) (hlaw : ReciprocalMeanLaw (μ : Measure DiskFamily) β) :
    ((β + 2) / 3) ^ 2 *
      (∫ f, normalizedJacobian ((β + 2) / 3) (halfPlaneFunction f) I ∂(μ : Measure DiskFamily)) =
      ((4 * β - 1) * (β + 2)) / 9 := by
  rw [expected_normalizedJacobian μ β ((β + 2) / 3) (by linarith) hlaw]
  ring

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.AreaTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma measurable_halfPlaneProjection : Measurable halfPlaneProjection :=
  UpperHalfPlane.measurableEmbedding_coe.measurable_invFun

lemma halfPlaneProjection_of_pos {z : ℂ} (hz : 0 < z.im) :
    halfPlaneProjection z = ⟨z, hz⟩ := halfPlaneProjection_coe ⟨z, hz⟩

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.CriticalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
namespace StrictInverseFirstPower
noncomputable section

lemma criticalHeight_pos {k : ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hk : 0 < k) (hz : 0 < z.im) (hF : deriv F z ≠ 0) :
    0 < criticalHeight k F z := by
  exact mul_pos (mul_pos hk (Real.rpow_pos_of_pos hz _)) (norm_pos_iff.mpr (inv_ne_zero hF))

lemma continuous_criticalMap (k : ℝ) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => criticalMap k (halfPlaneFunction p.1) p.2) := by
  exact continuous_halfPlaneFunction.sub ((continuous_const.mul
    (Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.comp continuous_snd))).mul
    continuous_halfPlaneFunction_deriv |>.div_const _)

lemma continuous_criticalHeight (k : ℝ) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => criticalHeight k (halfPlaneFunction p.1) p.2) := by
  apply (continuous_const.mul ?_).mul ?_
  · exact (UpperHalfPlane.continuous_im.comp continuous_snd).rpow_const
      (fun p => Or.inl p.2.im_ne_zero)
  · exact (continuous_halfPlaneFunction_deriv.inv₀
      (fun p => halfPlaneFunction_deriv_ne_zero p.1 p.2.im_pos)).norm

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.MeasurableGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma isClosed_exists_mem_compact {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {R : Set (P × X)} (hR : IsClosed R) :
    IsClosed {p : P | ∃ x ∈ K, (p,x) ∈ R} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : IsClosed {q : P × K | (q.1,(q.2:X)) ∈ R} :=
    hR.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hh := isClosedMap_fst_of_compactSpace _ hc
  convert hh using 1
  ext p
  simp only [mem_ofPred_eq, mem_image, Prod.exists, Subtype.exists, exists_and_right,
    exists_eq_right]
  constructor <;> rintro ⟨x,hx,hr⟩ <;> exact ⟨x,hx,hr⟩

lemma measurableSet_exists_of_closed_sigmaCompact {P X : Type*}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace X] [SigmaCompactSpace X]
    {R : Set (P × X)} (hR : IsClosed R) :
    MeasurableSet {p : P | ∃ x : X, (p,x) ∈ R} := by
  have he : {p : P | ∃ x : X, (p,x) ∈ R} =
      ⋃ n : ℕ, {p : P | ∃ x ∈ compactCovering X n, (p,x) ∈ R} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨n,hn⟩ := (iUnion_eq_univ_iff.mp (iUnion_compactCovering X)) x
      exact ⟨n,x,hn,hx⟩
    · rintro ⟨n,x,_,hx⟩
      exact ⟨x,hx⟩
  rw [he]
  exact MeasurableSet.iUnion (fun n =>
    (isClosed_exists_mem_compact (isCompact_compactCovering X n) hR).measurableSet)

lemma measurableSet_compact_positive_sublevels {P X : Type*}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X] [WeaklyLocallyCompactSpace X]
    {g : P × X → ℝ} (hg : Continuous g) :
    MeasurableSet {p : P | ∀ r : ℝ, 0 < r → IsCompact {x : X | g (p,x) ≤ r}} := by
  let K : CompactExhaustion X := CompactExhaustion.choice X
  let C (n m : ℕ) : Set P := {p | ∀ x : X, x ∉ K m → (n:ℝ)+1 ≤ g (p,x)}
  have hC (n m : ℕ) : IsClosed (C n m) := by
    change IsClosed {p | ∀ x : X, x ∉ K m → (n:ℝ)+1 ≤ g (p,x)}
    simp only [ofPred_forall]
    exact isClosed_iInter (fun x => isClosed_iInter (fun _ =>
      isClosed_le continuous_const (hg.comp (continuous_id.prodMk continuous_const))))
  have he : {p : P | ∀ r : ℝ, 0 < r → IsCompact {x : X | g (p,x) ≤ r}} =
      ⋂ n : ℕ, ⋃ m : ℕ, C n m := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · intro hp n
      obtain ⟨m, hm⟩ := K.exists_superset_of_isCompact (hp ((n:ℝ)+1) (by positivity))
      refine ⟨m, ?_⟩
      intro x hx
      exact le_of_lt (lt_of_not_ge (fun hh => hx (hm hh)))
    · intro hp r hr
      obtain ⟨n,hn⟩ := exists_nat_gt r
      obtain ⟨m,hm⟩ := hp n
      have hs : {x : X | g (p,x) ≤ r} ⊆ K m := by
        intro x hx
        by_contra hxK
        have hh := hm x hxK
        exact (not_le_of_gt (lt_trans hn (by linarith : (n:ℝ)<(n:ℝ)+1))) (hh.trans hx)
      exact IsCompact.of_isClosed_subset (K.isCompact m)
        (isClosed_le (hg.comp (continuous_const.prodMk continuous_id)) continuous_const) hs
  rw [he]
  exact MeasurableSet.iInter (fun n => MeasurableSet.iUnion (fun m => (hC n m).measurableSet))

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma continuous_logarithmicDerivative :
    Continuous (fun p : DiskFamily × HalfPlaneSet => logarithmicDerivative (halfPlaneFunction p.1) p.2) := by
  have he : (fun p : DiskFamily × HalfPlaneSet => logarithmicDerivative (halfPlaneFunction p.1) p.2) =
      (fun p => I * (p.2.val.im : ℂ) * (deriv (reciprocalFunction p.1) p.2 / reciprocalFunction p.1 p.2)) := by
    funext p
    exact logarithmicDerivative_eq_reciprocal _ p.2.property
  rw [he]
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_im.comp (continuous_subtype_val.comp continuous_snd)))).mul
    (continuous_reciprocalFunction_deriv.div continuous_reciprocalFunction
      (fun p => reciprocalFunction_ne_zero _ p.2.property))

lemma continuous_jacobianExpression (k : ℝ) :
    Continuous (fun p : DiskFamily × HalfPlaneSet => jacobianExpression k (halfPlaneFunction p.1) p.2) := by
  unfold jacobianExpression
  exact ((continuous_const.add ((Complex.continuous_re.comp continuous_logarithmicDerivative).const_mul _)).add
    (continuous_logarithmicDerivative.norm.pow 2)).div_const _

lemma jacobianExpression_rebase_I (k : ℝ) (f : DiskFamily) (z : UpperHalfPlane) :
    jacobianExpression k (halfPlaneFunction (rebase f z)) I =
      jacobianExpression k (halfPlaneFunction f) z := by
  simpa using jacobianExpression_rebase k f z UpperHalfPlane.I

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma continuous_reciprocalPotential (k : ℝ) :
    Continuous (fun p : (DiskFamily × ℂ) × UpperHalfPlane => reciprocalPotential k p.1 p.2) := by
  exact ((continuous_halfPlaneFunction.comp
    ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).sub
      (continuous_snd.comp continuous_fst)).norm.div
    ((UpperHalfPlane.continuous_im.comp continuous_snd).rpow_const (fun p => Or.inl p.2.im_ne_zero))
    (fun p => (Real.rpow_pos_of_pos p.2.im_pos _).ne')

lemma continuous_jacobianExpression_upper (k : ℝ) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => jacobianExpression k (halfPlaneFunction p.1) p.2) := by
  have hc : Continuous (fun p : DiskFamily × UpperHalfPlane =>
      (p.1, (⟨(p.2:ℂ),p.2.im_pos⟩ : HalfPlaneSet))) :=
    continuous_fst.prodMk ((UpperHalfPlane.continuous_coe.comp continuous_snd).subtype_mk _)
  have hh := (continuous_jacobianExpression k).comp hc
  exact hh

lemma measurableSet_regular_pairs (k : ℝ) :
    MeasurableSet {p : DiskFamily × ℂ | ∀ z : UpperHalfPlane,
      criticalMap k (halfPlaneFunction p.1) z = p.2 →
        jacobianExpression k (halfPlaneFunction p.1) z ≠ 0} := by
  have hm : Continuous (fun q : (DiskFamily × ℂ) × UpperHalfPlane => (q.1.1,q.2)) :=
    (continuous_fst.comp continuous_fst).prodMk continuous_snd
  have hG := (continuous_criticalMap k).comp hm
  have hJ := (continuous_jacobianExpression_upper k).comp hm
  have he := measurableSet_exists_of_closed_sigmaCompact
    ((isClosed_eq hG (continuous_snd.comp continuous_fst)).inter (isClosed_eq hJ (continuous_const (y := (0 : ℝ)))))
  convert he.compl using 1
  ext p
  simp

lemma measurableSet_untied_pairs (k : ℝ) :
    MeasurableSet {p : DiskFamily × ℂ | ∀ z w : UpperHalfPlane,
      criticalMap k (halfPlaneFunction p.1) z = p.2 →
      criticalMap k (halfPlaneFunction p.1) w = p.2 →
      criticalHeight k (halfPlaneFunction p.1) z = criticalHeight k (halfPlaneFunction p.1) w → z = w} := by
  let R (n : ℕ) : Set ((DiskFamily × ℂ) × (UpperHalfPlane × UpperHalfPlane)) :=
    {q | criticalMap k (halfPlaneFunction q.1.1) q.2.1 = q.1.2 ∧
      criticalMap k (halfPlaneFunction q.1.1) q.2.2 = q.1.2 ∧
      criticalHeight k (halfPlaneFunction q.1.1) q.2.1 = criticalHeight k (halfPlaneFunction q.1.1) q.2.2 ∧
      1/((n:ℝ)+1) ≤ dist (q.2.1 : ℂ) (q.2.2 : ℂ)}
  have hR (n : ℕ) : IsClosed (R n) := by
    exact (isClosed_eq ((continuous_criticalMap k).comp
      ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd)))
        (continuous_snd.comp continuous_fst)).inter <|
      (isClosed_eq ((continuous_criticalMap k).comp
        ((continuous_fst.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd)))
          (continuous_snd.comp continuous_fst)).inter <|
      (isClosed_eq ((continuous_criticalHeight k).comp
        ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd)))
        ((continuous_criticalHeight k).comp
          ((continuous_fst.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd)))).inter <|
      isClosed_le continuous_const
        ((UpperHalfPlane.continuous_coe.comp (continuous_fst.comp continuous_snd)).dist
          (UpperHalfPlane.continuous_coe.comp (continuous_snd.comp continuous_snd)))
  have he : {p : DiskFamily × ℂ | ∀ z w : UpperHalfPlane,
      criticalMap k (halfPlaneFunction p.1) z = p.2 →
      criticalMap k (halfPlaneFunction p.1) w = p.2 →
      criticalHeight k (halfPlaneFunction p.1) z = criticalHeight k (halfPlaneFunction p.1) w → z = w} =
      (⋃ n : ℕ, {p : DiskFamily × ℂ | ∃ x : UpperHalfPlane × UpperHalfPlane, (p,x) ∈ R n})ᶜ := by
    ext p
    simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion]
    constructor
    · intro hp
      rintro ⟨n,⟨z,w⟩,hz,hw,hv,hd⟩
      have := hp z w hz hw hv
      subst w
      have h0 := one_div_pos.mpr (by positivity : (0:ℝ)<(n:ℝ)+1)
      rw [dist_self] at hd
      linarith
    · intro hp z w hz hw hv
      by_contra hne
      have hd : 0 < dist (z:ℂ) (w:ℂ) := dist_pos.mpr (fun he => hne (UpperHalfPlane.ext he))
      obtain ⟨n,hn⟩ := exists_nat_gt (1 / dist (z:ℂ) (w:ℂ))
      apply hp
      refine ⟨n,(z,w),hz,hw,hv,?_⟩
      apply (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
      have hh := (div_lt_iff₀ hd).mp hn
      nlinarith
  rw [he]
  exact (MeasurableSet.iUnion (fun n => measurableSet_exists_of_closed_sigmaCompact (hR n))).compl

lemma measurableSet_goodPairs (k : ℝ) : MeasurableSet {p : DiskFamily × ℂ | GoodPair k p} := by
  have hc : MeasurableSet {p : DiskFamily × ℂ |
      ∀ h : ℝ, 0 < h → IsCompact (potentialSuperlevel k (halfPlaneFunction p.1) p.2 h)} := by
    simp only [compactPotential_iff]
    exact measurableSet_compact_positive_sublevels (continuous_reciprocalPotential k)
  exact hc.inter ((measurableSet_regular_pairs k).inter (measurableSet_untied_pairs k))

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.RegularTargets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology

open Set Filter MeasureTheory Complex
open scoped Topology

open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma isOpen_regular_locus {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) :
    IsOpen {z ∈ U | (fderiv ℝ G z).det ≠ 0} := by
  exact ((ContinuousLinearMap.continuous_det).comp_continuousOn
    (hG.continuousOn_fderiv_of_isOpen hU le_rfl)).isOpen_inter_preimage hU
      (isOpen_ne_fun continuous_id (continuous_const (y := (0:ℝ))))

lemma regular_inverse_chart {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) {z : ℂ} (hz : z ∈ U) (hd : (fderiv ℝ G z).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, (e : ℂ → ℂ) = G ∧ z ∈ e.source ∧
      e.source ⊆ {w ∈ U | (fderiv ℝ G w).det ≠ 0} ∧ ContDiffOn ℝ 1 e.symm e.target := by
  let R := {w ∈ U | (fderiv ℝ G w).det ≠ 0}
  have hR : IsOpen R := isOpen_regular_locus hU hG
  have hcz : ContDiffAt ℝ 1 G z := hG.contDiffAt (hU.mem_nhds hz)
  let L := (fderiv ℝ G z).toContinuousLinearEquivOfDetNeZero hd
  have hdz : HasFDerivAt G (L : ℂ →L[ℝ] ℂ) z := by
    simpa only [L, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using
      (hcz.differentiableAt one_ne_zero).hasFDerivAt
  let e0 := hcz.toOpenPartialHomeomorph G hdz one_ne_zero
  let e := e0.restr R
  have he : (e : ℂ → ℂ) = G := rfl
  have hs : e.source ⊆ R := by
    rw [show e = e0.restr R from rfl, e0.restr_source' R hR]
    exact inter_subset_right
  refine ⟨e, he, ?_, hs, ?_⟩
  · rw [show e = e0.restr R from rfl, e0.restr_source' R hR]
    exact ⟨hcz.mem_toOpenPartialHomeomorph_source hdz one_ne_zero, hz, hd⟩
  · intro ξ hξ
    have hp := hs (e.map_target hξ)
    have hc : ContDiffAt ℝ 1 G (e.symm ξ) := hG.contDiffAt (hU.mem_nhds hp.1)
    let A := (fderiv ℝ G (e.symm ξ)).toContinuousLinearEquivOfDetNeZero hp.2
    have hdf : HasFDerivAt e (A : ℂ →L[ℝ] ℂ) (e.symm ξ) := by
      rw [he]
      simpa only [A, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using
        (hc.differentiableAt one_ne_zero).hasFDerivAt
    exact (e.contDiffAt_symm hξ hdf (he ▸ hc)).contDiffWithinAt

lemma countable_regular_inverse_charts {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) :
    ∃ C : Set (OpenPartialHomeomorph ℂ ℂ), C.Countable ∧
      (∀ e ∈ C, (e : ℂ → ℂ) = G ∧
        e.source ⊆ {z ∈ U | (fderiv ℝ G z).det ≠ 0} ∧ ContDiffOn ℝ 1 e.symm e.target) ∧
      {z ∈ U | (fderiv ℝ G z).det ≠ 0} ⊆ ⋃ e ∈ C, e.source := by
  classical
  let R := {z ∈ U | (fderiv ℝ G z).det ≠ 0}
  have hex (z : R) := regular_inverse_chart hU hG z.property.1 z.property.2
  choose E hE hmem hsub hdiff using hex
  have hcover : R ⊆ ⋃ z : R, (E z).source := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z,hz⟩,hmem ⟨z,hz⟩⟩
  obtain ⟨c,hc,hcov⟩ := (HereditarilyLindelofSpace.isLindelof R).elim_countable_subcover
    (fun z : R => (E z).source) (fun z => (E z).open_source) hcover
  refine ⟨E '' c,hc.image E,?_,?_⟩
  · rintro e ⟨z,_,rfl⟩
    exact ⟨hE z,hsub z,hdiff z⟩
  · intro z hz
    obtain ⟨w,hw,hz'⟩ := mem_iUnion₂.mp (hcov hz)
    exact mem_iUnion₂.mpr ⟨E w,⟨w,hw,rfl⟩,hz'⟩

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.DescendingRanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set

namespace StrictInverseFirstPower
noncomputable section

lemma descendingRank_lt_of_value_lt {X : Type*} {v : X → ℝ} {S : Set X}
    {x y : X} (hy : y ∈ S) (hxy : v x < v y)
    (hfin : {z | z ∈ S ∧ v x < v z}.Finite) :
    descendingRank v S y < descendingRank v S x := by
  unfold descendingRank
  apply Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩) hfin
  · intro z hz
    exact ⟨hz.1,hxy.trans hz.2⟩
  · intro he
    have hyx : y ∈ {z | z ∈ S ∧ v x < v z} := ⟨hy,hxy⟩
    rw [← he] at hyx
    exact lt_irrefl _ hyx.2

lemma descendingRank_injOn {X : Type*} {v : X → ℝ} {S : Set X}
    (hv : InjOn v S) (hfin : ∀ x ∈ S, {z | z ∈ S ∧ v x < v z}.Finite) :
    InjOn (descendingRank v S) S := by
  intro x hx y hy he
  apply hv hx hy
  rcases lt_trichotomy (v x) (v y) with hlt | heq | hgt
  · exact False.elim ((descendingRank_lt_of_value_lt hy hlt (hfin x hx)).ne he.symm)
  · exact heq
  · exact False.elim ((descendingRank_lt_of_value_lt hx hgt (hfin y hy)).ne he)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.BorelRanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma measurableSet_exists_closed_open {P X : Type*}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace X] [SigmaCompactSpace X] [PerfectlyNormalSpace (P × X)]
    {C U : Set (P × X)} (hC : IsClosed C) (hU : IsOpen U) :
    MeasurableSet {p : P | ∃ x : X, (p,x) ∈ C ∩ U} := by
  obtain ⟨W,hW,hUW⟩ := hU.isClosed_compl.isGδ.eq_iInter_nat
  have he : U = ⋃ n : ℕ, (W n)ᶜ := by
    rw [← compl_iInter, ← hUW, compl_compl]
  have hp : {p : P | ∃ x : X, (p,x) ∈ C ∩ U} =
      ⋃ n : ℕ, {p : P | ∃ x : X, (p,x) ∈ C ∩ (W n)ᶜ} := by
    ext p
    simp only [mem_ofPred_eq,mem_iUnion,mem_inter_iff,he]
    constructor
    · rintro ⟨x,hx,n,hn⟩
      exact ⟨n,x,hx,hn⟩
    · rintro ⟨n,x,hx,hn⟩
      exact ⟨x,hx,n,hn⟩
  rw [hp]
  exact MeasurableSet.iUnion (fun n =>
    measurableSet_exists_of_closed_sigmaCompact (hC.inter (hW n).isClosed_compl))

lemma finite_ncard_ge_iff_tuple {X : Type*} {S : Set X} (hS : S.Finite) (n : ℕ) :
    n ≤ S.ncard ↔ ∃ t : Fin n → X, Function.Injective t ∧ ∀ i, t i ∈ S := by
  classical
  let := hS.fintype
  have hc : S.ncard = Fintype.card S := by
    rw [Set.ncard_eq_toFinset_card']
    exact Set.toFinset_card S
  rw [hc]
  constructor
  · intro hn
    let e : Fin n ↪ S := (Fin.castLEEmb hn).trans (Fintype.equivFin S).symm.toEmbedding
    exact ⟨fun i => (e i : X), Subtype.val_injective.comp e.injective, fun i => (e i).2⟩
  · rintro ⟨t,ht,hS⟩
    simpa using Fintype.card_le_of_injective (fun i : Fin n => (⟨t i,hS i⟩ : S))
      (fun i j h => ht (congrArg Subtype.val h))

lemma measurable_ncard_locally_closed_fiber {P X : Type*}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P] [TopologicalSpace.MetrizableSpace P]
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SigmaCompactSpace X]
    {C U : Set (P × X)} (hC : IsClosed C) (hU : IsOpen U)
    (hf : ∀ p : P, {x : X | (p,x) ∈ C ∩ U}.Finite) :
    Measurable (fun p : P => {x : X | (p,x) ∈ C ∩ U}.ncard) := by
  apply measurable_of_Ici
  intro n
  let Cn : Set (P × (Fin n → X)) := {q | ∀ i, (q.1,q.2 i) ∈ C}
  let Un : Set (P × (Fin n → X)) :=
    {q | (∀ i, (q.1,q.2 i) ∈ U) ∧ Function.Injective q.2}
  have hCn : IsClosed Cn := by
    change IsClosed {q : P × (Fin n → X) | ∀ i, (q.1,q.2 i) ∈ C}
    simp only [ofPred_forall]
    exact isClosed_iInter (fun i => hC.preimage
      (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)))
  have hUn : IsOpen Un := by
    have hmem : IsOpen {q : P × (Fin n → X) | ∀ i, (q.1,q.2 i) ∈ U} := by
      simp only [ofPred_forall]
      exact isOpen_iInter_of_finite (fun i => hU.preimage
        (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)))
    have hinj : IsOpen {q : P × (Fin n → X) | Function.Injective q.2} := by
      have he : {q : P × (Fin n → X) | Function.Injective q.2} =
          {q | ∀ i j : Fin n, i ≠ j → q.2 i ≠ q.2 j} := by
        ext q
        simp only [mem_ofPred_eq]
        constructor
        · intro h i j hij heq
          exact hij (h heq)
        · intro h i j heq
          by_contra hij
          exact h i j hij heq
      rw [he]
      simp only [ofPred_forall]
      exact isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun j =>
        isOpen_iInter_of_finite (fun _ => isOpen_ne_fun
          ((continuous_apply i).comp continuous_snd) ((continuous_apply j).comp continuous_snd))))
    exact hmem.inter hinj
  have hp := measurableSet_exists_closed_open hCn hUn
  convert hp using 1
  ext p
  simp only [mem_preimage,mem_Ici,mem_ofPred_eq,Cn,Un,mem_inter_iff]
  have htest := finite_ncard_ge_iff_tuple (hf p) n
  simp only [mem_inter_iff] at htest
  rw [htest]
  constructor
  · rintro ⟨t,ht,hm⟩
    exact ⟨t,fun i => (hm i).1,fun i => (hm i).2,ht⟩
  · rintro ⟨t,hC,hU,ht⟩
    exact ⟨t,ht,fun i => ⟨hC i,hU i⟩⟩

lemma measurable_of_borel_graph {P X : Type*}
    [MeasurableSpace P] [MeasurableSpace X]
    [StandardBorelSpace P] [StandardBorelSpace X]
    {f : P → X} (hg : MeasurableSet {q : P × X | f q.1 = q.2}) :
    Measurable f := by
  let R : Set (P × X) := {q | f q.1 = q.2}
  have : StandardBorelSpace R := hg.standardBorel
  let π : R → P := fun q => q.1.1
  have hπ : MeasurableEmbedding π :=
    (measurable_fst.comp measurable_subtype_coe).measurableEmbedding (by
      intro q r he
      apply Subtype.ext
      apply Prod.ext he
      exact q.2.symm.trans ((congrArg f he).trans r.2))
  intro A hA
  have hm : MeasurableSet {q : R | q.1.2 ∈ A} :=
    (measurable_snd.comp measurable_subtype_coe) hA
  have hi := hπ.measurableSet_image.mpr hm
  convert hi using 1
  ext p
  simp only [mem_preimage,mem_image,mem_ofPred_eq,π]
  constructor
  · intro hp
    exact ⟨⟨(p,f p),rfl⟩,hp,rfl⟩
  · rintro ⟨q,hq,rfl⟩
    rwa [q.2]

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.CriticalRanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma signedCriticalFiber_strictCut_finite {k : ℝ} (hk : 0 < k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) (positive : Bool) (z : UpperHalfPlane) :
    {w | w ∈ signedCriticalFiber k f ξ positive ∧
      criticalHeight k (halfPlaneFunction f) z < criticalHeight k (halfPlaneFunction f) w}.Finite := by
  apply (goodPair_criticalCut_finite hk hg
    (criticalHeight_pos hk z.im_pos (halfPlaneFunction_deriv_ne_zero f z.im_pos))).subset
  intro w hw
  exact ⟨hw.1.1,hw.2.le⟩

lemma goodPair_criticalHeight_injOn {k : ℝ} {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) :
    InjOn (fun w : UpperHalfPlane => criticalHeight k (halfPlaneFunction f) w)
      {w : UpperHalfPlane | criticalMap k (halfPlaneFunction f) w = ξ} := by
  intro z hz w hw he
  exact hg.2.2 z w hz hw he

lemma criticalRank_injOn {k : ℝ} (hk : 0 < k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) (positive : Bool) :
    InjOn (criticalRank k f ξ positive) (signedCriticalFiber k f ξ positive) := by
  apply descendingRank_injOn
    ((goodPair_criticalHeight_injOn hg).mono (fun _ hz => hz.1))
  intro z _
  exact signedCriticalFiber_strictCut_finite hk hg positive z

lemma continuous_rank_f (k : ℝ) :
    Continuous (fun q : RankParameters k × UpperHalfPlane => q.1.1.1.1) :=
  continuous_fst.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))

lemma continuous_rank_z (k : ℝ) :
    Continuous (fun q : RankParameters k × UpperHalfPlane => q.1.1.2) :=
  continuous_snd.comp (continuous_subtype_val.comp continuous_fst)

lemma isClosed_rankClosedRelation (k : ℝ) : IsClosed (rankClosedRelation k) := by
  have hG := (continuous_criticalMap k).comp ((continuous_rank_f k).prodMk continuous_snd)
  have hξ : Continuous (fun q : RankParameters k × UpperHalfPlane => q.1.1.1.2) :=
    continuous_snd.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))
  exact isClosed_eq hG hξ

lemma isOpen_rankOpenRelation (k : ℝ) (positive : Bool) :
    IsOpen (rankOpenRelation k positive) := by
  have hJ := (continuous_jacobianExpression_upper k).comp
    ((continuous_rank_f k).prodMk continuous_snd)
  have hVz := (continuous_criticalHeight k).comp
    ((continuous_rank_f k).prodMk (continuous_rank_z k))
  have hVw := (continuous_criticalHeight k).comp ((continuous_rank_f k).prodMk continuous_snd)
  apply IsOpen.inter _ (isOpen_lt hVz hVw)
  cases positive
  · exact isOpen_lt hJ continuous_const
  · exact isOpen_lt continuous_const hJ

lemma rankRelation_finite {k : ℝ} (hk : 0 < k) (positive : Bool) (p : RankParameters k) :
    {w | (p,w) ∈ rankClosedRelation k ∩ rankOpenRelation k positive}.Finite := by
  convert signedCriticalFiber_strictCut_finite hk p.2 positive p.1.2 using 1
  ext w
  change (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ _)
  tauto

lemma measurable_criticalRank {k : ℝ} (hk : 0 < k) (positive : Bool) :
    Measurable (fun p : RankParameters k =>
      criticalRank k p.1.1.1 p.1.1.2 positive p.1.2) := by
  have hr := measurable_ncard_locally_closed_fiber
    (isClosed_rankClosedRelation k) (isOpen_rankOpenRelation k positive)
    (rankRelation_finite hk positive)
  convert hr using 1
  funext p
  unfold criticalRank descendingRank
  congr 1
  ext w
  change ((_ ∧ _) ∧ _) ↔ (_ ∧ _ ∧ _)
  tauto

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.RankPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

instance rankParameters_standardBorel (k : ℝ) : StandardBorelSpace (RankParameters k) :=
  ((measurableSet_goodPairs k).preimage measurable_fst).standardBorel

lemma measurableSet_rankPairRelation {k : ℝ} (hk : 0 < k) :
    MeasurableSet {q : RankParameters k × UpperHalfPlane | RankPairRelation k q.1 q.2} := by
  have hGz := (continuous_criticalMap k).comp
    ((continuous_rank_f k).prodMk (continuous_rank_z k))
  have hGw := (continuous_criticalMap k).comp
    ((continuous_rank_f k).prodMk continuous_snd)
  have hξ : Continuous (fun q : RankParameters k × UpperHalfPlane => q.1.1.1.2) :=
    continuous_snd.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))
  have hJz := (continuous_jacobianExpression_upper k).comp
    ((continuous_rank_f k).prodMk (continuous_rank_z k))
  have hJw := (continuous_jacobianExpression_upper k).comp
    ((continuous_rank_f k).prodMk continuous_snd)
  have hHz := (continuous_criticalHeight k).comp
    ((continuous_rank_f k).prodMk (continuous_rank_z k))
  have hHw := (continuous_criticalHeight k).comp
    ((continuous_rank_f k).prodMk continuous_snd)
  let replace : RankParameters k × UpperHalfPlane → RankParameters k :=
    fun q => ⟨(q.1.1.1,q.2),q.1.2⟩
  have hr : Measurable replace :=
    ((measurable_fst.comp (measurable_subtype_coe.comp measurable_fst)).prodMk
      measurable_snd).subtype_mk
  have hm1 := (measurable_criticalRank hk false).comp hr
  have hm2 : Measurable (fun q : RankParameters k × UpperHalfPlane =>
      criticalRank k q.1.1.1.1 q.1.1.1.2 true q.1.1.2) :=
    (measurable_criticalRank hk true).comp measurable_fst
  exact ((isClosed_eq hGz hξ).measurableSet.inter (isOpen_lt continuous_const hJz).measurableSet).inter
    (((isClosed_eq hGw hξ).measurableSet.inter (isOpen_lt hJw continuous_const).measurableSet).inter
      ((measurableSet_eq_fun hm1 hm2).inter (isOpen_lt hHz hHw).measurableSet))

lemma rankPairRelation_unique {k : ℝ} (hk : 0 < k) {p : RankParameters k}
    {v w : UpperHalfPlane} (hv : RankPairRelation k p v) (hw : RankPairRelation k p w) : v = w := by
  exact criticalRank_injOn hk p.2 false hv.2.1 hw.2.1 (hv.2.2.1.trans hw.2.2.1.symm)

lemma measurableSet_rankPairingDomain {k : ℝ} (hk : 0 < k) :
    MeasurableSet (rankPairingDomain k) := by
  let R := {q : RankParameters k × UpperHalfPlane | RankPairRelation k q.1 q.2}
  have hR : MeasurableSet R := measurableSet_rankPairRelation hk
  let : StandardBorelSpace R := hR.standardBorel
  let π : R → RankParameters k := fun q => q.1.1
  have hπ : MeasurableEmbedding π :=
    (measurable_fst.comp measurable_subtype_coe).measurableEmbedding (by
      intro q r he
      apply Subtype.ext
      apply Prod.ext he
      have hr : RankPairRelation k q.1.1 r.1.2 := by
        change q.val.fst = r.val.fst at he
        rw [he]
        exact r.property
      exact rankPairRelation_unique hk q.2 hr)
  have he : π '' univ = rankPairingDomain k := by
    ext p
    constructor
    · rintro ⟨q,_,rfl⟩
      exact ⟨q.1.2,q.2⟩
    · rintro ⟨w,hw⟩
      exact ⟨⟨(p,w),hw⟩,mem_univ _,rfl⟩
  rw [← he]
  exact hπ.measurableSet_image.mpr MeasurableSet.univ

lemma availableRankPartner_spec (k : ℝ) (p : AvailableRankPair k) :
    RankPairRelation k p.1 (availableRankPartner k p) := Classical.choose_spec p.2

lemma measurable_availableRankPartner {k : ℝ} (hk : 0 < k) :
    Measurable (availableRankPartner k) := by
  let : StandardBorelSpace (AvailableRankPair k) := (measurableSet_rankPairingDomain hk).standardBorel
  apply measurable_of_borel_graph
  let π : AvailableRankPair k × UpperHalfPlane → RankParameters k × UpperHalfPlane :=
    fun q => (q.1.1, q.2)
  have hπ : Measurable π := by
    exact (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hm := (measurableSet_rankPairRelation hk).preimage hπ
  convert hm using 1
  ext q
  constructor
  · intro he
    change RankPairRelation k q.1.1 q.2
    rw [← he]
    exact availableRankPartner_spec k q.1
  · intro hr
    exact rankPairRelation_unique hk (availableRankPartner_spec k q.1) hr

lemma availableRankPartner_injOn_fiber {k : ℝ} (hk : 0 < k)
    {p q : AvailableRankPair k} (hf : p.1.1.1 = q.1.1.1)
    (he : availableRankPartner k p = availableRankPartner k q) : p.1.1.2 = q.1.1.2 := by
  have hp := availableRankPartner_spec k p
  have hq := availableRankPartner_spec k q
  have hff := congrArg Prod.fst hf
  have hfξ := congrArg Prod.snd hf
  have hq' : q.1.1.2 ∈ signedCriticalFiber k p.1.1.1.1 p.1.1.1.2 true := by
    rw [hff, hfξ]
    exact hq.1
  apply criticalRank_injOn hk p.1.2 true hp.1 hq'
  calc
    _ = criticalRank k p.1.1.1.1 p.1.1.1.2 false (availableRankPartner k p) := hp.2.2.1.symm
    _ = criticalRank k q.1.1.1.1 q.1.1.1.2 false (availableRankPartner k q) := by rw [he, hff, hfξ]
    _ = _ := by rw [hff, hfξ]; exact hq.2.2.1

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.CriticalCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma goodPair_rebase_iff (k : ℝ) (f : DiskFamily) (ξ : ℂ) (z : UpperHalfPlane) :
    GoodPair k (rebase f z,targetRebase f z ξ) ↔ GoodPair k (f,ξ) := by
  refine ⟨fun hg => ?_,fun hg => goodPair_rebase hg z⟩
  refine ⟨?_,?_,?_⟩
  · apply (compactPotential_iff _ _).mpr
    intro r hr
    have hc := (compactPotential_iff _ _).mp hg.1
      (r / heightRebaseScale k f z) (div_pos hr (heightRebaseScale_pos k f z))
    convert hc.image (affineUpperHomeomorph z).continuous using 1
    ext w
    constructor
    · intro hw
      let v := (affineUpperHomeomorph z).symm w
      have hv : affineProduct z v = w := (affineUpperHomeomorph z).apply_symm_apply w
      refine ⟨v,?_,hv⟩
      change reciprocalPotential k (rebase f z,targetRebase f z ξ) v ≤ _
      rw [reciprocalPotential_rebase,hv]
      exact (div_le_div_iff_of_pos_right (heightRebaseScale_pos k f z)).mpr hw
    · rintro ⟨v,hv,rfl⟩
      change reciprocalPotential k (rebase f z,targetRebase f z ξ) v ≤ _ at hv
      rw [reciprocalPotential_rebase] at hv
      exact (div_le_div_iff_of_pos_right (heightRebaseScale_pos k f z)).mp hv
  · intro w hw
    let v := (affineUpperHomeomorph z).symm w
    have hv : affineProduct z v = w := (affineUpperHomeomorph z).apply_symm_apply w
    have hc : criticalMap k (halfPlaneFunction (rebase f z)) v = targetRebase f z ξ :=
      (criticalMap_rebase_eq_iff k f z v ξ).mpr (hv.symm ▸ hw)
    simpa only [jacobianExpression_rebase,← coe_affineProduct,hv] using hg.2.1 v hc
  · intro u v hu hv he
    let a := (affineUpperHomeomorph z).symm u
    let b := (affineUpperHomeomorph z).symm v
    have ha : affineProduct z a = u := (affineUpperHomeomorph z).apply_symm_apply u
    have hb : affineProduct z b = v := (affineUpperHomeomorph z).apply_symm_apply v
    have hca : criticalMap k (halfPlaneFunction (rebase f z)) a = targetRebase f z ξ :=
      (criticalMap_rebase_eq_iff k f z a ξ).mpr (ha.symm ▸ hu)
    have hcb : criticalMap k (halfPlaneFunction (rebase f z)) b = targetRebase f z ξ :=
      (criticalMap_rebase_eq_iff k f z b ξ).mpr (hb.symm ▸ hv)
    have hab := hg.2.2 a b hca hcb (by
      rw [criticalHeight_rebase,criticalHeight_rebase,ha,hb,he])
    calc u = affineProduct z a := ha.symm
         _ = affineProduct z b := congrArg (affineProduct z) hab
         _ = v := hb

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.RankCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma availableRankPartner_rebase {k : ℝ} (hk : 0 < k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) (z w : UpperHalfPlane)
    (hp : (⟨((rebase f z,targetRebase f z ξ),w),goodPair_rebase hg z⟩ : RankParameters k) ∈
      rankPairingDomain k) :
    availableRankPartner k ⟨⟨((f,ξ),affineProduct z w),hg⟩,
      (rankPairingDomain_rebase_iff hg z w).mp hp⟩ =
    affineProduct z (availableRankPartner k ⟨⟨((rebase f z,targetRebase f z ξ),w),
      goodPair_rebase hg z⟩,hp⟩) := by
  let p : AvailableRankPair k :=
    ⟨⟨((rebase f z,targetRebase f z ξ),w),goodPair_rebase hg z⟩,hp⟩
  let q : AvailableRankPair k := ⟨⟨((f,ξ),affineProduct z w),hg⟩,
    (rankPairingDomain_rebase_iff hg z w).mp hp⟩
  change availableRankPartner k q = affineProduct z (availableRankPartner k p)
  have hp' := availableRankPartner_spec k p
  have hq' := availableRankPartner_spec k q
  have hr : RankPairRelation k q.1 (affineProduct z (availableRankPartner k p)) :=
    (rankPairRelation_rebase_iff hg z w (availableRankPartner k p)).mp hp'
  exact rankPairRelation_unique hk hq' hr

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.TransportPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma availableSource_injective {k : ℝ} : Function.Injective (availableSource k) := by
  intro p q he
  have hf : p.1.1.1.1 = q.1.1.1.1 := congrArg (fun q : DiskFamily × UpperHalfPlane => q.1) he
  have hz : p.1.1.2 = q.1.1.2 := congrArg (fun q : DiskFamily × UpperHalfPlane => q.2) he
  have hp := (availableRankPartner_spec k p).1.1
  have hq := (availableRankPartner_spec k q).1.1
  have hξ : p.1.1.1.2 = q.1.1.1.2 := by
    rw [← hp,← hq,hf,hz]
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (Prod.ext hf hξ) hz

lemma measurable_availableSource (k : ℝ) : Measurable (availableSource k) := by
  exact (measurable_fst.comp (measurable_fst.comp (measurable_subtype_coe.comp measurable_subtype_coe))).prodMk
    (measurable_snd.comp (measurable_subtype_coe.comp measurable_subtype_coe))

lemma measurableEmbedding_availableSource {k : ℝ} (hk : 0 < k) :
    MeasurableEmbedding (availableSource k) := by
  let : StandardBorelSpace (AvailableRankPair k) := (measurableSet_rankPairingDomain hk).standardBorel
  exact (measurable_availableSource k).measurableEmbedding availableSource_injective

lemma measurableSet_sourcePairingDomain {k : ℝ} (hk : 0 < k) :
    MeasurableSet (sourcePairingDomain k) := (measurableEmbedding_availableSource hk).measurableSet_range

lemma sourcePair_apply (k : ℝ) (q : sourcePairingDomain k) :
    availableSource k (sourcePair k q) = q.1 := q.2.choose_spec

lemma measurable_sourcePair {k : ℝ} (hk : 0 < k) : Measurable (sourcePair k) := by
  have he : sourcePair k = (measurableEmbedding_availableSource hk).equivRange.symm := by
    funext q
    apply availableSource_injective
    have ha := (measurableEmbedding_availableSource hk).equivRange.apply_symm_apply q
    have hb := congrArg Subtype.val ha
    rw [MeasurableEmbedding.equivRange_apply] at hb
    exact (sourcePair_apply k q).trans hb.symm
  rw [he]
  exact (measurableEmbedding_availableSource hk).equivRange.symm.measurable

lemma measurable_sourcePartnerOn {k : ℝ} (hk : 0 < k) : Measurable (sourcePartnerOn k) :=
  (measurable_availableRankPartner hk).comp (measurable_sourcePair hk)

lemma sourcePartner_of_mem (k : ℝ) {q : DiskFamily × UpperHalfPlane}
    (hq : q ∈ sourcePairingDomain k) : sourcePartner k q = sourcePartnerOn k ⟨q,hq⟩ := by
  classical
  simp only [sourcePartner,dite_eq_left hq]

lemma measurable_sourcePartner {k : ℝ} (hk : 0 < k) : Measurable (sourcePartner k) := by
  classical
  exact (measurable_sourcePartnerOn hk).dite measurable_const (measurableSet_sourcePairingDomain hk)

lemma sourcePairingDomain_iff (k : ℝ) (f : DiskFamily) (z : UpperHalfPlane) :
    (f,z) ∈ sourcePairingDomain k ↔
      ∃ hg : GoodPair k (f,criticalMap k (halfPlaneFunction f) z),
        (⟨((f,criticalMap k (halfPlaneFunction f) z),z),hg⟩ : RankParameters k) ∈ rankPairingDomain k := by
  constructor
  · rintro ⟨p,hp⟩
    have hf : p.1.1.1.1 = f := congrArg Prod.fst hp
    have hz : p.1.1.2 = z := congrArg Prod.snd hp
    have hξ : p.1.1.1.2 = criticalMap k (halfPlaneFunction f) z := by
      rw [← (availableRankPartner_spec k p).1.1,hf,hz]
    have hg : GoodPair k (f,criticalMap k (halfPlaneFunction f) z) := by
      rw [← hξ,← hf]
      exact p.1.2
    refine ⟨hg,?_⟩
    have he : (⟨((f,criticalMap k (halfPlaneFunction f) z),z),hg⟩ : RankParameters k) = p.1 := by
      apply Subtype.ext
      exact (Prod.ext (Prod.ext hf hξ) hz).symm
    rw [he]
    exact p.2
  · rintro ⟨hg,hp⟩
    exact ⟨⟨⟨((f,criticalMap k (halfPlaneFunction f) z),z),hg⟩,hp⟩,rfl⟩

lemma sourcePartner_spec (k : ℝ) {f : DiskFamily} {z : UpperHalfPlane}
    (hq : (f,z) ∈ sourcePairingDomain k) :
    GoodPair k (f,criticalMap k (halfPlaneFunction f) z) ∧
    0 < jacobianExpression k (halfPlaneFunction f) z ∧
    jacobianExpression k (halfPlaneFunction f) (sourcePartner k (f,z)) < 0 ∧
    criticalMap k (halfPlaneFunction f) (sourcePartner k (f,z)) =
      criticalMap k (halfPlaneFunction f) z ∧
    criticalHeight k (halfPlaneFunction f) z <
      criticalHeight k (halfPlaneFunction f) (sourcePartner k (f,z)) := by
  let p := sourcePair k ⟨(f,z),hq⟩
  have hp := availableRankPartner_spec k p
  have hsource := sourcePair_apply k ⟨(f,z),hq⟩
  have hf : p.1.1.1.1 = f := congrArg Prod.fst hsource
  have hz : p.1.1.2 = z := congrArg Prod.snd hsource
  have hξ : p.1.1.1.2 = criticalMap k (halfPlaneFunction f) z := by
    rw [← hp.1.1,hf,hz]
  have hr : sourcePartner k (f,z) = availableRankPartner k p := sourcePartner_of_mem k hq
  have hg := p.1.2
  change GoodPair k (p.1.1.1.1,p.1.1.1.2) at hg
  simp only [RankPairRelation,signedCriticalFiber,mem_ofPred_eq] at hp
  rw [hf,hz,hξ] at hp
  rw [hf,hξ] at hg
  rw [hr]
  exact ⟨hg,hp.1.2,hp.2.1.2,hp.2.1.1,hp.2.2.2⟩

lemma sourcePartner_injOn_fiber {k : ℝ} (hk : 0 < k) (f : DiskFamily)
    {z w : UpperHalfPlane} (hz : (f,z) ∈ sourcePairingDomain k)
    (hw : (f,w) ∈ sourcePairingDomain k)
    (hG : criticalMap k (halfPlaneFunction f) z = criticalMap k (halfPlaneFunction f) w)
    (he : sourcePartner k (f,z) = sourcePartner k (f,w)) : z = w := by
  let p := sourcePair k ⟨(f,z),hz⟩
  let q := sourcePair k ⟨(f,w),hw⟩
  have hp := sourcePair_apply k ⟨(f,z),hz⟩
  have hq := sourcePair_apply k ⟨(f,w),hw⟩
  have hpf : p.1.1.1.1 = f := congrArg Prod.fst hp
  have hqf : q.1.1.1.1 = f := congrArg Prod.fst hq
  have hpz : p.1.1.2 = z := congrArg Prod.snd hp
  have hqw : q.1.1.2 = w := congrArg Prod.snd hq
  have hξ : p.1.1.1.2 = q.1.1.1.2 := by
    rw [← (availableRankPartner_spec k p).1.1,← (availableRankPartner_spec k q).1.1,
      hpf,hqf,hpz,hqw,hG]
  have hf := Prod.ext (hpf.trans hqf.symm) hξ
  have he' : availableRankPartner k p = availableRankPartner k q := by
    simpa only [sourcePartner_of_mem k hz,sourcePartner_of_mem k hw,sourcePartnerOn] using he
  have h := availableRankPartner_injOn_fiber hk hf he'
  exact hpz.symm.trans (h.trans hqw)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.PairingCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma sourcePartner_eq_available (k : ℝ) {f : DiskFamily} {ξ : ℂ} {z : UpperHalfPlane}
    (hg : GoodPair k (f,ξ))
    (hp : (⟨((f,ξ),z),hg⟩ : RankParameters k) ∈ rankPairingDomain k) :
    sourcePartner k (f,z) = availableRankPartner k ⟨⟨((f,ξ),z),hg⟩,hp⟩ := by
  let p : AvailableRankPair k := ⟨⟨((f,ξ),z),hg⟩,hp⟩
  have hq : (f,z) ∈ sourcePairingDomain k := ⟨p,rfl⟩
  rw [sourcePartner_of_mem k hq]
  unfold sourcePartnerOn
  congr 1
  exact availableSource_injective (sourcePair_apply k ⟨(f,z),hq⟩)

lemma sourcePairingDomain_rebase_iff (k : ℝ) (f : DiskFamily) (t w : UpperHalfPlane) :
    (rebase f t,w) ∈ sourcePairingDomain k ↔ (f,affineProduct t w) ∈ sourcePairingDomain k := by
  rw [sourcePairingDomain_iff,sourcePairingDomain_iff,criticalMap_rebase]
  constructor
  · rintro ⟨hg',hp⟩
    have hg := (goodPair_rebase_iff k f _ t).mp hg'
    exact ⟨hg,(rankPairingDomain_rebase_iff hg t w).mp hp⟩
  · rintro ⟨hg,hp⟩
    exact ⟨goodPair_rebase hg t,(rankPairingDomain_rebase_iff hg t w).mpr hp⟩

lemma sourcePartner_rebase {k : ℝ} (hk : 0 < k) (f : DiskFamily) (t w : UpperHalfPlane)
    (hp : (rebase f t,w) ∈ sourcePairingDomain k) :
    sourcePartner k (f,affineProduct t w) = affineProduct t (sourcePartner k (rebase f t,w)) := by
  obtain ⟨hg',hp'⟩ := (sourcePairingDomain_iff k _ _).mp hp
  rw [criticalMap_rebase] at hg'
  have hg := (goodPair_rebase_iff k f _ t).mp hg'
  have hpr : (⟨((rebase f t,targetRebase f t (criticalMap k (halfPlaneFunction f) (affineProduct t w))),w),
      goodPair_rebase hg t⟩ : RankParameters k) ∈ rankPairingDomain k := by
    simpa only [criticalMap_rebase] using hp'
  rw [sourcePartner_eq_available k (goodPair_rebase hg t) hpr,
    sourcePartner_eq_available k hg ((rankPairingDomain_rebase_iff hg t w).mp hpr)]
  exact availableRankPartner_rebase hk hg t w hpr

lemma measurable_partnerRatio {k : ℝ} (hk : 0 < k) : Measurable (partnerRatio k) := by
  have hnum : Measurable (fun q : DiskFamily × UpperHalfPlane =>
      criticalHeight k (halfPlaneFunction q.1) (sourcePartner k q)) :=
    (continuous_criticalHeight k).measurable.comp (measurable_fst.prodMk (measurable_sourcePartner hk))
  exact ((hnum.div (continuous_criticalHeight k).measurable).pow_const 3).piecewise
    (measurableSet_sourcePairingDomain hk) measurable_const

lemma partnerRatio_gt_one {k : ℝ} (hk : 0 < k) {q : DiskFamily × UpperHalfPlane}
    (hq : q ∈ sourcePairingDomain k) : 1 < partnerRatio k q := by
  have hs := sourcePartner_spec k hq
  have hp : 0 < criticalHeight k (halfPlaneFunction q.1) q.2 := criticalHeight_pos hk q.2.im_pos (halfPlaneFunction_deriv_ne_zero q.1 q.2.im_pos)
  rw [partnerRatio,ite_eq_left hq]
  have hd : 1 < criticalHeight k (halfPlaneFunction q.1) (sourcePartner k q) /
      criticalHeight k (halfPlaneFunction q.1) q.2 := (one_lt_div hp).mpr hs.2.2.2.2
  exact one_lt_pow₀ hd (by norm_num)

lemma partnerRatio_nonneg {k : ℝ} (hk : 0 < k) (q : DiskFamily × UpperHalfPlane) : 0 ≤ partnerRatio k q := by
  classical
  by_cases hq : q ∈ sourcePairingDomain k
  · exact (partnerRatio_gt_one hk hq).le.trans' (by norm_num)
  · simp only [partnerRatio,ite_eq_right hq,le_refl]

lemma partnerRatio_rebase {k : ℝ} (hk : 0 < k) (f : DiskFamily) (t w : UpperHalfPlane) :
    partnerRatio k (rebase f t,w) = partnerRatio k (f,affineProduct t w) := by
  classical
  by_cases hp : (rebase f t,w) ∈ sourcePairingDomain k
  · have hp' := (sourcePairingDomain_rebase_iff k f t w).mp hp
    rw [partnerRatio,ite_eq_left hp,partnerRatio,ite_eq_left hp']
    simp only
    rw [criticalHeight_rebase,criticalHeight_rebase,sourcePartner_rebase hk f t w hp]
    congr 1
    exact mul_div_mul_left _ _ (heightRebaseScale_pos k f t).ne'
  · have hp' : (f,affineProduct t w) ∉ sourcePairingDomain k :=
      fun h => hp ((sourcePairingDomain_rebase_iff k f t w).mpr h)
    simp only [partnerRatio,ite_eq_right hp,ite_eq_right hp']

lemma measurableSet_truncatedPairingDomain {k : ℝ} (hk : 0 < k) (N : ℝ) :
    MeasurableSet (truncatedPairingDomain k N) := by
  have hR := measurable_sourcePartner hk
  have hi := (UpperHalfPlane.continuous_im.measurable.comp hR).div
    (UpperHalfPlane.continuous_im.measurable.comp measurable_snd)
  have hr := ((UpperHalfPlane.continuous_re.measurable.comp hR).sub
    (UpperHalfPlane.continuous_re.measurable.comp measurable_snd)).abs
  exact (measurableSet_sourcePairingDomain hk).inter ((measurableSet_le measurable_const hi).inter
    ((measurableSet_le hi measurable_const).inter (measurableSet_le hr
      (measurable_const.mul (UpperHalfPlane.continuous_im.measurable.comp measurable_snd)))))

lemma truncatedPairingDomain_rebase {k : ℝ} (hk : 0 < k) (N : ℝ)
    (f : DiskFamily) (t w : UpperHalfPlane) :
    (rebase f t,w) ∈ truncatedPairingDomain k N ↔
      (f,affineProduct t w) ∈ truncatedPairingDomain k N := by
  by_cases hp : (rebase f t,w) ∈ sourcePairingDomain k
  · have hp' := (sourcePairingDomain_rebase_iff k f t w).mp hp
    simp only [truncatedPairingDomain,mem_ofPred_eq,hp,hp',true_and]
    rw [sourcePartner_rebase hk f t w hp]
    simp only [affineProduct_im,affineProduct_re]
    rw [mul_div_mul_left _ _ t.im_ne_zero]
    have he : t.re+t.im*(sourcePartner k (rebase f t,w)).re-(t.re+t.im*w.re) =
        t.im*((sourcePartner k (rebase f t,w)).re-w.re) := by ring
    rw [he,abs_mul,abs_of_pos t.im_pos]
    have heN : N*(t.im*w.im) = t.im*(N*w.im) := by ring
    rw [heN,mul_le_mul_iff_right₀ t.im_pos]
  · have hp' : (f,affineProduct t w) ∉ sourcePairingDomain k :=
      fun h => hp ((sourcePairingDomain_rebase_iff k f t w).mpr h)
    simp only [truncatedPairingDomain,mem_ofPred_eq,hp,hp',false_and]

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.FiberSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory
open scoped ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma fiberSum_le_of_injection {X Y : Type*} {G : X → Y} {s t : Set X}
    {h q : X → ℝ≥0∞} (R : s → X) (hR : Function.Injective R)
    (hRt : ∀ z, R z ∈ t) (hG : ∀ z, G (R z) = G z)
    (hw : ∀ z : s, h z ≤ q (R z)) (ξ : Y) :
    fiberSum G s h ξ ≤ fiberSum G t q ξ := by
  let r : {z | z ∈ s ∧ G z = ξ} → {z | z ∈ t ∧ G z = ξ} :=
    fun z => ⟨R ⟨z.1,z.2.1⟩,hRt _,(hG _).trans z.2.2⟩
  have hr : Function.Injective r := by
    intro z w he
    apply Subtype.ext
    have e : (⟨z.val,z.property.1⟩ : s) = ⟨w.val,w.property.1⟩ :=
      hR (congrArg Subtype.val he)
    exact congrArg (fun a : s => (a : X)) e
  exact Summable.tsum_le_tsum_of_inj r hr (fun _ _ => bot_le) (fun z => hw ⟨z.1,z.2.1⟩)
    ENNReal.summable ENNReal.summable

lemma fiberSum_iUnion {X Y I : Type*} (G : X → Y) (s : I → Set X) (h : X → ℝ≥0∞)
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (ξ : Y) :
    fiberSum G (⋃ i, s i) h ξ = ∑' i, fiberSum G (s i) h ξ := by
  unfold fiberSum
  have he : {z | z ∈ ⋃ i, s i ∧ G z = ξ} = ⋃ i, {z | z ∈ s i ∧ G z = ξ} := by
    ext z
    simp only [mem_ofPred_eq,mem_iUnion]
    tauto
  rw [he]
  apply ENNReal.tsum_biUnion
  intro i _ j _ hij
  exact (hd hij).mono (fun _ hz => hz.1) (fun _ hz => hz.1)

lemma fiberSum_eq_single {X Y : Type*} {G : X → Y} {s : Set X} {h : X → ℝ≥0∞}
    (hi : InjOn G s) {z : X} (hz : z ∈ s) : fiberSum G s h (G z) = h z := by
  unfold fiberSum
  apply tsum_eq_single (⟨z,hz,rfl⟩ : {w | w ∈ s ∧ G w = G z})
  intro w hw
  exact False.elim (hw (Subtype.ext (hi w.2.1 hz w.2.2)))

lemma fiberSum_eq_zero_of_not_mem_image {X Y : Type*} {G : X → Y} {s : Set X}
    {h : X → ℝ≥0∞} {ξ : Y} (hξ : ξ ∉ G '' s) : fiberSum G s h ξ = 0 := by
  have : IsEmpty {z | z ∈ s ∧ G z = ξ} := ⟨fun z => hξ ⟨z,z.2.1,z.2.2⟩⟩
  simp [fiberSum]

lemma fiberSum_eq_indicator_inverse {X Y : Type*} {G : X → Y} {s : Set X}
    (hi : InjOn G s) (h : X → ℝ≥0∞) (φ : Y → X) (hφ : ∀ z ∈ s, φ (G z) = z) :
    fiberSum G s h = (G '' s).indicator (fun ξ => h (φ ξ)) := by
  classical
  funext ξ
  by_cases hξ : ξ ∈ G '' s
  · obtain ⟨z,hz,rfl⟩ := hξ
    rw [fiberSum_eq_single hi hz,indicator_of_mem (mem_image_of_mem G hz),hφ z hz]
  · rw [fiberSum_eq_zero_of_not_mem_image hξ,indicator_of_notMem hξ]

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.AreaTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Filter Function
open scoped ENNReal Topology
namespace StrictInverseFirstPower
noncomputable section

lemma chart_measurable_fiberSum {G : ℂ → ℂ} (e : OpenPartialHomeomorph ℂ ℂ)
    (he : (e : ℂ → ℂ) = G) {s : Set ℂ} (hs : MeasurableSet s) (hse : s ⊆ e.source)
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) : Measurable (fiberSum G s h) := by
  classical
  have him : MeasurableSet (G '' s) := by
    rw [← he]
    exact hs.image_of_continuousOn_injOn (e.continuousOn.mono hse) (e.injOn.mono hse)
  let φ := e.target.piecewise e.symm (fun _ => 0)
  have hφ : Measurable φ := e.continuousOn_symm.measurable_piecewise
    continuousOn_const e.open_target.measurableSet
  have hinv : ∀ z ∈ s, φ (G z) = z := by
    intro z hz
    rw [show G z = e z from congrFun he.symm z]
    simp only [φ, piecewise_eq_of_mem _ _ _ (e.map_source (hse hz)), e.left_inv (hse hz)]
  rw [fiberSum_eq_indicator_inverse (he ▸ e.injOn.mono hse) h φ hinv]
  exact (hh.comp hφ).indicator him

lemma chart_area_formula {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) (e : OpenPartialHomeomorph ℂ ℂ)
    (he : (e : ℂ → ℂ) = G) {s : Set ℂ} (hs : MeasurableSet s)
    (hsU : s ⊆ U) (hse : s ⊆ e.source) (h : ℂ → ℝ≥0∞) :
    ∫⁻ ξ, fiberSum G s h ξ =
      ∫⁻ z in s, ENNReal.ofReal |(fderiv ℝ G z).det| * h z := by
  classical
  have hinv : ∀ z ∈ s, e.symm (G z) = z := by
    intro z hz
    rw [← he]
    exact e.left_inv (hse hz)
  have hi : InjOn G s := he ▸ e.injOn.mono hse
  have hf : ∀ z ∈ s, HasFDerivWithinAt G (fderiv ℝ G z) s z := by
    intro z hz
    exact ((hG.contDiffAt (hU.mem_nhds (hsU hz))).differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt
  have him := measurable_image_of_fderivWithin hs hf hi
  rw [fiberSum_eq_indicator_inverse hi h e.symm hinv,lintegral_indicator him]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hf hi]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hs] with z hz
  rw [hinv z hz]

lemma regular_area_formula {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) {s : Set ℂ} (hs : MeasurableSet s)
    (hsR : s ⊆ {z ∈ U | (fderiv ℝ G z).det ≠ 0})
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) :
    Measurable (fiberSum G s h) ∧
      ∫⁻ ξ, fiberSum G s h ξ = ∫⁻ z in s, ENNReal.ofReal |(fderiv ℝ G z).det| * h z := by
  classical
  obtain ⟨C,hC,hchart,hcov⟩ := countable_regular_inverse_charts hU hG
  by_cases hn : C.Nonempty
  · obtain ⟨e,he⟩ := hC.exists_eq_range hn
    have hem (n : ℕ) : e n ∈ C := he ▸ mem_range_self n
    let A (n : ℕ) := s ∩ (e n).source
    let B := disjointed A
    have hmA (n : ℕ) : MeasurableSet (A n) := hs.inter (e n).open_source.measurableSet
    have hmB (n : ℕ) : MeasurableSet (B n) := MeasurableSet.disjointed hmA n
    have hbA (n : ℕ) : B n ⊆ A n := disjointed_le A n
    have hbE (n : ℕ) : B n ⊆ (e n).source := (hbA n).trans inter_subset_right
    have hbS (n : ℕ) : B n ⊆ s := (hbA n).trans inter_subset_left
    have hbs : (⋃ n, B n) = s := by
      rw [iUnion_disjointed]
      apply Subset.antisymm
      · exact iUnion_subset (fun n => inter_subset_left)
      · intro z hz
        obtain ⟨c,hc,hzc⟩ := mem_iUnion₂.mp (hcov (hsR hz))
        obtain ⟨n,rfl⟩ := he ▸ hc
        exact mem_iUnion.mpr ⟨n,hz,hzc⟩
    have hmb (n : ℕ) : Measurable (fiberSum G (B n) h) :=
      chart_measurable_fiberSum (e n) (hchart _ (hem n)).1 (hmB n) (hbE n) hh
    have heq : fiberSum G s h = fun ξ => ∑' n, fiberSum G (B n) h ξ := by
      funext ξ
      rw [← hbs]
      exact fiberSum_iUnion G B h (disjoint_disjointed A) ξ
    refine ⟨heq ▸ .tsum hmb,?_⟩
    rw [heq,lintegral_tsum (fun n => (hmb n).aemeasurable)]
    simp_rw [chart_area_formula hU hG _ (hchart _ (hem _)).1 (hmB _)
      ((hbS _).trans (fun z hz => (hsR hz).1)) (hbE _)]
    rw [← lintegral_iUnion (fun n => hmB n) (disjoint_disjointed A),hbs]
  · have hs0 : s = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨e,he,_⟩ := mem_iUnion₂.mp (hcov (hsR hz))
      exact hn ⟨e,he⟩
    subst s
    have he : fiberSum G ∅ h = 0 := by ext ξ; simp [fiberSum]
    rw [he]
    exact ⟨measurable_const, by simp⟩

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma continuous_unsignedTargetWeight (β : ℝ) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => unsignedTargetWeight β p.1 p.2) := by
  exact ENNReal.continuous_ofReal.comp (((UpperHalfPlane.continuous_im.comp continuous_snd).rpow_const
    (fun p => Or.inl p.2.im_ne_zero)).mul (continuous_halfPlaneQ.norm.pow 3))

lemma continuous_jacobianPart (k : ℝ) (positive : Bool) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => jacobianPart k p.1 positive p.2) := by
  cases positive
  · exact (continuous_jacobianExpression_upper k).neg.max continuous_const
  · exact (continuous_jacobianExpression_upper k).max continuous_const

lemma continuous_sourceMassDensity (β k : ℝ) (positive : Bool) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => sourceMassDensity β k p.1 positive p.2) := by
  exact ENNReal.continuous_ofReal.comp ((((UpperHalfPlane.continuous_im.comp continuous_snd).rpow_const
    (fun p => Or.inl p.2.im_ne_zero)).mul continuous_halfPlaneQ.norm).mul
      (continuous_jacobianPart k positive))

lemma measurableSet_signedJacobianLocus (k : ℝ) (f : DiskFamily) (positive : Bool) :
    MeasurableSet (signedJacobianLocus k f positive) := by
  have hc : Continuous (fun z : UpperHalfPlane => (f,z)) := continuous_const.prodMk continuous_id
  have hm := (continuous_jacobianExpression_upper k).comp hc
  have hs : MeasurableSet {z : UpperHalfPlane | if positive then
      0 < jacobianExpression k (halfPlaneFunction f) z else
      jacobianExpression k (halfPlaneFunction f) z < 0} := by
    cases positive
    · change MeasurableSet {z : UpperHalfPlane | jacobianExpression k (halfPlaneFunction f) z < 0}
      exact measurableSet_lt hm.measurable measurable_const
    · change MeasurableSet {z : UpperHalfPlane | 0 < jacobianExpression k (halfPlaneFunction f) z}
      exact measurableSet_lt measurable_const hm.measurable
  have he : signedJacobianLocus k f positive = UpperHalfPlane.coe '' {z : UpperHalfPlane | if positive then
      0 < jacobianExpression k (halfPlaneFunction f) z else
      jacobianExpression k (halfPlaneFunction f) z < 0} := by
    ext z
    constructor
    · intro hz
      refine ⟨⟨z,hz.1⟩,?_,rfl⟩
      exact hz.2
    · rintro ⟨w,hw,rfl⟩
      exact ⟨w.im_pos,hw⟩
  rw [he]
  exact UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr hs

lemma criticalMap_det_eq (k : ℝ) (hk : k ≠ 0) (f : DiskFamily) {z : ℂ} (hz : 0 < z.im) :
    (fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det =
      ‖deriv (halfPlaneFunction f) z‖^2 * jacobianExpression k (halfPlaneFunction f) z := by
  have ha := (halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz)
  have he := normalizedJacobian_eq hk ha.differentiableAt ha.deriv.differentiableAt
    (halfPlaneFunction_deriv_ne_zero f hz)
  exact (div_eq_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr
    (halfPlaneFunction_deriv_ne_zero f hz)))).mp he |>.trans (mul_comm _ _)

lemma sourceMassDensity_eq_targetWeight_det {β k : ℝ} (hk : k ≠ 0) (f : DiskFamily)
    (positive : Bool) {z : ℂ} (hz : z ∈ signedJacobianLocus k f positive) :
    sourceMassDensity β k f positive ⟨z,hz.1⟩ =
      ENNReal.ofReal |(fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det| *
        unsignedTargetWeight β f ⟨z,hz.1⟩ := by
  have hJ : jacobianPart k f positive ⟨z,hz.1⟩ = |jacobianExpression k (halfPlaneFunction f) z| := by
    cases positive
    · simp only [signedJacobianLocus,Bool.false_eq_true,↓reduceIte,mem_ofPred_eq] at hz
      simp only [jacobianPart,Bool.false_eq_true,↓reduceIte,max_eq_left (neg_nonneg.mpr hz.2.le),
        abs_of_neg hz.2]
    · simp only [signedJacobianLocus,↓reduceIte,mem_ofPred_eq] at hz
      simp only [jacobianPart,↓reduceIte,max_eq_left hz.2.le,abs_of_pos hz.2]
  have hd : ‖deriv (halfPlaneFunction f) z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (halfPlaneFunction_deriv_ne_zero f hz.1)
  rw [sourceMassDensity,unsignedTargetWeight,hJ,criticalMap_det_eq k hk f hz.1,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  simp only [halfPlaneQ,norm_inv,abs_mul,abs_pow,abs_norm]
  field_simp

lemma sourceMassDensity_zero_of_not_sign {β k : ℝ} (f : DiskFamily) (positive : Bool)
    (z : UpperHalfPlane) (hz : (z:ℂ) ∉ signedJacobianLocus k f positive) :
    sourceMassDensity β k f positive z = 0 := by
  have hp : jacobianPart k f positive z = 0 := by
    cases positive
    · have hJ : 0 ≤ jacobianExpression k (halfPlaneFunction f) z := by
        simpa only [signedJacobianLocus,mem_ofPred_eq,Bool.false_eq_true,↓reduceIte,
          UpperHalfPlane.coe_im, and_iff_right z.im_pos,not_lt] using hz
      exact max_eq_right (neg_nonpos.mpr hJ)
    · have hJ : jacobianExpression k (halfPlaneFunction f) z ≤ 0 := by
        simpa only [signedJacobianLocus,mem_ofPred_eq,↓reduceIte,
          UpperHalfPlane.coe_im, and_iff_right z.im_pos,not_lt] using hz
      exact max_eq_right hJ
  simp [sourceMassDensity,hp]

lemma source_area_formula {β k : ℝ} (hk : k ≠ 0) (f : DiskFamily) (positive : Bool)
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ z in {z : ℂ | 0 < z.im}, h z * sourceMassDensity β k f positive (halfPlaneProjection z)) =
      ∫⁻ ξ, fiberSum (criticalMap k (halfPlaneFunction f)) (signedJacobianLocus k f positive)
        (fun z => h z * unsignedTargetWeight β f (halfPlaneProjection z)) ξ := by
  have hreg : signedJacobianLocus k f positive ⊆
      {z ∈ {z : ℂ | 0 < z.im} | (fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det ≠ 0} := by
    intro z hz
    refine ⟨hz.1, (not_congr (jacobianExpression_zero_iff k hk f hz.1)).mp ?_⟩
    cases positive
    · exact ne_of_lt hz.2
    · exact ne_of_gt hz.2
  have hG : ContDiffOn ℝ 1 (criticalMap k (halfPlaneFunction f)) {z : ℂ | 0 < z.im} := by
    intro z hz
    exact (criticalMap_contDiffAt k f hz).contDiffWithinAt.of_le (by norm_num)
  have ht : Measurable (fun z => h z * unsignedTargetWeight β f (halfPlaneProjection z)) := hh.mul
    ((continuous_unsignedTargetWeight β).measurable.comp (measurable_const.prodMk measurable_halfPlaneProjection))
  rw [(regular_area_formula isOpen_halfPlane hG (measurableSet_signedJacobianLocus k f positive) hreg ht).2]
  have he : (∫⁻ z in signedJacobianLocus k f positive,
      ENNReal.ofReal |(fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det| *
        (h z * unsignedTargetWeight β f (halfPlaneProjection z))) =
      ∫⁻ z in signedJacobianLocus k f positive,
        h z * sourceMassDensity β k f positive (halfPlaneProjection z) := by
    apply setLIntegral_congr_fun (measurableSet_signedJacobianLocus k f positive)
    intro z hz
    dsimp only
    rw [halfPlaneProjection_of_pos hz.1,sourceMassDensity_eq_targetWeight_det hk f positive hz]
    ring
  rw [he,← lintegral_indicator (measurableSet_signedJacobianLocus k f positive),
    ← lintegral_indicator isOpen_halfPlane.measurableSet]
  apply lintegral_congr
  intro z
  by_cases hz : 0 < z.im
  · rw [indicator_of_mem (show z ∈ {z : ℂ | 0 < z.im} from hz)]
    by_cases hs : z ∈ signedJacobianLocus k f positive
    · rw [indicator_of_mem hs]
    · rw [indicator_of_notMem hs,halfPlaneProjection_of_pos hz,
        sourceMassDensity_zero_of_not_sign f positive ⟨z,hz⟩ hs,mul_zero]
  · rw [indicator_of_notMem (show z ∉ {z : ℂ | 0 < z.im} from hz),
      indicator_of_notMem (show z ∉ signedJacobianLocus k f positive from fun hs => hz hs.1)]

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.LawDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma spatialWeight_eq (β : ℝ) (f : DiskFamily) (z : UpperHalfPlane) :
    spatialWeight β f z = ENNReal.ofReal (z.im^(β-1)) * (‖halfPlaneQ f z‖₊ : ℝ≥0∞) := by
  rw [spatialWeight,ENNReal.ofReal_mul (Real.rpow_nonneg z.im_pos.le _)]
  simp [enorm_eq_nnnorm]

lemma law_spatialWeight (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : AffineProbabilityLaw μ β) (z : UpperHalfPlane)
    {φ : DiskFamily → ℝ≥0∞} (hφ : Measurable φ) :
    (∫⁻ f, spatialWeight β f z * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
      ENNReal.ofReal (z.im⁻¹) * ∫⁻ f, φ f ∂(μ : Measure DiskFamily) := by
  simp only [spatialWeight_eq,mul_assoc]
  have hm : Measurable (fun f => (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * φ (rebase f z)) :=
    (measurable_Qnorm_fixed z).coe_nnreal_ennreal.mul (hφ.comp (measurable_rebase_fixed z))
  rw [lintegral_const_mul (μ := (μ : Measure DiskFamily)) (ENNReal.ofReal (z.im^(β-1))) hm,
    hlaw z φ hφ,← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg z.im_pos.le _),← Real.rpow_add z.im_pos]
  congr 1
  rw [show β-1+-β = -(1:ℝ) by ring,Real.rpow_neg_one]

lemma spatialWeight_jacobianPart (β k : ℝ) (f : DiskFamily) (positive : Bool) (z : UpperHalfPlane) :
    spatialWeight β f z * ENNReal.ofReal (jacobianPart k f positive z) =
      sourceMassDensity β k f positive z := by
  rw [spatialWeight,sourceMassDensity,
    ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg z.im_pos.le _) (norm_nonneg _))]

lemma jacobianPart_rebase (k : ℝ) (f : DiskFamily) (t w : UpperHalfPlane) (positive : Bool) :
    jacobianPart k (rebase f t) positive w = jacobianPart k f positive (affineProduct t w) := by
  simp only [jacobianPart,jacobianExpression_rebase,coe_affineProduct]

lemma law_sourceMassDensity (μ : ProbabilityMeasure DiskFamily) (β k : ℝ)
    (hlaw : AffineProbabilityLaw μ β) (positive : Bool)
    {H : DiskFamily × UpperHalfPlane → ℝ≥0∞} (hH : Measurable H)
    (hcov : ∀ f z, H (f,z) = H (rebase f z,UpperHalfPlane.I)) (z : UpperHalfPlane) :
    (∫⁻ f, sourceMassDensity β k f positive z * H (f,z) ∂(μ : Measure DiskFamily)) =
      ENNReal.ofReal (z.im⁻¹) * ∫⁻ f,
        ENNReal.ofReal (jacobianPart k f positive UpperHalfPlane.I) * H (f,UpperHalfPlane.I)
        ∂(μ : Measure DiskFamily) := by
  let φ : DiskFamily → ℝ≥0∞ := fun f =>
    ENNReal.ofReal (jacobianPart k f positive UpperHalfPlane.I) * H (f,UpperHalfPlane.I)
  have hφ : Measurable φ :=
    ((continuous_jacobianPart k positive).measurable.comp
      (measurable_id.prodMk measurable_const)).ennreal_ofReal.mul
      (hH.comp (measurable_id.prodMk measurable_const))
  have he (f : DiskFamily) : sourceMassDensity β k f positive z * H (f,z) =
      spatialWeight β f z * φ (rebase f z) := by
    rw [← spatialWeight_jacobianPart,hcov]
    simp only [φ,jacobianPart_rebase,affineProduct_I,mul_assoc]
  simp_rw [he]
  exact law_spatialWeight μ β hlaw z hφ

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.TransportBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma coe_upperArea_preserving : MeasurePreserving UpperHalfPlane.coe upperArea
    (volume.restrict {z : ℂ | 0 < z.im}) := by
  refine ⟨UpperHalfPlane.measurable_coe,?_⟩
  rw [UpperHalfPlane.measurableEmbedding_coe.map_comap,UpperHalfPlane.range_coe]

lemma upperArea_lintegral {h : UpperHalfPlane → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ z, h z ∂upperArea) = ∫⁻ z in {z : ℂ | 0 < z.im}, h (halfPlaneProjection z) := by
  have he := coe_upperArea_preserving.lintegral_comp (hh.comp measurable_halfPlaneProjection)
  have hp (z : UpperHalfPlane) : halfPlaneProjection z = z := by
    rw [halfPlaneProjection_of_pos z.im_pos]
  simpa only [Function.comp_apply,hp] using he

lemma upper_source_area_formula {β k : ℝ} (hk : k ≠ 0) (f : DiskFamily) (positive : Bool)
    {h : UpperHalfPlane → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ z, h z * sourceMassDensity β k f positive z ∂upperArea) =
      ∫⁻ ξ, fiberSum (criticalMap k (halfPlaneFunction f)) (signedJacobianLocus k f positive)
        (fun z => h (halfPlaneProjection z) * unsignedTargetWeight β f (halfPlaneProjection z)) ξ := by
  have hm : Measurable (fun z => h z * sourceMassDensity β k f positive z) :=
    hh.mul ((continuous_sourceMassDensity β k positive).measurable.comp
      (measurable_const.prodMk measurable_id))
  rw [upperArea_lintegral hm]
  exact source_area_formula hk f positive (hh.comp measurable_halfPlaneProjection)

lemma unsignedTargetWeight_height {β k : ℝ} (hk : k ≠ 0) (hβ : 3*(k-1)=β-1)
    (f : DiskFamily) (z : UpperHalfPlane) :
    unsignedTargetWeight β f z = ENNReal.ofReal ((criticalHeight k (halfPlaneFunction f) z / k)^3) := by
  unfold unsignedTargetWeight criticalHeight halfPlaneQ
  congr 1
  have hc : k*z.im^(k-1)*‖(deriv (halfPlaneFunction f) z)⁻¹‖/k =
      z.im^(k-1)*‖(deriv (halfPlaneFunction f) z)⁻¹‖ := by field_simp
  simp only [UpperHalfPlane.coe_im]
  rw [hc,mul_pow,← Real.rpow_mul_natCast z.im_pos.le (k-1) 3]
  norm_num only [Nat.cast_ofNat]
  rw [mul_comm (k-1) (3:ℝ),hβ]

lemma partnerRatio_weight {β k : ℝ} (hk : 0 < k) (hβ : 3*(k-1)=β-1)
    (f : DiskFamily) (z : UpperHalfPlane) (hz : (f,z) ∈ sourcePairingDomain k) :
    ENNReal.ofReal (partnerRatio k (f,z)) * unsignedTargetWeight β f z =
      unsignedTargetWeight β f (sourcePartner k (f,z)) := by
  rw [unsignedTargetWeight_height hk.ne' hβ,unsignedTargetWeight_height hk.ne' hβ,
    ← ENNReal.ofReal_mul (partnerRatio_nonneg hk _)]
  congr 1
  rw [partnerRatio,ite_eq_left hz]
  have hv := (criticalHeight_pos hk z.im_pos (halfPlaneFunction_deriv_ne_zero f z.im_pos)).ne'
  field_simp

lemma fiberSum_indicator {X Y : Type*} (G : X → Y) (s t : Set X) (h : X → ℝ≥0∞) (ξ : Y) :
    fiberSum G s (t.indicator h) ξ = fiberSum G (s ∩ t) h ξ := by
  classical
  unfold fiberSum
  rw [tsum_subtype,tsum_subtype]
  apply tsum_congr
  intro z
  by_cases hs : z∈s <;> by_cases ht : z∈t <;> by_cases hg : G z=ξ <;>
    simp [hs,ht,hg]

lemma sourcePartner_injectiveOn {k : ℝ} (hk : 0 < k) (f : DiskFamily) :
    InjOn (fun z => sourcePartner k (f,z)) {z | (f,z) ∈ sourcePairingDomain k} := by
  intro z hz w hw he
  apply sourcePartner_injOn_fiber hk f hz hw _ he
  rw [← (sourcePartner_spec k hz).2.2.2.1,← (sourcePartner_spec k hw).2.2.2.1]
  exact congrArg (fun w : UpperHalfPlane => criticalMap k (halfPlaneFunction f) w) he

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.NormalizedTargets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma expected_source_mass (μ : ProbabilityMeasure DiskFamily) (β k : ℝ)
    (hlaw : AffineProbabilityLaw μ β) (positive : Bool)
    {H : DiskFamily × UpperHalfPlane → ℝ≥0∞} (hH : Measurable H)
    (hcov : ∀ f z, H (f,z) = H (rebase f z,UpperHalfPlane.I)) (A : Set UpperHalfPlane) :
    (∫⁻ f, ∫⁻ z in A, sourceMassDensity β k f positive z * H (f,z) ∂upperArea
      ∂(μ : Measure DiskFamily)) =
      (∫⁻ z in A, ENNReal.ofReal (z.im⁻¹) ∂upperArea) *
        ∫⁻ f, ENNReal.ofReal (jacobianPart k f positive UpperHalfPlane.I) *
          H (f,UpperHalfPlane.I) ∂(μ : Measure DiskFamily) := by
  have hm := (continuous_sourceMassDensity β k positive).measurable.mul hH
  rw [lintegral_lintegral_swap hm.aemeasurable]
  simp_rw [law_sourceMassDensity μ β k hlaw positive hH hcov]
  exact lintegral_mul_const _ (UpperHalfPlane.continuous_im.inv₀
    (fun z => z.im_ne_zero)).measurable.ennreal_ofReal

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.TransportTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma measurable_transportTest {k : ℝ} (hk : 0 < k) (N : ℝ) :
    Measurable (transportTest k N) :=
  (measurable_partnerRatio hk).ennreal_ofReal.indicator (measurableSet_truncatedPairingDomain hk N)

lemma transportTest_rebase {k : ℝ} (hk : 0 < k) (N : ℝ) (f : DiskFamily) (z : UpperHalfPlane) :
    transportTest k N (f,z) = transportTest k N (rebase f z,UpperHalfPlane.I) := by
  classical
  unfold transportTest
  have he := truncatedPairingDomain_rebase hk N f z UpperHalfPlane.I
  rw [affineProduct_I] at he
  by_cases hq : (f,z)∈truncatedPairingDomain k N
  · rw [indicator_of_mem hq,indicator_of_mem (he.mpr hq),partnerRatio_rebase hk,
      affineProduct_I]
  · rw [indicator_of_notMem hq,indicator_of_notMem (fun hh=>hq (he.mp hh))]

lemma truncatedPairingDomain_mono {k N M : ℝ} (hN : 0 < N) (hNM : N ≤ M) :
    truncatedPairingDomain k N ⊆ truncatedPairingDomain k M := by
  intro q hq
  exact ⟨hq.1,(one_div_le_one_div_of_le hN hNM).trans hq.2.1,
    hq.2.2.1.trans hNM,hq.2.2.2.trans (mul_le_mul_of_nonneg_right hNM q.2.im_pos.le)⟩

lemma mem_truncatedPairingDomain_eventually {k : ℝ} {q : DiskFamily × UpperHalfPlane}
    (hq : q∈sourcePairingDomain k) :
    ∀ᶠ n : ℕ in atTop, q∈truncatedPairingDomain k (n+1) := by
  let r := (sourcePartner k q).im / q.2.im
  have hr : 0 < r := div_pos (sourcePartner k q).im_pos q.2.im_pos
  obtain ⟨N,hN⟩ := exists_nat_ge (max (1/r) (max r (|(sourcePartner k q).re-q.2.re|/q.2.im)))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n+1 := by exact_mod_cast (by omega : N≤n+1)
  have hn0 : (0 : ℝ) < n+1 := by positivity
  have h1 : 1/r ≤ n+1 := (le_max_left _ _).trans (hN.trans hNn)
  refine ⟨hq,?_,(le_max_left _ _).trans ((le_max_right _ _).trans (hN.trans hNn)),?_⟩
  · exact (div_le_iff₀ hn0).mpr (by nlinarith [(div_le_iff₀ hr).mp h1])
  · exact (div_le_iff₀ q.2.im_pos).mp ((le_max_right _ _).trans
      ((le_max_right _ _).trans (hN.trans hNn)))

lemma transportTest_nat_monotone {k : ℝ} (q : DiskFamily × UpperHalfPlane) :
    Monotone (fun n : ℕ => transportTest k (n+1) q) := by
  intro n m hnm
  apply indicator_le_indicator_of_subset (truncatedPairingDomain_mono (by positivity)
    (by exact_mod_cast Nat.succ_le_succ hnm))
  exact fun _ => bot_le

lemma iSup_transportTest {k : ℝ} (q : DiskFamily × UpperHalfPlane) :
    (⨆ n : ℕ,transportTest k (n+1) q)=ENNReal.ofReal (partnerRatio k q) := by
  classical
  by_cases hq : q∈sourcePairingDomain k
  · obtain ⟨n,hn⟩ := (mem_truncatedPairingDomain_eventually hq).exists
    apply le_antisymm
    · apply iSup_le
      intro m
      exact (indicator_le_self' (fun _ _ => bot_le)) q
    · rw [← indicator_of_mem hn (fun q => ENNReal.ofReal (partnerRatio k q))]
      exact le_iSup (fun n : ℕ=>transportTest k (n+1) q) n
  · have he : partnerRatio k q=0 := by simp [partnerRatio,hq]
    rw [he,ENNReal.ofReal_zero]
    apply le_antisymm _ bot_le
    apply iSup_le
    intro n
    exact le_of_eq (indicator_of_notMem (fun h=>hq h.1) _)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.TransportInjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma transport_fiber_inequality {β k N : ℝ} (hk : 0 < k) (hβ : 3*(k-1)=β-1)
    (f : DiskFamily) (A B : Set UpperHalfPlane)
    (hmap : ∀ z∈A, (f,z)∈truncatedPairingDomain k N → sourcePartner k (f,z)∈B) (ξ : ℂ) :
    fiberSum (criticalMap k (halfPlaneFunction f)) (signedJacobianLocus k f true)
      (fun z => A.indicator (fun w=>transportTest k N (f,w)) (halfPlaneProjection z) *
        unsignedTargetWeight β f (halfPlaneProjection z)) ξ ≤
    fiberSum (criticalMap k (halfPlaneFunction f)) (signedJacobianLocus k f false)
      (fun z => B.indicator (fun _=>1) (halfPlaneProjection z) *
        unsignedTargetWeight β f (halfPlaneProjection z)) ξ := by
  classical
  let T : Set ℂ := {z | halfPlaneProjection z∈A ∧
    (f,halfPlaneProjection z)∈truncatedPairingDomain k N}
  have he : (fun z => A.indicator (fun w=>transportTest k N (f,w)) (halfPlaneProjection z) *
      unsignedTargetWeight β f (halfPlaneProjection z)) =
      T.indicator (fun z => ENNReal.ofReal (partnerRatio k (f,halfPlaneProjection z)) *
        unsignedTargetWeight β f (halfPlaneProjection z)) := by
    funext z
    by_cases ha : halfPlaneProjection z∈A <;>
      by_cases hd : (f,halfPlaneProjection z)∈truncatedPairingDomain k N <;>
      simp [T,transportTest,ha,hd]
  rw [he,fiberSum_indicator]
  let s := signedJacobianLocus k f true ∩ T
  let R : s → ℂ := fun z => sourcePartner k (f,halfPlaneProjection z.1)
  have hD (z : s) : (f,halfPlaneProjection z.1) ∈ sourcePairingDomain k := z.2.2.2.1
  have hproj (z : s) : (halfPlaneProjection z.1 : ℂ)=z.1 := by
    rw [halfPlaneProjection_of_pos z.2.1.1]
  have hRinj : Function.Injective R := by
    intro z w he
    have hp := (sourcePartner_injectiveOn hk f) (hD z) (hD w)
      (UpperHalfPlane.coe_injective he)
    apply Subtype.ext
    rw [← hproj z,← hproj w,hp]
  apply fiberSum_le_of_injection R hRinj
  · intro z
    have hs := sourcePartner_spec k (hD z)
    exact ⟨(sourcePartner k (f,halfPlaneProjection z.1)).im_pos,hs.2.2.1⟩
  · intro z
    have hs := (sourcePartner_spec k (hD z)).2.2.2.1
    dsimp [R]
    rw [hproj z] at hs
    exact hs
  · intro z
    have hb := hmap (halfPlaneProjection z.1) z.2.2.1 z.2.2.2
    dsimp [R]
    rw [halfPlaneProjection_coe,indicator_of_mem hb,one_mul,
      partnerRatio_weight hk hβ f _ (hD z)]

lemma transport_set_inequality {β k N : ℝ} (hk : 0 < k) (hβ : 3*(k-1)=β-1)
    (f : DiskFamily) {A B : Set UpperHalfPlane} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hmap : ∀ z∈A, (f,z)∈truncatedPairingDomain k N → sourcePartner k (f,z)∈B) :
    (∫⁻ z in A, sourceMassDensity β k f true z * transportTest k N (f,z) ∂upperArea) ≤
      ∫⁻ z in B, sourceMassDensity β k f false z ∂upperArea := by
  have hm : Measurable (fun z : UpperHalfPlane => transportTest k N (f,z)) :=
    (measurable_transportTest hk N).comp (measurable_const.prodMk measurable_id)
  have hL : (∫⁻ z in A, sourceMassDensity β k f true z * transportTest k N (f,z) ∂upperArea) =
      ∫⁻ z, A.indicator (fun w=>transportTest k N (f,w)) z * sourceMassDensity β k f true z ∂upperArea := by
    rw [← lintegral_indicator hA]
    apply lintegral_congr
    intro z
    by_cases hz : z∈A <;> simp [hz,mul_comm]
  have hR : (∫⁻ z in B, sourceMassDensity β k f false z ∂upperArea) =
      ∫⁻ z, B.indicator (fun _=>1) z * sourceMassDensity β k f false z ∂upperArea := by
    rw [← lintegral_indicator hB]
    apply lintegral_congr
    intro z
    by_cases hz : z∈B <;> simp [hz]
  rw [hL,hR,upper_source_area_formula hk.ne' f true (hm.indicator hA),
    upper_source_area_formula hk.ne' f false (measurable_const.indicator hB)]
  exact lintegral_mono (transport_fiber_inequality hk hβ f A B hmap)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.BoxTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma measurableSet_upperBox (S a b : ℝ) : MeasurableSet (upperBox S a b) :=
  UpperHalfPlane.measurable_coe (measurableSet_complexBox S a b)

lemma lintegral_upperBox_inv {S a b : ℝ} (hS : 0 ≤ S) (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ z in upperBox S a b, ENNReal.ofReal (z.im⁻¹) ∂upperArea) =
      ENNReal.ofReal (2*S*(Real.log b-Real.log a)) := by
  have hm : Measurable (fun z : UpperHalfPlane => ENNReal.ofReal (z.im⁻¹)) :=
    UpperHalfPlane.continuous_im.measurable.inv.ennreal_ofReal
  rw [← lintegral_indicator (measurableSet_upperBox S a b),
    upperArea_lintegral (hm.indicator (measurableSet_upperBox S a b))]
  have he : (∫⁻ z in {z : ℂ | 0 < z.im},
      (upperBox S a b).indicator (fun w => ENNReal.ofReal (w.im⁻¹)) (halfPlaneProjection z)) =
      ∫⁻ z in {z : ℂ | 0 < z.im},
      (complexBox S a b).indicator (fun w => ENNReal.ofReal (w.im⁻¹)) z := by
    apply setLIntegral_congr_fun isOpen_halfPlane.measurableSet
    intro z hz
    dsimp only
    rw [halfPlaneProjection_of_pos hz]
    rfl
  rw [he,lintegral_indicator (measurableSet_complexBox S a b),
    Measure.restrict_restrict (measurableSet_complexBox S a b),inter_eq_left.mpr]
  · exact lintegral_complexBox_inv hS ha hab
  · intro z hz
    exact ha.trans_le hz.2.1

lemma partner_mem_expanded_box {k N S Y : ℝ} (hN : 1 ≤ N) (_hY : 1 ≤ Y)
    (f : DiskFamily) {z : UpperHalfPlane} (hz : z∈upperBox S 1 Y)
    (hD : (f,z)∈truncatedPairingDomain k N) :
    sourcePartner k (f,z)∈upperBox (S+N*Y) (1/N) (N*Y) := by
  change |(sourcePartner k (f,z)).re| ≤ S+N*Y ∧
    1/N ≤ (sourcePartner k (f,z)).im ∧ (sourcePartner k (f,z)).im ≤ N*Y
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  change |z.re| ≤ S ∧ 1 ≤ z.im ∧ z.im ≤ Y at hz
  have hylo := (le_div_iff₀ z.im_pos).mp hD.2.1
  have hyhi := (div_le_iff₀ z.im_pos).mp hD.2.2.1
  refine ⟨?_,?_,hyhi.trans (mul_le_mul_of_nonneg_left hz.2.2 hN0.le)⟩
  · calc
      |(sourcePartner k (f,z)).re| = |(sourcePartner k (f,z)).re-z.re+z.re| := by ring_nf
      _ ≤ |(sourcePartner k (f,z)).re-z.re| + |z.re| := abs_add_le _ _
      _ ≤ N*z.im+S := add_le_add hD.2.2.2 hz.1
      _ ≤ S+N*Y := by nlinarith [hz.2.2]
  · nlinarith [one_div_pos.mpr hN0]

lemma box_transport_expectation (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : AffineProbabilityLaw μ β) {k N S Y : ℝ} (hk : 0 < k)
    (hβ : 3*(k-1)=β-1) (hN : 1 ≤ N) (hS : 0 < S) (hY : 1 < Y) :
    ENNReal.ofReal (2*S*Real.log Y) *
      (∫⁻ f, ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I) *
        transportTest k N (f,UpperHalfPlane.I) ∂(μ : Measure DiskFamily)) ≤
      ENNReal.ofReal (2*(S+N*Y)*(Real.log Y+2*Real.log N)) *
        ∫⁻ f, ENNReal.ofReal (jacobianPart k f false UpperHalfPlane.I) ∂(μ : Measure DiskFamily) := by
  have hi := lintegral_mono (μ := (μ : Measure DiskFamily)) (fun f =>
    transport_set_inequality hk hβ f (measurableSet_upperBox S 1 Y)
      (measurableSet_upperBox (S+N*Y) (1/N) (N*Y))
      (fun _ hz hD => partner_mem_expanded_box hN hY.le f hz hD))
  have hR := expected_source_mass μ β k hlaw false (H := fun _ => 1)
    measurable_const (fun _ _ => rfl) (upperBox (S+N*Y) (1/N) (N*Y))
  simp only [mul_one] at hR
  rw [expected_source_mass μ β k hlaw true (measurable_transportTest hk N)
    (transportTest_rebase hk N),hR,lintegral_upperBox_inv hS.le zero_lt_one hY.le] at hi
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hY0 : 0 < Y := lt_trans zero_lt_one hY
  have hlo : 1/N ≤ N*Y := by
    apply (div_le_iff₀ hN0).mpr
    have hNY : 1 ≤ N*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hN) (sub_nonneg.mpr hY.le)]
    simpa using mul_le_mul hNY hN (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0≤N*Y)
  rw [lintegral_upperBox_inv (by positivity) (one_div_pos.mpr hN0) hlo,
    Real.log_one,sub_zero,Real.log_mul hN0.ne' hY0.ne',Real.log_div one_ne_zero hN0.ne',
    Real.log_one] at hi
  convert hi using 1
  congr 2
  ring

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.BoxSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace StrictInverseFirstPower
noncomputable section

lemma slope_le_of_all_positive {a b c : ℝ}
    (h : ∀ S : ℝ, 0 < S → S*a ≤ S*b+c) : a ≤ b := by
  by_contra hn
  have hp : 0 < a-b := sub_pos.mpr (lt_of_not_ge hn)
  let S := (|c|+1)/(a-b)
  have hS : 0 < S := div_pos (by positivity) hp
  have he : S*(a-b)=|c|+1 := div_mul_cancel₀ _ hp.ne'
  have hh := h S hS
  nlinarith [le_abs_self c]

lemma ennreal_box_slope {A d : ℝ≥0∞} (hd : d≠⊤) {N : ℝ} (hN : 1 ≤ N)
    (h : ∀ S Y : ℝ, 0 < S → 1 < Y →
      ENNReal.ofReal (2*S*Real.log Y)*A ≤
        ENNReal.ofReal (2*(S+N*Y)*(Real.log Y+2*Real.log N))*d) : A ≤ d := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hA : A ≠ ⊤ := by
    have hh := h 1 (Real.exp 1) zero_lt_one (Real.one_lt_exp_iff.mpr zero_lt_one)
    simp only [mul_one,Real.log_exp] at hh
    have hfin : ENNReal.ofReal (2 * (1+N*Real.exp 1)*(1+2*Real.log N))*d < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hd)
    have hx := hh.trans_lt hfin
    intro ha
    rw [ha,ENNReal.mul_top (by norm_num)] at hx
    exact (lt_irrefl ⊤) hx
  apply (ENNReal.toReal_le_toReal hA hd).mp
  apply slope_le_of_all_positive (c := 2*Real.log N*d.toReal)
  intro t ht
  have hin (S : ℝ) (hS : 0 < S) := h S (Real.exp t) hS (Real.one_lt_exp_iff.mpr ht)
  have hlin : t*A.toReal ≤ (t+2*Real.log N)*d.toReal := by
    apply slope_le_of_all_positive (c := N*Real.exp t*(t+2*Real.log N)*d.toReal)
    intro S hS
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd) (hin S hS)
    rw [ENNReal.toReal_mul,ENNReal.toReal_mul] at hh
    simp only [Real.log_exp] at hh
    rw [ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_ofReal (by positivity)] at hh
    nlinarith
  nlinarith

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.TransportLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma integrable_jacobianPart_base (μ : ProbabilityMeasure DiskFamily) (k : ℝ) (positive : Bool) :
    Integrable (fun f => jacobianPart k f positive UpperHalfPlane.I) (μ : Measure DiskFamily) :=
  ((continuous_jacobianPart k positive).comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma jacobianPart_nonneg (k : ℝ) (f : DiskFamily) (positive : Bool) (z : UpperHalfPlane) :
    0 ≤ jacobianPart k f positive z := le_max_right _ _

lemma lintegral_jacobianPart_base (μ : ProbabilityMeasure DiskFamily) (k : ℝ) (positive : Bool) :
    (∫⁻ f, ENNReal.ofReal (jacobianPart k f positive UpperHalfPlane.I) ∂(μ : Measure DiskFamily)) =
      ENNReal.ofReal (∫ f, jacobianPart k f positive UpperHalfPlane.I ∂(μ : Measure DiskFamily)) :=
  (ofReal_integral_eq_lintegral_ofReal (integrable_jacobianPart_base μ k positive)
    (Eventually.of_forall (fun f => jacobianPart_nonneg k f positive _))).symm

lemma truncated_transport_le (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : AffineProbabilityLaw μ β) {k N : ℝ} (hk : 0 < k)
    (hβ : 3*(k-1)=β-1) (hN : 1 ≤ N) :
    (∫⁻ f, ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I) *
      transportTest k N (f,UpperHalfPlane.I) ∂(μ : Measure DiskFamily)) ≤
      ∫⁻ f, ENNReal.ofReal (jacobianPart k f false UpperHalfPlane.I) ∂(μ : Measure DiskFamily) := by
  apply ennreal_box_slope (by rw [lintegral_jacobianPart_base]; exact ENNReal.ofReal_ne_top) hN
  intro S Y hS hY
  exact box_transport_expectation μ β hlaw hk hβ hN hS hY

lemma weighted_transport_le (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : AffineProbabilityLaw μ β) {k : ℝ} (hk : 0 < k) (hβ : 3*(k-1)=β-1) :
    (∫⁻ f, ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I) *
      ENNReal.ofReal (partnerRatio k (f,UpperHalfPlane.I)) ∂(μ : Measure DiskFamily)) ≤
      ∫⁻ f, ENNReal.ofReal (jacobianPart k f false UpperHalfPlane.I) ∂(μ : Measure DiskFamily) := by
  have hm (n : ℕ) : Measurable (fun f : DiskFamily =>
      ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I)*transportTest k (n+1) (f,UpperHalfPlane.I)) :=
    (((continuous_jacobianPart k true).measurable.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal).mul
      ((measurable_transportTest hk _).comp (measurable_id.prodMk measurable_const))
  have hmono : Monotone (fun n : ℕ => fun f : DiskFamily =>
      ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I)*transportTest k (n+1) (f,UpperHalfPlane.I)) := by
    intro n m hnm f
    exact mul_le_mul' le_rfl (transportTest_nat_monotone _ hnm)
  simp_rw [← iSup_transportTest (k := k),ENNReal.mul_iSup]
  rw [lintegral_iSup hm hmono]
  apply iSup_le
  intro n
  exact truncated_transport_le μ β hlaw hk hβ (by exact_mod_cast Nat.succ_pos n)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.StrictTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma transport_positive_le_negative (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hβ : 0 ≤ β) (hlaw : AffineProbabilityLaw μ β) :
    (∫⁻ f, ENNReal.ofReal (jacobianPart ((β+2)/3) f true UpperHalfPlane.I) ∂(μ : Measure DiskFamily)) ≤
      ∫⁻ f, ENNReal.ofReal (jacobianPart ((β+2)/3) f false UpperHalfPlane.I) ∂(μ : Measure DiskFamily) := by
  exact (lintegral_mono_ae (ae_base_positive_le_weighted μ β hβ hlaw)).trans
    (weighted_transport_le μ β hlaw (by linarith) (by ring))

lemma transport_equality_ae_zero (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hβ : 0 ≤ β) (hlaw : AffineProbabilityLaw μ β)
    (he : (∫⁻ f, ENNReal.ofReal (jacobianPart ((β+2)/3) f true UpperHalfPlane.I) ∂(μ : Measure DiskFamily)) =
      ∫⁻ f, ENNReal.ofReal (jacobianPart ((β+2)/3) f false UpperHalfPlane.I) ∂(μ : Measure DiskFamily)) :
    ∀ᵐ f ∂(μ : Measure DiskFamily), jacobianExpression ((β+2)/3) (halfPlaneFunction f) I = 0 := by
  let k := (β+2)/3
  have hk : 0 < k := by dsimp [k]; linarith
  have hfin : (∫⁻ f, ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I) ∂(μ : Measure DiskFamily)) ≠ ⊤ := by
    rw [lintegral_jacobianPart_base]
    exact ENNReal.ofReal_ne_top
  have hm : Measurable (fun f : DiskFamily => ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I) *
      ENNReal.ofReal (partnerRatio k (f,UpperHalfPlane.I))) :=
    (((continuous_jacobianPart k true).measurable.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal).mul
      (((measurable_partnerRatio hk).comp (measurable_id.prodMk measurable_const)).ennreal_ofReal)
  have ha := ae_eq_of_ae_le_of_lintegral_le (ae_base_positive_le_weighted μ β hβ hlaw) hfin
    hm.aemeasurable (he ▸ weighted_transport_le μ β hlaw hk (by ring))
  have hp : ∀ᵐ f ∂(μ : Measure DiskFamily), jacobianPart k f true UpperHalfPlane.I = 0 := by
    filter_upwards [ha,ae_bad_base_positive_zero μ β hβ hlaw] with f hf hb
    by_cases hD : (f,UpperHalfPlane.I)∈sourcePairingDomain k
    · have hc := partnerRatio_gt_one hk hD
      have hre := congrArg ENNReal.toReal hf
      rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (jacobianPart_nonneg k f true _),
        ENNReal.toReal_ofReal (partnerRatio_nonneg hk _)] at hre
      nlinarith [jacobianPart_nonneg k f true UpperHalfPlane.I]
    · exact hb hD
  have hnzero : (∫⁻ f, ENNReal.ofReal (jacobianPart k f false UpperHalfPlane.I) ∂(μ : Measure DiskFamily)) = 0 := by
    rw [← he]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hp] with f hf
    change ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I) = 0
    rw [hf,ENNReal.ofReal_zero]
  have hmn : Measurable (fun f : DiskFamily => ENNReal.ofReal (jacobianPart k f false UpperHalfPlane.I)) :=
    ((continuous_jacobianPart k false).measurable.comp
    (measurable_id.prodMk measurable_const)).ennreal_ofReal
  have hn := (lintegral_eq_zero_iff' hmn.aemeasurable).mp hnzero
  filter_upwards [hp,hn] with f hf hg
  have hnle := ENNReal.ofReal_eq_zero.mp hg
  change max (jacobianExpression k (halfPlaneFunction f) I) 0 = 0 at hf
  change max (-jacobianExpression k (halfPlaneFunction f) I) 0 ≤ 0 at hnle
  exact le_antisymm ((le_max_left _ _).trans hf.le) (by linarith [le_max_left (-jacobianExpression k (halfPlaneFunction f) I) 0])

lemma expected_jacobian_as_parts (μ : ProbabilityMeasure DiskFamily) (k : ℝ) :
    (∫ f, jacobianExpression k (halfPlaneFunction f) I ∂(μ : Measure DiskFamily)) =
      (∫ f, jacobianPart k f true UpperHalfPlane.I ∂(μ : Measure DiskFamily)) -
      ∫ f, jacobianPart k f false UpperHalfPlane.I ∂(μ : Measure DiskFamily) := by
  rw [← integral_sub (integrable_jacobianPart_base μ k true) (integrable_jacobianPart_base μ k false)]
  apply integral_congr_ae
  filter_upwards [] with f
  simp only [jacobianPart,Bool.false_eq_true,↓reduceIte,UpperHalfPlane.coe_I]
  by_cases h : 0 ≤ jacobianExpression k (halfPlaneFunction f) I
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
  · rw [max_eq_right (le_of_not_ge h), max_eq_left (neg_nonneg.mpr (le_of_not_ge h))]
    ring

theorem strict_weighted_transport (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hβ : 0 ≤ β) (hlaw : AffineProbabilityLaw μ β) :
    (∫ f, jacobianExpression ((β+2)/3) (halfPlaneFunction f) I ∂(μ : Measure DiskFamily)) ≤ 0 ∧
      ((∫ f, jacobianExpression ((β+2)/3) (halfPlaneFunction f) I ∂(μ : Measure DiskFamily)) = 0 →
        ∀ᵐ f ∂(μ : Measure DiskFamily), jacobianExpression ((β+2)/3) (halfPlaneFunction f) I = 0) := by
  have hN : 0 ≤ ∫ f, jacobianPart ((β+2)/3) f false UpperHalfPlane.I ∂(μ : Measure DiskFamily) :=
    integral_nonneg (fun f => jacobianPart_nonneg ((β+2)/3) f false UpperHalfPlane.I)
  have hi := transport_positive_le_negative μ β hβ hlaw
  simp only [lintegral_jacobianPart_base] at hi
  have hre := (ENNReal.ofReal_le_ofReal_iff hN).mp hi
  rw [expected_jacobian_as_parts]
  refine ⟨sub_nonpos.mpr hre,?_⟩
  intro he
  apply transport_equality_ae_zero μ β hβ hlaw
  simp only [lintegral_jacobianPart_base,sub_eq_zero.mp he]

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.EqualityBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex
open scoped Topology

namespace StrictInverseFirstPower

noncomputable section

theorem disk_decay_zero_at_zero {g : ℂ → ℂ} {C : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 1))
    (hbound : ∀ w ∈ ball (0 : ℂ) 1, ‖g w‖ ≤ C * (1 - ‖w‖ ^ 2)) :
    g 0 = 0 := by
  have h_circle (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
      ‖g 0‖ ≤ C * (1 - r ^ 2) := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (hg.diffContOnCl_ball (closedBall_subset_ball hr1))
    · intro w hw
      rw [frontier_ball _ hr.ne'] at hw
      have hw' : ‖w‖ = r := by simpa using hw
      simpa [hw'] using hbound w (by simpa [mem_ball, dist_zero_right, hw'] using hr1)
    · exact subset_closure (mem_ball_self hr)
  have ht : Tendsto (fun r : ℝ => C * (1 - r ^ 2)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun r : ℝ => C * (1 - r ^ 2)) := by fun_prop
    simpa using (hcont.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have hn : ‖g 0‖ ≤ 0 := ge_of_tendsto ht (by
    filter_upwards [eventually_mem_nhdsWithin,
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with r hr1 hr
    exact h_circle r hr hr1)
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

theorem halfPlane_linear_decay_zero {g : ℂ → ℂ} {C : ℝ}
    (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.im})
    (hbound : ∀ z : ℂ, 0 < z.im → ‖g z‖ ≤ C * z.im) : g I = 0 := by
  let h : ℂ → ℂ := fun w => (1 - w) ^ 2 * g (cayleyToHalfPlane w)
  have hh : DifferentiableOn ℂ h (ball 0 1) := by
    apply DifferentiableOn.mul
    · fun_prop
    · exact hg.comp cayley_differentiableOn (fun w hw => cayley_mem_halfPlane hw)
  have hb : ∀ w ∈ ball (0 : ℂ) 1, ‖h w‖ ≤ C * (1 - ‖w‖ ^ 2) := by
    intro w hw
    calc
      ‖h w‖ = ‖1 - w‖ ^ 2 * ‖g (cayleyToHalfPlane w)‖ := by
        simp [h, norm_pow]
      _ ≤ ‖1 - w‖ ^ 2 * (C * (cayleyToHalfPlane w).im) :=
        mul_le_mul_of_nonneg_left (hbound _ (cayley_mem_halfPlane hw)) (sq_nonneg _)
      _ = C * (1 - ‖w‖ ^ 2) := by
        rw [← cayley_im_mul_norm_sq (one_sub_ne_zero_of_mem_disk hw)]
        ring
  have hz := disk_decay_zero_at_zero hh hb
  simpa [h, cayleyToHalfPlane] using hz
theorem norm_logarithmicDerivative (F : ℂ → ℂ) {z : ℂ} (hz : 0 < z.im) :
    ‖logarithmicDerivative F z‖ = z.im * ‖deriv (deriv F) z / deriv F z‖ := by
  simp [logarithmicDerivative, abs_of_pos hz]

theorem jacobian_eq_zero_lower_bound {F : ℂ → ℂ} {z : ℂ}
    (h : jacobianExpression (3 / 4) F z = 0) :
    1 / 4 ≤ ‖logarithmicDerivative F z‖ := by
  have hq := Complex.re_le_norm (logarithmicDerivative F z)
  have hn := norm_nonneg (logarithmicDerivative F z)
  unfold jacobianExpression at h
  have he := (div_eq_zero_iff.mp h).resolve_right (by norm_num)
  norm_num at he
  by_contra hlt
  have hlt' : ‖logarithmicDerivative F z‖ < 1 / 4 := lt_of_not_ge hlt
  have hsq : ‖logarithmicDerivative F z‖ ^ 2 < (1 / 4 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hn (by norm_num)).mpr hlt'
  nlinarith

theorem no_identically_zero_jacobianExpression {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im}) :
    ¬ ∀ z : ℂ, 0 < z.im → jacobianExpression (3 / 4) F z = 0 := by
  intro hJ
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hF' := hF.deriv hopen
  have hF'' := hF'.deriv hopen
  let p : ℂ → ℂ := fun z => deriv (deriv F) z / deriv F z
  have hlow (z : ℂ) (hz : 0 < z.im) : 1 / 4 ≤ z.im * ‖p z‖ := by
    simpa only [norm_logarithmicDerivative F hz] using jacobian_eq_zero_lower_bound (hJ z hz)
  have hp (z : ℂ) (hz : 0 < z.im) : p z ≠ 0 := by
    intro h
    have := hlow z hz
    simp only [h, norm_zero, mul_zero] at this
    norm_num at this
  have hFne (z : ℂ) (hz : 0 < z.im) : deriv F z ≠ 0 := by
    intro he
    exact hp z hz (by simp [p, he])
  have hpd : DifferentiableOn ℂ p {z : ℂ | 0 < z.im} :=
    hF''.div hF' (fun z hz => hFne z hz)
  have hgd : DifferentiableOn ℂ (fun z => (p z)⁻¹) {z : ℂ | 0 < z.im} :=
    hpd.inv (fun z hz => hp z hz)
  have hgb (z : ℂ) (hz : 0 < z.im) : ‖(p z)⁻¹‖ ≤ 4 * z.im := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ (norm_pos_iff.mpr (hp z hz))]
    nlinarith [hlow z hz]
  have hgz := halfPlane_linear_decay_zero hgd hgb
  exact inv_ne_zero (hp I (by simp)) hgz

end

end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma continuous_jacobianExpression_fixed (k : ℝ) (z : UpperHalfPlane) :
    Continuous (fun f : DiskFamily => jacobianExpression k (halfPlaneFunction f) z) := by
  let w : HalfPlaneSet := ⟨(z : ℂ), z.im_pos⟩
  have hp : Continuous (fun f : DiskFamily => (f, w)) := continuous_id.prodMk continuous_const
  have hc := (continuous_jacobianExpression k).comp hp
  exact hc

lemma ae_jacobian_zero_everywhere (μ : ProbabilityMeasure DiskFamily) (β k : ℝ)
    (hlaw : ∀ (z : UpperHalfPlane) (φ : C(DiskFamily, ℝ)),
      (∫ f, ‖halfPlaneQ f z‖ * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
        z.im ^ (-β) * ∫ f, φ f ∂(μ : Measure DiskFamily))
    (hzero : ∀ᵐ f ∂(μ : Measure DiskFamily), jacobianExpression k (halfPlaneFunction f) I = 0)
    (z : UpperHalfPlane) :
    ∀ᵐ f ∂(μ : Measure DiskFamily), jacobianExpression k (halfPlaneFunction f) z = 0 := by
  let φ : C(DiskFamily, ℝ) := ⟨fun f => |jacobianExpression k (halfPlaneFunction f) I|,
    (continuous_jacobianExpression_fixed k UpperHalfPlane.I).abs⟩
  have hφ : ∫ f, φ f ∂(μ : Measure DiskFamily) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hzero] with f hf
    change |jacobianExpression k (halfPlaneFunction f) I| = 0
    rw [hf, abs_zero]
  have he := hlaw z φ
  simp only [hφ, mul_zero] at he
  have hfun (f : DiskFamily) : ‖halfPlaneQ f z‖ * φ (rebase f z) =
      ‖halfPlaneQ f z‖ * |jacobianExpression k (halfPlaneFunction f) z| := by
    change ‖halfPlaneQ f z‖ * |jacobianExpression k (halfPlaneFunction (rebase f z)) I| = _
    rw [jacobianExpression_rebase_I]
  have hc : Continuous (fun f : DiskFamily =>
      ‖halfPlaneQ f z‖ * |jacobianExpression k (halfPlaneFunction f) z|) :=
    ((continuous_halfPlaneQ.comp (continuous_id.prodMk continuous_const)).norm).mul
      (continuous_jacobianExpression_fixed k z).abs
  have ha := (integral_eq_zero_iff_of_nonneg
    (fun f => mul_nonneg (norm_nonneg _) (abs_nonneg _))
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp
      (by simpa only [hfun] using he)
  filter_upwards [ha] with f hf
  exact abs_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left
    (norm_ne_zero_iff.mpr (halfPlaneQ_ne_zero f z)))

theorem affine_law_not_ae_zero_jacobian (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : ∀ (z : UpperHalfPlane) (φ : C(DiskFamily, ℝ)),
      (∫ f, ‖halfPlaneQ f z‖ * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
        z.im ^ (-β) * ∫ f, φ f ∂(μ : Measure DiskFamily)) :
    ¬ ∀ᵐ f ∂(μ : Measure DiskFamily),
      jacobianExpression (3 / 4) (halfPlaneFunction f) I = 0 := by
  intro hzero
  obtain ⟨f, hf⟩ := (μ : Measure DiskFamily).nonempty_support (by
    intro h
    have hu := measure_univ (μ := (μ : Measure DiskFamily))
    simp [h] at hu)
  apply no_identically_zero_jacobianExpression (halfPlaneFunction_differentiableOn f)
  intro z hz
  exact (μ : Measure DiskFamily).support_subset_of_isClosed
    (isClosed_eq (continuous_jacobianExpression_fixed (3 / 4) ⟨z, hz⟩) continuous_const)
    (ae_jacobian_zero_everywhere μ β (3 / 4) hlaw hzero ⟨z, hz⟩) hf

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.DyadicGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

theorem dyadicExponent_lt_quarter : dyadicExponent < 1/4 := by
  by_contra hn
  have hβ : 1/4 ≤ dyadicExponent := le_of_not_gt hn
  have hβ0 : 0 ≤ dyadicExponent := dyadicExponent_nonneg
  obtain ⟨μ,hμ⟩ := exists_exact_affine_probability_continuous (by linarith : 0 < dyadicExponent)
  have hlaw : AffineProbabilityLaw μ dyadicExponent := by
    intro z φ hφ
    rw [← weightedRebaseMeasure_lintegral _ _ _ hφ,
      weightedRebaseMeasure_eq_smul μ dyadicExponent hμ z,lintegral_smul_measure]
    rfl
  let k := (dyadicExponent+2)/3
  have hk : k ≠ 0 := by dsimp [k]; linarith
  have hm := expected_normalizedJacobian_at_source_k μ dyadicExponent hβ
    (affine_real_law_mean_law μ dyadicExponent hμ)
  change k^2 * (∫ f, normalizedJacobian k (halfPlaneFunction f) I ∂(μ : Measure DiskFamily)) =
    ((4 * dyadicExponent - 1) * (dyadicExponent + 2)) / 9 at hm
  simp_rw [halfPlaneFunction_normalizedJacobian_I _ hk] at hm
  have ht := strict_weighted_transport μ dyadicExponent hβ0 hlaw
  have he : dyadicExponent = 1/4 := by
    have hle : k^2 * (∫ f, jacobianExpression k (halfPlaneFunction f) I ∂(μ : Measure DiskFamily)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) ht.1
    rw [hm] at hle
    nlinarith
  have k_eq : (dyadicExponent+2)/3 = (3/4:ℝ) := by rw [he]; norm_num
  have hz : (∫ f, jacobianExpression ((dyadicExponent+2)/3) (halfPlaneFunction f) I ∂(μ : Measure DiskFamily)) = 0 := by
    dsimp [k] at hm
    rw [he] at hm ⊢
    norm_num at hm ⊢
    linarith
  have hae := ht.2 hz
  rw [k_eq] at hae
  exact affine_law_not_ae_zero_jacobian μ dyadicExponent hμ hae

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.CircleBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma continuous_Q_slice (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => affineOperator (xyPoint x y hy) 1) :=
  (continuous_affineOperator_strong 1).comp (continuous_xyPoint continuous_id continuous_const _)

lemma horizontalQMean_apply (y : ℝ) (hy : 0 < y) (f : DiskFamily) :
    horizontalQMean y hy f = (1/2:ℝ) * ∫ x in (-1:ℝ)..1, ‖halfPlaneQ f (xyPoint x y hy)‖ := by
  have he := (ContinuousMap.evalCLM ℝ f).intervalIntegral_comp_comm (μ := volume)
    ((continuous_Q_slice y hy).intervalIntegrable (-1) 1)
  simp only [ContinuousMap.evalCLM_apply, affineOperator_apply,
    ContinuousMap.one_apply, mul_one] at he
  change (1/2:ℝ) * _ = _
  rw [← he]

lemma continuous_Q_slice_apply (f : DiskFamily) (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => ‖halfPlaneQ f (xyPoint x y hy)‖) := by
  have hh := (ContinuousMap.evalCLM ℝ f).continuous.comp (continuous_Q_slice y hy)
  change Continuous (fun x => (ContinuousMap.evalCLM ℝ f) (affineOperator (xyPoint x y hy) 1)) at hh
  simpa only [ContinuousMap.evalCLM_apply, affineOperator_apply, ContinuousMap.one_apply, mul_one] using hh

lemma dyadic_left_xy (x y : ℝ) (hy : 0 < y) :
    affineProduct dyadicLeft (xyPoint x y hy) =
      xyPoint ((1/2:ℝ)*x-1/2) (y/2) (half_pos hy) := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, dyadicLeft, xyPoint]
  ring

lemma dyadic_right_xy (x y : ℝ) (hy : 0 < y) :
    affineProduct dyadicRight (xyPoint x y hy) =
      xyPoint ((1/2:ℝ)*x+1/2) (y/2) (half_pos hy) := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, dyadicRight, xyPoint]
  ring

lemma horizontalQMean_half (y : ℝ) (hy : 0 < y) :
    horizontalQMean (y/2) (half_pos hy) = dyadicOperator (horizontalQMean y hy) := by
  let A : ℝ → C(DiskFamily, ℝ) := fun x => affineOperator (xyPoint x (y/2) (half_pos hy)) 1
  have hA : Continuous A := continuous_Q_slice (y/2) (half_pos hy)
  have hleft : (∫ x in (-1:ℝ)..1,
      affineOperator dyadicLeft (affineOperator (xyPoint x y hy) 1)) =
        (2:ℝ) • ∫ x in (-1:ℝ)..0, A x := by
    simp_rw [← mul_apply_eq_comp, affineOperator_mul, dyadic_left_xy]
    have hh := intervalIntegral.integral_comp_mul_add (a := (-1:ℝ)) (b := 1) A
      (by norm_num : (1/2:ℝ) ≠ 0) (-1/2)
    norm_num only at hh
    simpa only [sub_eq_add_neg] using hh
  have hright : (∫ x in (-1:ℝ)..1,
      affineOperator dyadicRight (affineOperator (xyPoint x y hy) 1)) =
        (2:ℝ) • ∫ x in (0:ℝ)..1, A x := by
    simp_rw [← mul_apply_eq_comp, affineOperator_mul, dyadic_right_xy]
    have hh := intervalIntegral.integral_comp_mul_add (a := (-1:ℝ)) (b := 1) A
      (by norm_num : (1/2:ℝ) ≠ 0) (1/2)
    norm_num only at hh
    simpa only [sub_eq_add_neg] using hh
  unfold horizontalQMean dyadicOperator
  rw [smul_apply, add_apply,
    map_smul, map_smul,
    ← (affineOperator dyadicLeft).intervalIntegral_comp_comm ((continuous_Q_slice y hy).intervalIntegrable _ _),
    ← (affineOperator dyadicRight).intervalIntegral_comp_comm ((continuous_Q_slice y hy).intervalIntegrable _ _),
    hleft, hright, smul_smul, smul_smul]
  norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals (hA.intervalIntegrable (-1) 0)
    (hA.intervalIntegrable 0 1)]
  exact smul_add _ _ _

lemma horizontalQMean_dyadic (n : ℕ) :
    horizontalQMean (dyadicHeight n) (dyadicHeight_pos n) =
      (dyadicOperator^n) (horizontalQMean 1 zero_lt_one) := by
  induction n with
  | zero => simp [dyadicHeight]
  | succ n ih =>
    simp only [dyadicHeight_succ]
    rw [horizontalQMean_half (dyadicHeight n) (dyadicHeight_pos n), ih, pow_succ', mul_apply_eq_comp]

lemma horizontalQMean_bound (n : ℕ) (f : DiskFamily) :
    (∫ x in (-1:ℝ)..1, ‖halfPlaneQ f (xyPoint x (dyadicHeight n) (dyadicHeight_pos n))‖) ≤
      (2 * ‖horizontalQMean 1 zero_lt_one‖) * ‖dyadicOperator^n‖ := by
  have hh := (horizontalQMean (dyadicHeight n) (dyadicHeight_pos n)).norm_coe_le_norm f
  have hb := (dyadicOperator^n).le_opNorm (horizontalQMean 1 zero_lt_one)
  rw [← horizontalQMean_dyadic] at hb
  rw [horizontalQMean_apply, Real.norm_eq_abs] at hh
  have hle := (le_abs_self _).trans (hh.trans hb)
  nlinarith

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma arcDenom_pos {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (t : ℝ) :
    0 < arcDenom r t := by
  have hh := mul_nonneg hr0 (show 0 ≤ 1+Real.cos t by linarith [Real.neg_one_le_cos t])
  have hs := sq_pos_of_pos (show 0 < 1-r by linarith)
  dsimp [arcDenom]
  nlinarith

lemma arcDenom_le_four {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1) (t : ℝ) :
    arcDenom r t ≤ 4 := by
  have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one t) hr0
  dsimp [arcDenom]
  nlinarith

lemma arcDenom_ge_one {r : ℝ} (hr0 : 0 ≤ r) {t : ℝ}
    (ht : t ∈ Icc (-(Real.pi/2)) (Real.pi/2)) : 1 ≤ arcDenom r t := by
  have hc : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], ht.2⟩
  have hh := mul_nonneg hr0 hc
  dsimp [arcDenom]
  nlinarith

lemma arcX_continuous {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) : Continuous (arcX r) := by
  exact ((continuous_const.mul continuous_const).mul Real.continuous_sin).div
    ((continuous_const.add ((continuous_const.mul continuous_const).mul Real.continuous_cos)).add
      continuous_const) (fun t => (arcDenom_pos hr0 hr t).ne')

lemma arcY_continuous {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) : Continuous (arcY r) := by
  exact continuous_const.div
    ((continuous_const.add ((continuous_const.mul continuous_const).mul Real.continuous_cos)).add
      continuous_const) (fun t => (arcDenom_pos hr0 hr t).ne')

lemma arcX_hasDerivAt {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (t : ℝ) :
    HasDerivAt (arcX r) (arcXDeriv r t) t := by
  have hn := (Real.hasDerivAt_sin t).const_mul (2*r)
  have hd := (((Real.hasDerivAt_cos t).const_mul (2*r)).const_add 1).add_const (r^2)
  have hh : HasDerivAt (arcX r)
      ((2*r*Real.cos t * arcDenom r t - 2*r*Real.sin t*(2*r*(-Real.sin t))) / (arcDenom r t)^2) t :=
    hn.div hd (arcDenom_pos hr0 hr t).ne'
  convert hh using 1
  dsimp [arcXDeriv,arcDenom]
  congr 1
  linear_combination -(4*r^2)*(Real.sin_sq_add_cos_sq t)

lemma arcXDeriv_continuous {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) : Continuous (arcXDeriv r) := by
  exact ((continuous_const.mul Real.continuous_cos).add continuous_const).div
    (((continuous_const.add ((continuous_const.mul continuous_const).mul Real.continuous_cos)).add
      continuous_const).pow 2) (fun t => pow_ne_zero _ (arcDenom_pos hr0 hr t).ne')

lemma arcXDeriv_lower {r : ℝ} (hr0 : 1/2 ≤ r) (hr : r < 1) {t : ℝ}
    (ht : t ∈ Icc (-(Real.pi/2)) (Real.pi/2)) : (1/16:ℝ) ≤ arcXDeriv r t := by
  have hrp : 0 ≤ r := by linarith
  have hc : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], ht.2⟩
  have hd := arcDenom_pos hrp hr t
  have hu := arcDenom_le_four hrp hr.le t
  have hn : 0 ≤ 2*r*(1+r^2)*Real.cos t := by positivity
  rw [arcXDeriv, le_div_iff₀ (sq_pos_of_pos hd)]
  nlinarith

lemma arcX_bounds {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) {t : ℝ}
    (ht : t ∈ Icc (-(Real.pi/2)) (Real.pi/2)) : -1 ≤ arcX r t ∧ arcX r t ≤ 1 := by
  have hd := arcDenom_pos hr0 hr t
  have hc : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], ht.2⟩
  have hc' := mul_nonneg hr0 hc
  have ha := mul_le_mul_of_nonneg_left (Real.sin_le_one t) hr0
  have hb := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin t) hr0
  constructor
  · rw [arcX, le_div_iff₀ hd]
    dsimp [arcDenom]
    nlinarith [sq_nonneg (1-r)]
  · rw [arcX, div_le_iff₀ hd]
    dsimp [arcDenom]
    nlinarith [sq_nonneg (1-r)]

lemma arcY_pos {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (t : ℝ) : 0 < arcY r t := by
  apply div_pos _ (arcDenom_pos hr0 hr t)
  nlinarith

lemma arcY_scale_bounds {r v : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hv : v ≤ 1-r) (hrv : 1-r ≤ 2*v) {t : ℝ}
    (ht : t ∈ Icc (-(Real.pi/2)) (Real.pi/2)) : v/4 ≤ arcY r t ∧ arcY r t ≤ 4*v := by
  have hvp : 0 < v := by linarith
  have hd := arcDenom_pos hr0 hr t
  have hu := arcDenom_le_four hr0 hr.le t
  have hl := arcDenom_ge_one hr0 ht
  have hprod := mul_le_mul_of_nonneg_left hu hvp.le
  have hprod' := mul_le_mul_of_nonneg_left hl hvp.le
  constructor
  · rw [arcY, le_div_iff₀ hd]
    nlinarith
  · rw [arcY, div_le_iff₀ hd]
    nlinarith [sq_nonneg (1-r)]

lemma cayley_leftArc (r t : ℝ) :
    cayleyToHalfPlane (-(r:ℂ)*Complex.exp ((t:ℂ)*I)) =
      (arcX r t:ℂ) + (arcY r t:ℂ)*I := by
  apply Complex.ext
  all_goals simp only [cayleyToHalfPlane, Complex.div_re, Complex.div_im,
    Complex.exp_mul_I, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
    Complex.cos_ofReal_im, Complex.sin_ofReal_im, Complex.normSq_apply,
    mul_zero, zero_mul, add_zero, zero_add, mul_one, neg_zero, sub_zero]
  all_goals dsimp [arcX, arcY, arcDenom]
  all_goals have hs := congrArg (fun a : ℝ => r^2*a) (Real.sin_sq_add_cos_sq t)
  all_goals have hd : (1 - -r * Real.cos t) * (1 - -r * Real.cos t) +
      (0 - -r * Real.sin t) * (0 - -r * Real.sin t) = 1 + 2*r*Real.cos t + r^2 := by nlinarith [hs]
  all_goals rw [hd]
  · rw [← add_div]
    congr 1
    ring
  · rw [← sub_div]
    congr 1
    nlinarith [hs]

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma uniform_vertical_Q_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : DiskFamily) (s : ℝ) (hs : 0 < s),
      1/4 ≤ s → s ≤ 4 → ‖halfPlaneQ f (xyPoint 0 s hs)‖ ≤ K := by
  let X := DiskFamily × Icc (1/4:ℝ) 4
  let W : C(X, ℝ) := ⟨fun p => ‖halfPlaneQ p.1 (xyPoint 0 p.2 (by have hh := p.2.property.1; linarith))‖,
    (continuous_halfPlaneQ.comp (continuous_fst.prodMk
      ((continuous_const.add
        ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_snd)).mul_const I)).upperHalfPlaneMk _))).norm⟩
  refine ⟨‖W‖+1, by positivity, ?_⟩
  intro f s hs hlo hhi
  have hh := W.norm_coe_le_norm (f,⟨s,hlo,hhi⟩)
  change ‖‖halfPlaneQ f (xyPoint 0 s hs)‖‖ ≤ ‖W‖ at hh
  rw [norm_norm] at hh
  linarith

lemma vertical_Q_comparison {K : ℝ}
    (hK : ∀ (f : DiskFamily) (s : ℝ) (hs : 0 < s),
      1/4 ≤ s → s ≤ 4 → ‖halfPlaneQ f (xyPoint 0 s hs)‖ ≤ K)
    (f : DiskFamily) (x y v : ℝ) (hy : 0 < y) (hv : 0 < v)
    (hlo : v/4 ≤ y) (hhi : y ≤ 4*v) :
    ‖halfPlaneQ f (xyPoint x y hy)‖ ≤ K * ‖halfPlaneQ f (xyPoint x v hv)‖ := by
  have hp : 0 < y/v := div_pos hy hv
  have hlow : 1/4 ≤ y/v := (le_div_iff₀ hv).mpr (by linarith)
  have hupp : y/v ≤ 4 := (div_le_iff₀ hv).mpr hhi
  have he : affineProduct (xyPoint x v hv) (xyPoint 0 (y/v) hp) = xyPoint x y hy := by
    simp only [affineProduct_xyPoint,mul_zero,add_zero,mul_div_cancel₀ _ hv.ne']
  have hh := hK (rebase f (xyPoint x v hv)) (y/v) hp hlow hupp
  rw [halfPlaneQ_rebase,he,norm_div] at hh
  exact (div_le_iff₀ (norm_pos_iff.mpr (halfPlaneQ_ne_zero f _))).mp hh

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma arc_integral_change_bound (f : DiskFamily) {r v : ℝ}
    (hr0 : 1/2 ≤ r) (hr : r < 1) (hv : 0 < v) :
    (∫ t in -(Real.pi/2)..(Real.pi/2),
      ‖halfPlaneQ f (xyPoint (arcX r t) v hv)‖) ≤
      16 * ∫ x in (-1:ℝ)..1, ‖halfPlaneQ f (xyPoint x v hv)‖ := by
  let g : ℝ → ℝ := fun x => ‖halfPlaneQ f (xyPoint x v hv)‖
  have hg : Continuous g := continuous_Q_slice_apply f v hv
  have hrp : 0 ≤ r := by linarith
  have hab : -(Real.pi/2) ≤ Real.pi/2 := by linarith [Real.pi_pos]
  have hxc := arcX_continuous hrp hr
  have hdc := arcXDeriv_continuous hrp hr
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := -(Real.pi/2)) (b := Real.pi/2)
    (fun t _ => arcX_hasDerivAt hrp hr t) hdc.continuousOn hg
  have hmono : (∫ t in -(Real.pi/2)..(Real.pi/2), g (arcX r t)) ≤
      ∫ t in -(Real.pi/2)..(Real.pi/2), 16 * (g (arcX r t) * arcXDeriv r t) := by
    apply intervalIntegral.integral_mono_on hab
      ((hg.comp hxc).intervalIntegrable _ _)
      ((continuous_const.mul ((hg.comp hxc).mul hdc)).intervalIntegrable _ _)
    intro t ht
    have hd := arcXDeriv_lower hr0 hr ht
    have hp : 0 ≤ g (arcX r t) := norm_nonneg _
    change g (arcX r t) ≤ 16 * (g (arcX r t) * arcXDeriv r t)
    nlinarith
  simp only [Function.comp_apply] at hsub
  rw [intervalIntegral.integral_const_mul, hsub] at hmono
  have hxle : arcX r (-(Real.pi/2)) ≤ arcX r (Real.pi/2) := by
    have hh := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (-(Real.pi/2)) (Real.pi/2))
      hxc.continuousOn (fun t _ => (arcX_hasDerivAt hrp hr t).hasDerivWithinAt)
      (fun t ht => (by
        exact le_trans (by norm_num : (0:ℝ) ≤ 1/16) (arcXDeriv_lower hr0 hr (interior_subset ht))))
    exact hh ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  have he0 := arcX_bounds hrp hr (show -(Real.pi/2) ∈ Icc (-(Real.pi/2)) (Real.pi/2) from ⟨le_rfl,hab⟩)
  have he1 := arcX_bounds hrp hr (show Real.pi/2 ∈ Icc (-(Real.pi/2)) (Real.pi/2) from ⟨hab,le_rfl⟩)
  exact hmono.trans (mul_le_mul_of_nonneg_left
    (intervalIntegral.integral_mono_interval he0.1 hxle he1.2
      (ae_of_all _ (fun x => norm_nonneg _)) (hg.intervalIntegrable (-1) 1)) (by norm_num))

lemma inverse_disk_deriv_cayley_bound (f : DiskFamily) (z : UpperHalfPlane) :
    ‖deriv (diskExtension f.val) (cayleyToDisk z)‖⁻¹ ≤ 4 * ‖halfPlaneQ f z‖ := by
  have hd := halfPlaneFunction_deriv f z.im_pos
  have hn : ‖deriv (halfPlaneFunction f) z‖ =
      4 * ‖deriv (diskExtension f.val) (cayleyToDisk z)‖ / ‖(z:ℂ)+I‖^2 := by
    rw [hd]
    simp only [norm_mul,norm_div,norm_pow,Complex.norm_I,norm_ofNat,mul_one]
    ring
  have hsq : 1 ≤ ‖(z:ℂ)+I‖^2 := by
    have hi := Complex.abs_im_le_norm ((z:ℂ)+I)
    have hz : 0 < (z:ℂ).im := z.im_pos
    simp only [Complex.add_im,Complex.I_im] at hi
    have hl := (le_abs_self _).trans hi
    nlinarith [norm_nonneg ((z:ℂ)+I)]
  have hp : 0 < ‖deriv (diskExtension f.val) (cayleyToDisk z)‖ :=
    norm_pos_iff.mpr (diskFamily_derivative_ne_zero f ⟨_,cayleyToDisk_mem z.im_pos⟩)
  simp only [halfPlaneQ,norm_inv,hn]
  rw [inv_div]
  field_simp
  exact hsq

lemma half_arc_inverse_bound {K : ℝ} (hK0 : 0 < K)
    (hK : ∀ (f : DiskFamily) (s : ℝ) (hs : 0 < s),
      1/4 ≤ s → s ≤ 4 → ‖halfPlaneQ f (xyPoint 0 s hs)‖ ≤ K)
    (f : DiskFamily) {r v : ℝ} (hr0 : 1/2 ≤ r) (hr : r < 1)
    (hv : v ≤ 1-r) (hrv : 1-r ≤ 2*v) :
    (∫ t in -(Real.pi/2)..(Real.pi/2),
      ‖deriv (diskExtension f.val) (-(r:ℂ)*Complex.exp ((t:ℂ)*I))‖⁻¹) ≤
      64*K * ∫ x in (-1:ℝ)..1,
        ‖halfPlaneQ f (xyPoint x v (by linarith))‖ := by
  have hrp : 0 ≤ r := by linarith
  have hvp : 0 < v := by linarith
  let γ : ℝ → UpperHalfPlane := fun t => xyPoint (arcX r t) (arcY r t) (arcY_pos hrp hr t)
  have hcγ : Continuous γ :=
    ((Complex.continuous_ofReal.comp (arcX_continuous hrp hr)).add
      ((Complex.continuous_ofReal.comp (arcY_continuous hrp hr)).mul_const I)).upperHalfPlaneMk _
  have he (t : ℝ) : cayleyToDisk (γ t) = -(r:ℂ)*Complex.exp ((t:ℂ)*I) := by
    rw [show (γ t : ℂ) = cayleyToHalfPlane (-(r:ℂ)*Complex.exp ((t:ℂ)*I)) from
      (cayley_leftArc r t).symm]
    apply cayleyToDisk_toHalfPlane
    simp only [mem_ball,dist_zero_right,norm_mul,norm_neg,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hrp,Complex.norm_exp_ofReal_mul_I,mul_one]
    exact hr
  have hcont : Continuous (fun t : ℝ => ‖deriv (diskExtension f.val)
      (-(r:ℂ)*Complex.exp ((t:ℂ)*I))‖⁻¹) := by
    simp_rw [← he]
    exact ((continuous_diskFamily_derivative.comp
      (continuous_const.prodMk (cayleyDiskMap.continuous.comp hcγ))).norm).inv₀
        (fun t => norm_ne_zero_iff.mpr (diskFamily_derivative_ne_zero f _))
  have hab : -(Real.pi/2) ≤ Real.pi/2 := by linarith [Real.pi_pos]
  have haux : Continuous (fun t => ‖halfPlaneQ f (xyPoint (arcX r t) v hvp)‖) :=
    (continuous_Q_slice_apply f v hvp).comp (arcX_continuous hrp hr)
  have hb : (∫ t in -(Real.pi/2)..(Real.pi/2),
      ‖deriv (diskExtension f.val) (-(r:ℂ)*Complex.exp ((t:ℂ)*I))‖⁻¹) ≤
      ∫ t in -(Real.pi/2)..(Real.pi/2),
        (4*K) * ‖halfPlaneQ f (xyPoint (arcX r t) v hvp)‖ := by
    apply intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable _ _)
      ((continuous_const.mul haux).intervalIntegrable _ _)
    intro t ht
    rw [← he]
    refine (inverse_disk_deriv_cayley_bound f (γ t)).trans ?_
    change 4 * ‖halfPlaneQ f (γ t)‖ ≤ (4*K)*‖halfPlaneQ f (xyPoint (arcX r t) v hvp)‖
    have hs := arcY_scale_bounds hrp hr hv hrv ht
    have hcmp := vertical_Q_comparison hK f (arcX r t) (arcY r t) v
      (arcY_pos hrp hr t) hvp hs.1 hs.2
    exact le_trans (mul_le_mul_of_nonneg_left hcmp (by norm_num)) (le_of_eq (by ring))
  rw [intervalIntegral.integral_const_mul] at hb
  exact hb.trans (by
    have hh := mul_le_mul_of_nonneg_left (arc_integral_change_bound f hr0 hr hvp)
      (show 0 ≤ 4*K by positivity)
    convert hh using 1
    ring)

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma circlePoint_mem_disk {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (t : ℝ) :
    (r:ℂ)*Complex.exp ((t:ℂ)*I) ∈ ball (0:ℂ) 1 := by
  simpa only [mem_ball,dist_zero_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hr0,Complex.norm_exp_ofReal_mul_I,mul_one] using hr

lemma circleInverseDensity_continuous (f : DiskFamily) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) : Continuous (circleInverseDensity f r) := by
  have hp : Continuous (fun t : ℝ => (⟨(r:ℂ)*Complex.exp ((t:ℂ)*I),
      circlePoint_mem_disk hr0 hr t⟩ : UnitDisk)) :=
    (continuous_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul_const I))).subtype_mk _
  exact (continuous_diskFamily_derivative.comp (continuous_const.prodMk hp)).norm.inv₀
    (fun t => norm_ne_zero_iff.mpr (diskFamily_derivative_ne_zero f _))

lemma circleInverseDensity_periodic (f : DiskFamily) (r : ℝ) :
    Function.Periodic (circleInverseDensity f r) (2*Real.pi) := by
  intro t
  unfold circleInverseDensity
  congr 3
  push_cast
  rw [add_mul,Complex.exp_add]
  have hh : Complex.exp (((2:ℂ)*Real.pi)*I) = 1 := by
    convert Complex.exp_two_pi_mul_I using 1
  rw [hh,mul_one]

lemma circleInverseDensity_shift_pi (f : DiskFamily) (r t : ℝ) :
    circleInverseDensity f r (t+Real.pi) = leftArcInverseDensity f r t := by
  unfold circleInverseDensity leftArcInverseDensity
  congr 3
  push_cast
  rw [add_mul,Complex.exp_add,Complex.exp_pi_mul_I]
  ring

lemma leftArcInverseDensity_negate (f : DiskFamily) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) (t : ℝ) :
    leftArcInverseDensity (diskNegateFamily f) r t = circleInverseDensity f r t := by
  unfold leftArcInverseDensity circleInverseDensity
  change ‖deriv (diskExtension (diskNegateMap f.val)) _‖⁻¹ = _
  have hm : -(r:ℂ)*Complex.exp ((t:ℂ)*I) ∈ ball (0:ℂ) 1 := by
    simpa only [neg_mul,mem_ball,dist_zero_right,norm_neg] using circlePoint_mem_disk hr0 hr t
  rw [(diskNegateMap_hasDerivAt f hm).deriv]
  simp only [neg_mul,neg_neg]

lemma wholeCircle_eq_two_left_arcs (f : DiskFamily) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) :
    (∫ t in -Real.pi..Real.pi, circleInverseDensity f r t) =
      (∫ t in -(Real.pi/2)..Real.pi/2, leftArcInverseDensity f r t) +
      ∫ t in -(Real.pi/2)..Real.pi/2, leftArcInverseDensity (diskNegateFamily f) r t := by
  have hc := circleInverseDensity_continuous f hr0 hr
  simp_rw [leftArcInverseDensity_negate f hr0 hr]
  have hp := (circleInverseDensity_periodic f r).intervalIntegral_add_eq
    (-Real.pi) (-(Real.pi/2))
  have hshift := intervalIntegral.integral_comp_add_right
    (circleInverseDensity f r) Real.pi (a := -(Real.pi/2)) (b := Real.pi/2)
  simp only [circleInverseDensity_shift_pi] at hshift
  have he1 : -Real.pi+2*Real.pi = Real.pi := by ring
  have he2 : -(Real.pi/2)+Real.pi = Real.pi/2 := by ring
  have he3 : Real.pi/2+Real.pi = -(Real.pi/2)+2*Real.pi := by ring
  rw [he1] at hp
  rw [he2,he3] at hshift
  rw [hp,← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),← hshift]
  exact add_comm _ _

lemma whole_circle_dyadic_operator_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : DiskFamily) (r : ℝ) (n : ℕ),
      1/2 ≤ r → r < 1 → dyadicHeight n ≤ 1-r → 1-r ≤ 2*dyadicHeight n →
      (∫ t in -Real.pi..Real.pi, circleInverseDensity f r t) ≤ C * ‖dyadicOperator^n‖ := by
  obtain ⟨K,hK0,hK⟩ := uniform_vertical_Q_bound
  let A := 2*‖horizontalQMean 1 zero_lt_one‖+1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨128*K*A,by positivity,?_⟩
  intro f r n hr0 hr hv hrv
  have h0 := half_arc_inverse_bound hK0 hK f hr0 hr hv hrv
  have h1 := half_arc_inverse_bound hK0 hK (diskNegateFamily f) hr0 hr hv hrv
  have hb0 := horizontalQMean_bound n f
  have hb1 := horizontalQMean_bound n (diskNegateFamily f)
  have hb0' := h0.trans (mul_le_mul_of_nonneg_left hb0 (show 0 ≤ 64*K by positivity))
  have hb1' := h1.trans (mul_le_mul_of_nonneg_left hb1 (show 0 ≤ 64*K by positivity))
  rw [wholeCircle_eq_two_left_arcs f (by linarith) hr]
  change (∫ t in -(Real.pi/2)..Real.pi/2, leftArcInverseDensity f r t) ≤ _ at hb0'
  change (∫ t in -(Real.pi/2)..Real.pi/2, leftArcInverseDensity (diskNegateFamily f) r t) ≤ _ at hb1'
  have hs := add_le_add hb0' hb1'
  refine hs.trans ?_
  dsimp [A]
  nlinarith [mul_nonneg hK0.le (norm_nonneg (dyadicOperator^n))]

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.UniformMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma dyadic_norm_power_bound {b : ℝ} (hb : dyadicExponent < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖dyadicOperator^n‖ ≤ C * (dyadicHeight n)^(-b) := by
  have hb0 : 0 < b := lt_of_le_of_lt dyadicExponent_nonneg hb
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : dyadicLogGrowth < b*Real.log 2 := (div_lt_iff₀ hl2).mp hb
  obtain ⟨N,hN⟩ := eventually_atTop.mp (normPower_eventually_le_exp
    dyadicOperator dyadicOperator_pow_norm_ge_one he)
  let C : ℝ := 1 + ∑ i ∈ Finset.range N, ‖dyadicOperator^i‖
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => norm_nonneg (dyadicOperator^i)))
  refine ⟨C,lt_of_lt_of_le zero_lt_one hC,?_⟩
  intro n
  have hexp : Real.exp ((b*Real.log 2)*n) = (dyadicHeight n)^(-b) := by
    rw [Real.rpow_def_of_pos (dyadicHeight_pos n)]
    unfold dyadicHeight
    rw [Real.log_pow,Real.log_div (by norm_num) (by norm_num),Real.log_one]
    congr 1
    ring
  have hpos : 1 ≤ Real.exp ((b*Real.log 2)*n) :=
    Real.one_le_exp (by positivity)
  rw [← hexp]
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_mul_of_one_le_left (by positivity) hC)
  · have hle : ‖dyadicOperator^n‖ ≤ ∑ i ∈ Finset.range N, ‖dyadicOperator^i‖ :=
      Finset.single_le_sum (f := fun i => ‖dyadicOperator^i‖) (fun i _ => norm_nonneg (dyadicOperator^i)) (Finset.mem_range.mpr (lt_of_not_ge hn))
    have hs : ‖dyadicOperator^n‖ ≤ C := by dsimp [C]; linarith
    exact hs.trans (le_mul_of_one_le_right (by positivity : 0 ≤ C) hpos)

lemma dyadicScale_for_radius {r : ℝ} (hr0 : 1/2 ≤ r) (hr : r < 1) :
    ∃ n : ℕ, dyadicHeight n ≤ 1-r ∧ 1-r ≤ 2*dyadicHeight n := by
  obtain ⟨n,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one
    (show 0 < 1-r by linarith) (show 1-r ≤ 1 by linarith)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  refine ⟨n+1,hlo.le,?_⟩
  change 1-r ≤ 2*((1/2:ℝ)^(n+1))
  rw [pow_succ]
  nlinarith

lemma dyadicHeight_neg_rpow_le {b d : ℝ} (hb : 0 ≤ b) (hd : 0 < d) (n : ℕ)
    (hhi : d ≤ 2*dyadicHeight n) :
    (dyadicHeight n)^(-b) ≤ (2:ℝ)^b * d^(-b) := by
  have hlow : d/2 ≤ dyadicHeight n := by linarith
  have hh := Real.rpow_le_rpow_of_nonpos (show 0 < d/2 by positivity) hlow (neg_nonpos.mpr hb)
  refine hh.trans_eq ?_
  rw [Real.div_rpow hd.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  simp only [div_inv_eq_mul,mul_comm]

lemma family_uniform_mean_bound {b : ℝ} (hb : dyadicExponent < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : DiskFamily) (r : ℝ), 1/2 ≤ r → r < 1 →
      (∫ t in -Real.pi..Real.pi, circleInverseDensity f r t) ≤ C * (1-r)^(-b) := by
  obtain ⟨A,hA,hAc⟩ := whole_circle_dyadic_operator_bound
  obtain ⟨B,hB,hBc⟩ := dyadic_norm_power_bound hb
  have hb0 : 0 ≤ b := dyadicExponent_nonneg.trans hb.le
  refine ⟨A*B*(2:ℝ)^b,by positivity,?_⟩
  intro f r hr0 hr
  obtain ⟨n,hlo,hhi⟩ := dyadicScale_for_radius hr0 hr
  calc
    (∫ t in -Real.pi..Real.pi, circleInverseDensity f r t) ≤ A*‖dyadicOperator^n‖ := hAc f r n hr0 hr hlo hhi
    _ ≤ A*(B*(dyadicHeight n)^(-b)) := mul_le_mul_of_nonneg_left (hBc n) hA.le
    _ = (A*B)*(dyadicHeight n)^(-b) := by ring
    _ ≤ (A*B)*((2:ℝ)^b*(1-r)^(-b)) := mul_le_mul_of_nonneg_left
      (dyadicHeight_neg_rpow_le hb0 (by linarith) n hhi) (by positivity)
    _ = _ := by ring

lemma integralMean_neg_one_as_family (f : ℂ → ℂ) (hf : NormalizedUnivalent f)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    integralMean (-1) f r = (2*Real.pi)⁻¹ *
      ∫ t in -Real.pi..Real.pi, circleInverseDensity (normalizedDiskFamily f hf) r t := by
  unfold integralMean circleInverseDensity
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [Real.rpow_neg_one]
  change ‖deriv f _‖⁻¹ = ‖deriv (diskExtension (normalizedDiskMap f hf)) _‖⁻¹
  rw [normalizedDiskMap_deriv f hf (circlePoint_mem_disk hr0 hr t)]

theorem uniform_integralMean_bound_above_dyadicExponent {b : ℝ} (hb : dyadicExponent < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℂ → ℂ), NormalizedUnivalent f →
      ∀ r : ℝ, 1/2 ≤ r → r < 1 → integralMean (-1) f r ≤ C*(1-r)^(-b) := by
  obtain ⟨A,hA,hAc⟩ := family_uniform_mean_bound hb
  refine ⟨(2*Real.pi)⁻¹*A,by positivity,?_⟩
  intro f hf r hr0 hr
  rw [integralMean_neg_one_as_family f hf (by linarith) hr]
  have hh := mul_le_mul_of_nonneg_left (hAc (normalizedDiskFamily f hf) r hr0 hr)
    (show 0 ≤ (2*Real.pi)⁻¹ by positivity)
  simpa only [mul_assoc] using hh

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.Spectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma integralMean_neg_one_pos (f : ℂ → ℂ) (hf : NormalizedUnivalent f)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) : 0 < integralMean (-1) f r := by
  rw [integralMean_neg_one_as_family f hf hr0 hr]
  apply mul_pos (by positivity)
  apply intervalIntegral.integral_pos (by linarith [Real.pi_pos])
    (circleInverseDensity_continuous (normalizedDiskFamily f hf) hr0 hr).continuousOn
  · intro t _
    exact inv_nonneg.mpr (norm_nonneg _)
  · refine ⟨0,⟨by linarith [Real.pi_pos],Real.pi_pos.le⟩,?_⟩
    apply inv_pos.mpr
    apply norm_pos_iff.mpr
    exact diskFamily_derivative_ne_zero (normalizedDiskFamily f hf) ⟨_,circlePoint_mem_disk hr0 hr 0⟩

lemma boundary_log_inverse_tendsto :
    Tendsto (fun r : ℝ => Real.log (1/(1-r))) (𝓝[<] (1:ℝ)) atTop := by
  have hd : Tendsto (fun r : ℝ => 1-r) (𝓝[<] (1:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [sub_self] using (tendsto_const_nhds.sub
        (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun r : ℝ => 1-r) (𝓝[<] (1:ℝ)) (𝓝 (1-1:ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change 0 < 1-r
      exact sub_pos.mpr hr
  simpa only [one_div,Function.comp_def] using Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp hd)

lemma growthExponent_le_of_mean_bound (f : ℂ → ℂ) (hf : NormalizedUnivalent f)
    {C b : ℝ} (hC : 0 < C)
    (hbound : ∀ r : ℝ, 1/2 ≤ r → r < 1 → integralMean (-1) f r ≤ C*(1-r)^(-b)) :
    growthExponent (-1) f ≤ (b : EReal) := by
  have ht : Tendsto (fun r : ℝ => b+Real.log C / Real.log (1/(1-r)))
      (𝓝[<] (1:ℝ)) (𝓝 b) := by
    simpa using tendsto_const_nhds.add
      (Tendsto.div_atTop (tendsto_const_nhds (x := Real.log C)) boundary_log_inverse_tendsto)
  have hte : Tendsto (fun r : ℝ => ((b+Real.log C / Real.log (1/(1-r)) : ℝ) : EReal))
      (𝓝[<] (1:ℝ)) (𝓝 (b : EReal)) := (continuous_coe_real_ereal.tendsto b).comp ht
  have he : ∀ᶠ r : ℝ in 𝓝[<] (1:ℝ),
      ((Real.log (integralMean (-1) f r) / Real.log (1/(1-r)) : ℝ) : EReal) ≤
        ((b+Real.log C / Real.log (1/(1-r)) : ℝ) : EReal) := by
    have hrlo : ∀ᶠ r : ℝ in 𝓝[<] (1:ℝ), 1/2 ≤ r :=
      (eventually_ge_nhds (by norm_num : (1/2:ℝ)<1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hrlo,self_mem_nhdsWithin] with r hr0 hr
    have hd : 0 < 1-r := sub_pos.mpr hr
    have hd1 : 1 < 1/(1-r) := (one_lt_div hd).mpr (by linarith)
    have hlogd : 0 < Real.log (1/(1-r)) := Real.log_pos hd1
    have hm := Real.log_le_log (integralMean_neg_one_pos f hf (by linarith) hr) (hbound r hr0 hr)
    rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hd _).ne',Real.log_rpow hd] at hm
    have hi : Real.log (1/(1-r)) = -Real.log (1-r) := by rw [one_div,Real.log_inv]
    apply EReal.coe_le_coe_iff.mpr
    apply (div_le_iff₀ hlogd).mpr
    have hc : (Real.log C / Real.log (1/(1-r)))*Real.log (1/(1-r)) = Real.log C :=
      div_mul_cancel₀ _ hlogd.ne'
    rw [add_mul,hc,hi]
    nlinarith
  exact (limsup_le_limsup he).trans_eq hte.limsup_eq

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.Endpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

/-- A single, strictly positive gap works for every normalized univalent map,
and hence for the supremum of the individual bounded-map exponents. -/
theorem uniform_inverse_first_power_gap :
    ∃ ε C : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < C ∧
      (∀ (f : ℂ → ℂ), NormalizedUnivalent f →
        ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
          integralMean (-1) f r ≤ C * (1 - r) ^ (-(1 / 4 : ℝ) + ε)) ∧
      boundedSpectrum (-1) ≤ ((1 / 4 - ε : ℝ) : EReal) := by
  let b := (dyadicExponent+1/4)/2
  have hb : dyadicExponent < b := by dsimp [b]; linarith [dyadicExponent_lt_quarter]
  have hb0 : 0 < b := lt_of_le_of_lt dyadicExponent_nonneg hb
  have hb1 : b < 1/4 := by dsimp [b]; linarith [dyadicExponent_lt_quarter]
  obtain ⟨C,hC,hbound⟩ := uniform_integralMean_bound_above_dyadicExponent hb
  refine ⟨1/4-b,C,by linarith,by linarith,hC,?_,?_⟩
  · intro f hf r hr0 hr
    simpa only [show -(1/4:ℝ)+(1/4-b) = -b by ring] using hbound f hf r hr0 hr
  · rw [show (1/4:ℝ) - (1/4-b) = b by ring]
    apply iSup_le
    intro f
    apply iSup_le
    intro hf
    exact growthExponent_le_of_mean_bound f hf.1 hC (hbound f hf.1)

theorem uniform_inverse_first_power :
    ∃ ε C : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      ∀ (f : ℂ → ℂ), NormalizedUnivalent f →
        ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
          integralMean (-1) f r ≤ C * (1 - r) ^ (-(1 / 4 : ℝ) + ε) := by
  obtain ⟨ε,C,hε,hε',_hC,hbound,_hs⟩ := uniform_inverse_first_power_gap
  exact ⟨ε,C,hε,hε',hbound⟩

theorem bounded_spectrum_strict : boundedSpectrum (-1) < (1 / 4 : EReal) := by
  obtain ⟨ε,_C,hε,_hε',_hC,_hbound,hs⟩ := uniform_inverse_first_power_gap
  apply hs.trans_lt
  change ((1/4-ε : ℝ) : EReal) < ((1/4 : ℝ) : EReal)
  exact EReal.coe_lt_coe_iff.mpr (by linarith)

theorem kraetzer_identity_false :
    ¬ ∀ p : ℝ, boundedSpectrum p = kraetzerPrediction p := by
  intro h
  have hp := bounded_spectrum_strict
  rw [h (-1)] at hp
  have hpred : kraetzerPrediction (-1) = ((1/4 : ℝ) : EReal) := by
    norm_num [kraetzerPrediction]
  rw [hpred] at hp
  change ((1/4 : ℝ) : EReal) < ((1/4 : ℝ) : EReal) at hp
  exact lt_irrefl _ hp

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace StrictInverseFirstPower

theorem main_oai :
    (∃ ε C : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      ∀ (f : ℂ → ℂ), NormalizedUnivalent f →
        ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
          integralMean (-1) f r ≤ C * (1 - r) ^ (-(1 / 4 : ℝ) + ε)) ∧
    boundedSpectrum (-1) < (1 / 4 : EReal) ∧
    (¬ ∀ p : ℝ, boundedSpectrum p = kraetzerPrediction p) :=
  ⟨uniform_inverse_first_power, bounded_spectrum_strict, kraetzer_identity_false⟩

end StrictInverseFirstPower

end OAI
end

theorem solution : type_of% @OAI.StrictInverseFirstPower.main_oai := @OAI.StrictInverseFirstPower.main_oai
