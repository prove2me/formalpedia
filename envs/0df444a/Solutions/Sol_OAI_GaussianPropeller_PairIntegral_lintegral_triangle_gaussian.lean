-- Prove2me | solution 1 for OAI.GaussianPropeller.PairIntegral.lintegral_triangle_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:56:24.336389+00:00
-- url     : https://prove2.me/submissions/b5492961-53cd-4f78-8c4c-ced525b8e570

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/PairIntegral.lean:L252-L278
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.PairIntegral.lintegral_triangle_gaussian. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral

-- ---- from OAI.Probability.GaussianPropeller.PairIntegral ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uX

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

namespace GaussianPropeller.PairIntegral

lemma integrableOn_pos_sub_pow (b : ℝ) {n : ℕ} (hn : n ≠ 0) :
    IntegrableOn (fun x : ℝ => (max (b-x) 0)^n) (Ici 0) := by
  by_cases hb : 0 ≤ b
  · have hi : IntegrableOn (fun x : ℝ => (max (b-x) 0)^n) (Icc 0 b) :=
      (by fun_prop : Continuous (fun x : ℝ => (max (b-x) 0)^n)).integrableOn_Icc
    have hz : IntegrableOn (fun x : ℝ => (max (b-x) 0)^n) (Ioi b) := by
      apply integrableOn_zero.congr_fun _ measurableSet_Ioi
      intro x hx
      have hx' : b ≤ x := le_of_lt hx
      simp only [max_eq_right (sub_nonpos.mpr hx'), zero_pow hn]
    simpa [Icc_union_Ioi_eq_Ici hb] using hi.union hz
  · apply integrableOn_zero.congr_fun _ measurableSet_Ici
    intro x hx
    have hx' : 0 ≤ x := hx
    simp only [max_eq_right (by linarith : b-x ≤ 0), zero_pow hn]

lemma integral_pos_sub_pow (b : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∫ x : ℝ in Ici 0, (max (b-x) 0)^n = (max b 0)^(n+1)/(n+1) := by
  by_cases hb : 0 ≤ b
  · rw [max_eq_left hb, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Ici (show Icc 0 b ⊆ Ici 0 from fun _ hx => hx.1)]
    · rw [setIntegral_congr_fun measurableSet_Icc (fun x hx =>
        congrArg (fun z : ℝ => z^n) (max_eq_left (by linarith [hx.2] : 0 ≤ b-x)))]
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb,
        intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^n) b]
      simp [integral_pow]
    · intro x hx
      have hxb : b < x := lt_of_not_ge (fun h => hx.2 ⟨hx.1,h⟩)
      simp [max_eq_right (by linarith : b-x ≤ 0), hn]
  · rw [max_eq_right (le_of_not_ge hb)]
    simp only [zero_pow (Nat.succ_ne_zero n), zero_div]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have hx' : 0 ≤ x := hx
    simp only [max_eq_right (by linarith : b-x ≤ 0), zero_pow hn]

lemma lintegral_pos_sub_pow (b : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∫⁻ x : ℝ in Ici 0, ENNReal.ofReal ((max (b-x) 0)^n) =
      ENNReal.ofReal ((max b 0)^(n+1)/(n+1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_pos_sub_pow b hn)
    (ae_of_all _ (fun _ => pow_nonneg (le_max_right _ _) _)), integral_pos_sub_pow b hn]

lemma lintegral_triangle_shifted (s : ℝ) :
    ∫⁻ a : ℝ in Ici 0, ∫⁻ b : ℝ in Ici 0,
      ENNReal.ofReal (max (3*s-a-b) 0) = ENNReal.ofReal ((max (3*s) 0)^3/6) := by
  have hl (c : ℝ) : ∫⁻ b : ℝ in Ici 0, ENNReal.ofReal (max (c-b) 0) =
      ENNReal.ofReal ((max c 0)^2/2) := by
    simpa only [pow_one, Nat.cast_one, one_add_one_eq_two] using
      lintegral_pos_sub_pow c (by decide : (1:ℕ) ≠ 0)
  simp_rw [hl]
  simp_rw [div_eq_mul_inv, ENNReal.ofReal_mul (sq_nonneg _)]
  rw [lintegral_mul_const _ (by fun_prop), lintegral_pos_sub_pow _ (by decide : (2:ℕ) ≠ 0)]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  norm_num
  ring

lemma gaussianPDF_std_le (x : ℝ) :
    gaussianPDF 0 1 x ≤ ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹) := by
  apply ENNReal.ofReal_le_ofReal
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  have he : Real.exp (-(x^2)/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg x])
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (mul_one _)

lemma lintegral_gaussian_std_le (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂gaussianReal 0 1 ≤
      ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹) * ∫⁻ x, f x := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1:NNReal) ≠ 0),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hf]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹) * f x :=
      lintegral_mono (fun x => by
        simpa only [mul_comm, Pi.mul_apply] using
          mul_le_mul_right (gaussianPDF_std_le x) (f x))
    _ = _ := lintegral_const_mul _ hf

lemma lintegral_affine_volume (f : ℝ → ℝ≥0∞) (hf : Measurable f) (b : ℝ)
    {a : ℝ} (ha : a ≠ 0) :
    ∫⁻ x : ℝ, f (a*x+b) = ENNReal.ofReal |a⁻¹| * ∫⁻ u, f u := by
  have hm := lintegral_map (μ := (volume : Measure ℝ))
    (f := fun u => f (u+b)) (g := fun x => a*x)
    (by fun_prop) (by fun_prop)
  rw [← hm, Real.map_volume_mul_left ha, lintegral_smul_measure,
    lintegral_add_right_eq_self]
  rfl

lemma lintegral_affine_gaussian_le (f : ℝ → ℝ≥0∞) (hf : Measurable f) (b : ℝ)
    {a : ℝ} (ha : 0 < a) :
    ∫⁻ x : ℝ, f (a*x+b) ∂gaussianReal 0 1 ≤
      ENNReal.ofReal ((Real.sqrt (2*Real.pi)*a)⁻¹) * ∫⁻ u, f u := by
  calc
    _ ≤ ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹) * ∫⁻ x : ℝ, f (a*x+b) :=
      lintegral_gaussian_std_le _ (by fun_prop)
    _ = _ := by
      rw [lintegral_affine_volume f hf b ha.ne', ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity)]
      simp only [abs_of_pos (inv_pos.mpr ha), mul_inv_rev, mul_comm]

lemma measurable_triangle : Measurable (fun p : ℝ × ℝ × ℝ => triangle p.1 p.2.1 p.2.2) := by
  unfold triangle
  exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop))
    (Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop)
      measurable_const) measurable_const

lemma lintegral_triangle (s : ℝ) :
    ∫⁻ u : ℝ, ∫⁻ v : ℝ, triangle s u v = ENNReal.ofReal ((max (3*s) 0)^3/6) := by
  calc
    _ = ∫⁻ a : ℝ, ∫⁻ b : ℝ, triangle s (s-a) (s-b) := by
      simp only [lintegral_sub_left_eq_self]
      exact (lintegral_sub_left_eq_self (fun u : ℝ => ∫⁻ v : ℝ, triangle s u v) s).symm
    _ = ∫⁻ a : ℝ in Ici 0, ∫⁻ b : ℝ in Ici 0,
        ENNReal.ofReal (max (3*s-a-b) 0) := by
      have hfun (a b : ℝ) : triangle s (s-a) (s-b) =
          (Ici (0:ℝ)).indicator (fun a => (Ici (0:ℝ)).indicator
            (fun b => ENNReal.ofReal (max (3*s-a-b) 0)) b) a := by
        simp only [triangle, Set.indicator, mem_Ici]
        simp only [show s-a ≤ s ↔ 0 ≤ a by constructor <;> intro h <;> linarith,
          show s-b ≤ s ↔ 0 ≤ b by constructor <;> intro h <;> linarith,
          show s+(s-a)+(s-b) = 3*s-a-b by ring]
      simp_rw [hfun]
      have hint (a : ℝ) :
          (∫⁻ b : ℝ, (Ici (0:ℝ)).indicator (fun a => (Ici (0:ℝ)).indicator
            (fun b => ENNReal.ofReal (max (3*s-a-b) 0)) b) a) =
          (Ici (0:ℝ)).indicator (fun a => ∫⁻ b : ℝ in Ici 0,
            ENNReal.ofReal (max (3*s-a-b) 0)) a := by
        by_cases ha : 0 ≤ a
        · simp only [Set.indicator, mem_Ici, ite_eq_left ha]
          simpa only [Set.indicator, mem_Ici] using lintegral_indicator measurableSet_Ici
            (fun b : ℝ => ENNReal.ofReal (max (3*s-a-b) 0))
        · simp only [Set.indicator, mem_Ici, ite_eq_right ha, lintegral_zero]
      simp_rw [hint]
      exact lintegral_indicator measurableSet_Ici _
    _ = _ := lintegral_triangle_shifted s

lemma lintegral_gaussian_pair_le (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f)
    (b : ℝ) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∫⁻ x : ℝ, (∫⁻ y : ℝ, f (a*x,b*x+c*y) ∂gaussianReal 0 1) ∂gaussianReal 0 1 ≤
      ENNReal.ofReal ((2*Real.pi*a*c)⁻¹) * ∫⁻ u : ℝ, ∫⁻ v : ℝ, f (u,v) := by
  let k := ENNReal.ofReal ((Real.sqrt (2*Real.pi)*c)⁻¹)
  have hm : Measurable (fun u : ℝ => ∫⁻ v : ℝ, f (u,v)) := hf.lintegral_prod_right'
  calc
    _ ≤ ∫⁻ x : ℝ, k * (∫⁻ v : ℝ, f (a*x,v)) ∂gaussianReal 0 1 := by
      apply lintegral_mono
      intro x
      simpa only [add_comm, k] using lintegral_affine_gaussian_le
        (fun v => f (a*x,v)) (by fun_prop) (b*x) hc
    _ = k * (∫⁻ x : ℝ, (∫⁻ v : ℝ, f (a*x,v)) ∂gaussianReal 0 1) :=
      lintegral_const_mul k (hm.comp (by fun_prop))
    _ ≤ k * (ENNReal.ofReal ((Real.sqrt (2*Real.pi)*a)⁻¹) *
        ∫⁻ u : ℝ, ∫⁻ v : ℝ, f (u,v)) := by
      gcongr
      simpa only [add_zero] using lintegral_affine_gaussian_le _ hm 0 ha
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [← mul_inv]
      congr 1
      calc
        _ = (Real.sqrt (2*Real.pi))^2*a*c := by ring
        _ = _ := by rw [Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)]

lemma integral_pos_cube_gaussian :
    ∫ x : ℝ, (max x 0)^3 ∂gaussianReal 0 1 = 2/Real.sqrt (2*Real.pi) := by
  have hc : ∫ x : ℝ in Ioi 0, x^3*Real.exp (-(1/2:ℝ)*x^2) = 2 := by
    have hh := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 3) (b := 1/2)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num [Real.rpow_natCast, Real.rpow_neg, Real.Gamma_nat_eq_factorial] at hh
    simpa only [neg_mul] using hh
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0)]
  have hf : (fun x : ℝ => gaussianPDFReal 0 1 x • (max x 0)^3) =
      (Real.sqrt (2*Real.pi))⁻¹ • (fun x : ℝ => (max x 0)^3*Real.exp (-(1/2:ℝ)*x^2)) := by
    ext x
    simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, Pi.smul_apply,
      smul_eq_mul]
    rw [show -(x^2)/2 = -(1/2:ℝ)*x^2 by ring]
    ring
  rw [hf]
  change (∫ x : ℝ, (Real.sqrt (2*Real.pi))⁻¹ * ((max x 0)^3*Real.exp (-(1/2:ℝ)*x^2))) = _
  rw [integral_const_mul]
  have hs : ∫ x : ℝ, (max x 0)^3*Real.exp (-(1/2:ℝ)*x^2) = 2 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0:ℝ))]
    · rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
        rw [max_eq_left (le_of_lt hx)])]
      exact hc
    · intro x hx
      have hx' : x ≤ 0 := le_of_not_gt hx
      simp [max_eq_right hx']
  rw [hs]
  ring

end GaussianPropeller.PairIntegral

namespace GaussianPropeller.PairIntegral

lemma integrable_pos_cube_gaussian :
    Integrable (fun x : ℝ => (max x 0)^3) (gaussianReal 0 1) := by
  have hi : Integrable (fun x : ℝ => ‖x‖^3) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 3).integrable_norm_pow (by decide : (3:ℕ) ≠ 0)
  apply hi.mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_max_right _ _) _)]
  apply pow_le_pow_left₀ (le_max_right _ _)
  exact max_le (le_abs_self _) (abs_nonneg _)

lemma lintegral_pos_cube_gaussian :
    ∫⁻ x : ℝ, ENNReal.ofReal ((max x 0)^3) ∂gaussianReal 0 1 =
      ENNReal.ofReal (2/Real.sqrt (2*Real.pi)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_pos_cube_gaussian
    (ae_of_all _ (fun _ => pow_nonneg (le_max_right _ _) _)), integral_pos_cube_gaussian]

lemma lintegral_triangle_gaussian {a c : ℝ} (b : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∫⁻ s : ℝ, (∫⁻ x : ℝ, (∫⁻ y : ℝ, triangle s (a*x) (b*x+c*y)
      ∂gaussianReal 0 1) ∂gaussianReal 0 1) ∂gaussianReal 0 1 ≤
      ENNReal.ofReal (9/(2*Real.pi*Real.sqrt (2*Real.pi)*a*c)) := by
  have hm : Measurable (fun s : ℝ => ENNReal.ofReal ((max (3*s) 0)^3/6)) := by fun_prop
  calc
    _ ≤ ∫⁻ s : ℝ, ENNReal.ofReal ((2*Real.pi*a*c)⁻¹) *
        ENNReal.ofReal ((max (3*s) 0)^3/6) ∂gaussianReal 0 1 := by
      apply lintegral_mono
      intro s
      exact (lintegral_gaussian_pair_le (fun p => triangle s p.1 p.2)
        (measurable_triangle.comp (measurable_const.prodMk measurable_id)) b ha hc).trans_eq
          (congrArg (ENNReal.ofReal ((2*Real.pi*a*c)⁻¹) * ·) (lintegral_triangle s))
    _ = _ := by
      have he (s : ℝ) : (max (3*s) 0)^3/6 = (9/2:ℝ)*(max s 0)^3 := by
        rw [show max (3*s) 0 = 3*max s 0 by
          by_cases hs : 0 ≤ s
          · rw [max_eq_left hs, max_eq_left (mul_nonneg (by norm_num) hs)]
          · rw [max_eq_right (le_of_not_ge hs), max_eq_right (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_not_ge hs)), mul_zero]]
        ring
      rw [lintegral_const_mul _ hm]
      simp_rw [he, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 9/2)]
      rw [lintegral_const_mul _ (by fun_prop), lintegral_pos_cube_gaussian,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 9/2),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp

end GaussianPropeller.PairIntegral

namespace GaussianPropeller.PairIntegral

end GaussianPropeller.PairIntegral

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.PairIntegral
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal


theorem solution : type_of% @_root_.OAI.GaussianPropeller.PairIntegral.lintegral_triangle_gaussian := @_root_.OAI.GaussianPropeller.PairIntegral.lintegral_triangle_gaussian
