-- Prove2me | solution 1 for OAI.SquareRootDegree.GaussianGain.tail_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:26:13.182993+00:00
-- url     : https://prove2.me/submissions/74dd65e4-6316-4d07-b79a-fa32c5fba7a0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/GaussianGain.lean:L273-L324
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.GaussianGain.tail_integral_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_GaussianGain
import Theorems.Thm_OAI_SquareRootDegree_SmoothGaussian_beta_lower
import Theorems.Thm_OAI_SquareRootDegree_SmoothSelector_hat_local

-- ---- from OAI.Combinatorics.BooleanFunctions.SmoothGaussian ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace SmoothGaussian

theorem tent_mass_pos {a h : ℝ} (hh : 0 < h) :
    0 < mass (gaussianReal 0 1) (tent a h) := by
  apply lt_of_lt_of_le _ (beta_lower hh)
  positivity

end SmoothGaussian
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.SmoothSelector ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace SmoothSelector

theorem clip_nonneg (x : ℝ) : 0 ≤ clip x := le_max_left _ _
theorem clip_le_one (x : ℝ) : clip x ≤ 1 := max_le zero_le_one (min_le_left _ _)
theorem clip_mono : Monotone clip := fun _ _ h => max_le_max le_rfl (min_le_min le_rfl h)
theorem clip_of_nonpos {x : ℝ} (hx : x ≤ 0) : clip x = 0 := by
  unfold clip; rw [max_eq_left (le_trans (min_le_right _ _) hx)]
theorem clip_of_one_le {x : ℝ} (hx : 1 ≤ x) : clip x = 1 := by
  unfold clip; rw [min_eq_left hx, max_eq_right zero_le_one]

theorem hat_nonneg (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (t : ℝ) :
    0 ≤ hat N δ i t := by
  unfold hat
  exact sub_nonneg.mpr (clip_mono (by linarith))

theorem hats_sum (N : ℕ) (δ t : ℝ) :
    ∑ i : Fin (2*N+1), hat N δ i t = clip (t/δ+N+1)-clip (t/δ-N) := by
  unfold hat
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    clip (t/δ+N-i+1)-clip (t/δ+N-i)) (2*N+1)]
  have he (i : ℕ) : clip (t/δ+N-i+1)-clip (t/δ+N-i) =
      clip (t/δ+N-i+1)-clip (t/δ+N-(i+1:ℕ)+1) := by push_cast; ring_nf
  simp_rw [he]
  rw [Finset.sum_range_sub']
  push_cast
  congr 1 <;> congr 1 <;> ring

theorem hats_sum_le_one (N : ℕ) (δ t : ℝ) :
    ∑ i : Fin (2*N+1), hat N δ i t ≤ 1 := by
  rw [hats_sum]
  linarith [clip_le_one (t/δ+N+1),clip_nonneg (t/δ-N)]

theorem hats_sum_eq_one {N : ℕ} {δ t : ℝ} (hδ : 0 < δ) (ht : |t| ≤ N*δ) :
    ∑ i : Fin (2*N+1), hat N δ i t = 1 := by
  rw [hats_sum]
  have ht' := abs_le.mp ht
  have hp : t/δ-N ≤ 0 := by
    have := (div_le_iff₀ hδ).mpr ht'.2
    linarith
  have hn : 1 ≤ t/δ+N+1 := by
    have : -(N:ℝ) ≤ t/δ := (le_div_iff₀ hδ).mpr (by linarith [ht'.1])
    linarith
  rw [clip_of_one_le hn,clip_of_nonpos hp,sub_zero]

theorem hat_support {N : ℕ} {δ t : ℝ} {i : Fin (2*N+1)} (hδ : 0 < δ)
    (hi : hat N δ i t ≠ 0) : |t| ≤ (N+1)*δ := by
  have hh := abs_lt.mp (hat_local hδ hi)
  have hi0 : 0 ≤ (i:ℝ) := Nat.cast_nonneg _
  have hiN : (i:ℝ) ≤ 2*N := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
  have h1 := mul_nonneg hδ.le hi0
  have h2 := mul_nonneg hδ.le (sub_nonneg.mpr hiN)
  rw [abs_le]
  dsimp [center] at hh
  constructor <;> nlinarith

theorem hat_compactSupport {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (i : Fin (2*N+1)) :
    HasCompactSupport (hat N δ i) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(N+1)*δ) (b := (N+1)*δ))
  intro x hx
  by_contra hn
  have hh := abs_le.mp (hat_support hδ hn)
  exact hx ⟨by linarith [hh.1],hh.2⟩

end SmoothSelector
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.GaussianGain ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace GaussianGain
open SmoothGaussian SmoothSelector

theorem gaussian_sq_integral (v : ℝ≥0) :
    (∫ x, x^2 ∂gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (show AEMeasurable (fun x : ℝ => x) (gaussianReal 0 v) from measurable_id.aemeasurable)] at h
  simpa using h

theorem gaussian_sq_integrable (v : ℝ≥0) : Integrable (fun x : ℝ => x^2) (gaussianReal 0 v) := by
  simpa using (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq

theorem gaussian_poly_integrable (v : ℝ≥0) :
    Integrable (fun x : ℝ => 1+x^2) (gaussianReal 0 v) :=
  (integrable_const 1).add (gaussian_sq_integrable v)

theorem density_tail_bound {R t : ℝ} (ht : R^2 ≤ t^2) :
    gaussianPDFReal 0 1 t ≤ 2 * Real.exp (-(R^2/4)) * gaussianPDFReal 0 2 t := by
  have he : Real.exp (-t^2/2) ≤ Real.exp (-(R^2/4)) * Real.exp (-t^2/4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hs : Real.sqrt (2*Real.pi*2) = Real.sqrt 2 * Real.sqrt (2*Real.pi) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1; ring_nf
  have hs2 : Real.sqrt 2 ≤ (2:ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg 2]
  have hs0 : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hc : (Real.sqrt (2*Real.pi))⁻¹ ≤ 2 * (Real.sqrt (2*Real.pi*2))⁻¹ := by
    rw [hs, mul_inv_rev]
    have h : (1:ℝ) ≤ 2 * (Real.sqrt 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))]
      simpa only [one_mul] using hs2
    nlinarith [mul_nonneg (inv_nonneg.mpr hs0.le) (sub_nonneg.mpr h)]
  simp only [gaussianPDFReal, NNReal.coe_one, NNReal.coe_ofNat, mul_one, sub_zero]
  calc
    _ ≤ (2*(Real.sqrt (2*Real.pi*2))⁻¹) *
        (Real.exp (-(R^2/4)) * Real.exp (-t^2/4)) :=
      mul_le_mul hc he (by positivity) (by positivity)
    _ = _ := by ring_nf

theorem density_integrable {v : ℝ≥0} (hv : v ≠ 0) {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 v)) :
    Integrable (fun t => gaussianPDFReal 0 v t * f t) volume := by
  rw [gaussianReal_of_var_ne_zero 0 hv] at hf
  have he := (integrable_withDensity_iff_integrable_smul₀'
    (show AEMeasurable (gaussianPDF 0 v) volume from
      (show Measurable (gaussianPDF 0 v) from by fun_prop).aemeasurable)
    (ae_of_all _ (fun _ => gaussianPDF_lt_top))).mp hf
  simpa only [toReal_gaussianPDF, smul_eq_mul] using he

theorem middle_mass_bound {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    (mass (gaussianReal 0 1) (tent 1 h))⁻¹ ≤ 54/h := by
  have hb := tent_mass_pos (a := 1) hh
  have hs : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs3 : Real.sqrt (2*Real.pi) ≤ 3 := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi),Real.pi_lt_four]
  have hA : (|(1:ℝ)|+h)^2/2 ≤ 2 := by norm_num only [abs_one]; nlinarith
  have he : Real.exp (-2) ≤ Real.exp (-((|(1:ℝ)|+h)^2)/2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hl : h/6*Real.exp (-2) ≤ mass (gaussianReal 0 1) (tent 1 h) := by
    apply le_trans _ (beta_lower hh)
    have hi : (1:ℝ)/3 ≤ (Real.sqrt (2*Real.pi))⁻¹ := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le hs hs3
    have hm := mul_le_mul hi he (Real.exp_pos (-2)).le (inv_nonneg.mpr hs.le)
    have hp := mul_le_mul_of_nonneg_left hm (show 0 ≤ h/2 by positivity)
    nlinarith
  have hE : Real.exp 2 ≤ 9 := by
    calc Real.exp 2 = (Real.exp 1)^2 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 3^2 := pow_le_pow_left₀ (Real.exp_pos _).le (le_trans Real.exp_one_lt_d9.le (by norm_num)) _
      _ = 9 := by norm_num
  have hlim : (mass (gaussianReal 0 1) (tent 1 h))⁻¹ ≤ 6/h * Real.exp 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hb]
    have heq : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; norm_num
    have hp := mul_le_mul_of_nonneg_right hl (show 0 ≤ 6/h*Real.exp 2 by positivity)
    calc 1 = (h/6*Real.exp (-2)) * (6/h*Real.exp 2) := by
           field_simp; nlinarith [heq]
      _ ≤ _ := by simpa only [mul_comm] using hp
  apply hlim.trans
  calc 6/h * Real.exp 2 ≤ 6/h*9 :=
      mul_le_mul_of_nonneg_left hE (show 0 ≤ 6/h by positivity)
    _ = 54/h := by ring_nf

theorem residual_nonneg (N : ℕ) (δ t : ℝ) : 0 ≤ residual N δ t :=
  sub_nonneg.mpr (hats_sum_le_one ..)

theorem residual_le_one (N : ℕ) (δ t : ℝ) : residual N δ t ≤ 1 := by
  have : 0 ≤ ∑ i, hat N δ i t := Finset.sum_nonneg (fun _ _ => hat_nonneg ..)
  dsimp [residual]; linarith

theorem residual_eq_zero {N : ℕ} {δ t : ℝ} (hδ : 0 < δ) (ht : |t| ≤ N*δ) :
    residual N δ t = 0 := by simp only [residual, hats_sum_eq_one hδ ht, sub_self]

theorem quadratic_integrable (c v : ℝ) (σ : ℝ≥0) :
    Integrable (fun t : ℝ => (1+t-c)^2+v) (gaussianReal 0 σ) := by
  have h0 : Integrable (fun _ : ℝ => (1-c)^2+v) (gaussianReal 0 σ) := integrable_const _
  have h1 : Integrable (fun t : ℝ => t) (gaussianReal 0 σ) :=
    (memLp_id_gaussianReal (μ := 0) (v := σ) 1).integrable (by norm_num)
  have h2 := gaussian_sq_integrable σ
  convert! (h2.add (h1.const_mul (2*(1-c)))).add h0 using 1
  funext t; simp only [Pi.add_apply]; ring_nf

theorem residual_quadratic_integrable {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (c v : ℝ) :
    Integrable (fun t => residual N δ t *((1+t-c)^2+v)) (gaussianReal 0 1) := by
  have hi (i : Fin (2*N+1)) : Integrable (fun t => hat N δ i t *((1+t-c)^2+v)) (gaussianReal 0 1) :=
    (by fun_prop : Continuous (fun t => hat N δ i t *((1+t-c)^2+v))).integrable_of_hasCompactSupport
      ((hat_compactSupport hδ i).mul_right)
  convert! (quadratic_integrable c v 1).sub (integrable_finsetSum _ (fun i _ => hi i)) using 1
  funext t
  simp only [Pi.sub_apply]
  dsimp [residual]
  rw [sub_mul,one_mul,Finset.sum_mul]

theorem tail_integral_bound {N : ℕ} {δ h R c v : ℝ} (hδ : 0 < δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hR : N*δ = R) (hc : |c-1| ≤ h)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (∫ t, residual N δ t * ((1+t-c)^2+v) / mass (gaussianReal 0 1) (tent 1 h) ∂gaussianReal 0 1) ≤
      972/h * Real.exp (-(R^2/4)) := by
  let β := mass (gaussianReal 0 1) (tent 1 h)
  have hb : 0 < β := tent_mass_pos hh
  have hβ : β⁻¹ ≤ 54/h := middle_mass_bound hh hh1
  have hi : Integrable (fun t => gaussianPDFReal 0 1 t *
      (residual N δ t*((1+t-c)^2+v)/β)) volume :=
    density_integrable (by norm_num) ((residual_quadratic_integrable hδ c v).div_const β)
  have hj : Integrable (fun t => (324/h*Real.exp (-(R^2/4))) *
      (gaussianPDFReal 0 2 t*(1+t^2))) volume :=
    (density_integrable (by norm_num) (gaussian_poly_integrable 2)).const_mul _
  have hpoint (t : ℝ) : gaussianPDFReal 0 1 t *
      (residual N δ t*((1+t-c)^2+v)/β) ≤ (324/h*Real.exp (-(R^2/4))) *
      (gaussianPDFReal 0 2 t*(1+t^2)) := by
    by_cases ht : |t| ≤ R
    · rw [residual_eq_zero hδ (by rwa [hR])]
      simp only [zero_mul,zero_div,mul_zero]
      exact mul_nonneg (by positivity) (mul_nonneg (gaussianPDFReal_nonneg ..) (by positivity))
    have hR0 : 0 ≤ R := by rw [← hR]; positivity
    have htsq : R^2 ≤ t^2 := by nlinarith [sq_abs t, abs_nonneg t,lt_of_not_ge ht]
    have hd := density_tail_bound htsq
    have hn : (1+t-c)^2+v ≤ 3*(1+t^2) := by
      have hc' := abs_le.mp hc
      nlinarith [sq_nonneg (t-(1-c)),sq_nonneg t]
    have hn0 : 0 ≤ (1+t-c)^2+v := add_nonneg (sq_nonneg _) hv0
    have hrn : residual N δ t*((1+t-c)^2+v) ≤ 3*(1+t^2) := by
      have := mul_le_mul (residual_le_one N δ t) hn hn0 (by norm_num : (0:ℝ)≤1)
      simpa using this
    have hq : residual N δ t*((1+t-c)^2+v)/β ≤ (54/h)*(3*(1+t^2)) := by
      rw [div_eq_mul_inv]
      calc _ ≤ (3*(1+t^2))*(54/h) := mul_le_mul hrn hβ (inv_nonneg.mpr hb.le) (by positivity)
        _ = _ := by ring_nf
    calc
      _ ≤ (2*Real.exp (-(R^2/4))*gaussianPDFReal 0 2 t) * ((54/h)*(3*(1+t^2))) :=
        mul_le_mul hd hq (div_nonneg (mul_nonneg (residual_nonneg N δ t) hn0) hb.le)
          (mul_nonneg (by positivity) (gaussianPDFReal_nonneg ..))
      _ = _ := by ring_nf
  have hbound := integral_mono hi hj hpoint
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0)≠0)]
  change (∫ t, gaussianPDFReal 0 1 t*(residual N δ t*((1+t-c)^2+v)/β)) ≤ _
  apply hbound.trans
  rw [integral_const_mul]
  change _ * (∫ t, gaussianPDFReal 0 2 t • (1+t^2)) ≤ _
  rw [← integral_gaussianReal_eq_integral_smul (by norm_num : (2:ℝ≥0)≠0)]
  rw [integral_add (integrable_const 1) (gaussian_sq_integrable 2), integral_const,
    gaussian_sq_integral]
  norm_num
  ring_nf
  exact le_rfl

end GaussianGain
end SquareRootDegree

end

end OAI

-- ---- platform node ----
open OAI OAI.SquareRootDegree OAI.SquareRootDegree.GaussianGain
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
open SmoothGaussian SmoothSelector

theorem solution {N : ℕ} {δ h R c v : ℝ} (hδ : 0 < δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hR : N*δ = R) (hc : |c-1| ≤ h)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (∫ t, residual N δ t * ((1+t-c)^2+v) / mass (gaussianReal 0 1) (tent 1 h) ∂gaussianReal 0 1) ≤
      972/h * Real.exp (-(R^2/4)) := by
  first
    | exact OAI.SquareRootDegree.GaussianGain.tail_integral_bound hδ hh hh1 hR hc hv0 hv1
    | exact OAI.SquareRootDegree.GaussianGain.tail_integral_bound
    | (apply OAI.SquareRootDegree.GaussianGain.tail_integral_bound <;> assumption)
    | (intros; apply OAI.SquareRootDegree.GaussianGain.tail_integral_bound <;> assumption)
