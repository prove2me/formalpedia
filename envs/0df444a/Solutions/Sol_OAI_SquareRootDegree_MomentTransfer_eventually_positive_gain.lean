-- Prove2me | solution 1 for OAI.SquareRootDegree.MomentTransfer.eventually_positive_gain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:29:34.287893+00:00
-- url     : https://prove2.me/submissions/e70eb72e-6e0b-464d-a5b8-cc7f33f868ec

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/MomentTransfer.lean:L210-L233
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.MomentTransfer.eventually_positive_gain. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_MomentTransfer
import Theorems.Thm_OAI_SquareRootDegree_GaussianGain_tail_integral_bound
import Theorems.Thm_OAI_SquareRootDegree_SmoothGaussian_beta_lower
import Theorems.Thm_OAI_SquareRootDegree_SmoothGaussian_weighted_interval_bounds
import Theorems.Thm_OAI_SquareRootDegree_SmoothSelector_hat_local

-- ---- from OAI.Combinatorics.BooleanFunctions.SmoothGaussian ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace SmoothGaussian

theorem tent_nonneg (a h x : ℝ) : 0 ≤ tent a h x := le_max_left _ _

theorem tent_eq_zero {a h x : ℝ} (hh : 0 < h) (hx : h ≤ |x-a|) :
    tent a h x = 0 := by
  unfold tent
  apply max_eq_left
  have : 1 ≤ |x-a|/h := (one_le_div hh).mpr hx
  linarith

theorem tent_ne_zero_iff {a h x : ℝ} (hh : 0 < h) :
    tent a h x ≠ 0 ↔ |x-a| < h := by
  constructor
  · intro hn
    exact lt_of_not_ge (fun hx => hn (tent_eq_zero hh hx))
  · intro hx
    apply ne_of_gt
    apply lt_of_lt_of_le _ (le_max_right _ _)
    have := (div_lt_one hh).mpr hx
    linarith

theorem tent_support {a h : ℝ} (hh : 0 < h) :
    Function.support (tent a h) ⊆ Set.Icc (a-h) (a+h) := by
  intro x hx
  have he := (tent_ne_zero_iff hh).mp hx
  rw [abs_lt] at he
  constructor <;> linarith

theorem tent_compactSupport {a h : ℝ} (hh : 0 < h) : HasCompactSupport (tent a h) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := a-h) (b := a+h))
  intro x hx
  by_contra hn
  exact hx (tent_support hh hn)

theorem integrable_tent_mul {a h : ℝ} (hh : 0 < h) (p : ℝ → ℝ) (hp : Continuous p)
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ] :
    Integrable (fun x => tent a h x * p x) μ := by
  apply ((continuous_tent a h).mul hp).integrable_of_hasCompactSupport
  exact (tent_compactSupport hh).mul_right

theorem tent_mass_pos {a h : ℝ} (hh : 0 < h) :
    0 < mass (gaussianReal 0 1) (tent a h) := by
  apply lt_of_lt_of_le _ (beta_lower hh)
  positivity

theorem tent_moments {a h : ℝ} (hh : 0 < h) :
    |mean (gaussianReal 0 1) (tent a h)-a| ≤ h ∧
    0 ≤ variance (gaussianReal 0 1) (tent a h) ∧
    variance (gaussianReal 0 1) (tent a h) ≤ h^2 := by
  apply weighted_interval_bounds (gaussianReal 0 1) (tent a h) hh.le (tent_nonneg a h)
  · intro x hx
    exact le_of_lt ((tent_ne_zero_iff hh).mp hx)
  · simpa using integrable_tent_mul (a := a) hh (fun _ => 1) continuous_const (gaussianReal 0 1)
  · exact integrable_tent_mul hh id continuous_id (gaussianReal 0 1)
  · exact integrable_tent_mul hh (fun x => x^2) (by fun_prop) (gaussianReal 0 1)
  · exact tent_mass_pos hh

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

theorem weight_nonneg (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (t : ℝ) :
    0 ≤ weight N δ i t := by
  unfold weight
  split_ifs <;> linarith [hat_nonneg N δ i t, hats_sum_le_one N δ t]

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

theorem gaussian_sq_integrable (v : ℝ≥0) : Integrable (fun x : ℝ => x^2) (gaussianReal 0 v) := by
  simpa using (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq

theorem density_div_mass_bound {a h δ R t : ℝ} (hh : 0 < h)
    (hδh : δ+h ≤ 1) (ha : |a-(1+t)| ≤ δ) (ht : |t| ≤ R+1) :
    gaussianPDFReal 0 1 t / mass (gaussianReal 0 1) (tent a h) ≤
      2/h * Real.exp (2*R+4) := by
  have hb := tent_mass_pos (a := a) hh
  have hA : |a|+h ≤ |t|+2 := by
    have he : |a| ≤ |a-(1+t)|+|1+t| := by
      simpa using abs_add_le (a-(1+t)) (1+t)
    have he' : |1+t| ≤ 1+|t| := by simpa using abs_add_le (1:ℝ) t
    linarith
  have hsq : (|a|+h)^2 ≤ (|t|+2)^2 := by
    nlinarith [abs_nonneg a, abs_nonneg t]
  have he : Real.exp (-t^2/2) ≤ Real.exp (-((|a|+h)^2)/2) * Real.exp (2*R+4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_abs t]
  apply (div_le_iff₀ hb).mpr
  have hl := beta_lower (a := a) hh
  have hp : 0 ≤ 2/h * Real.exp (2*R+4) := by positivity
  calc
    gaussianPDFReal 0 1 t ≤ (Real.sqrt (2*Real.pi))⁻¹ *
        (Real.exp (-((|a|+h)^2)/2) * Real.exp (2*R+4)) := by
      simpa only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero] using
        mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = (2/h * Real.exp (2*R+4)) *
      (h/2 * ((Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-((|a|+h)^2)/2))) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hl hp

theorem centralKernel_support {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (μ v β : Fin (2*N+1) → ℝ) {t : ℝ} (ht : (N+1)*δ < |t|) :
    centralKernel N δ μ v β t = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : hat N δ i t = 0 := by
    by_contra hn
    exact (not_le_of_gt ht) (hat_support hδ hn)
  simp [hi]

theorem centralKernel_compactSupport {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (μ v β : Fin (2*N+1) → ℝ) : HasCompactSupport (centralKernel N δ μ v β) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(N+1)*δ) (b := (N+1)*δ))
  intro t ht
  apply centralKernel_support hδ
  by_contra hn
  have hh := abs_le.mp (le_of_not_gt hn)
  apply ht
  constructor <;> linarith [hh.1,hh.2]

theorem central_density_bound {N : ℕ} {δ h R M : ℝ} (hδ : 0 < δ)
    (hh : 0 < h) (hsmall : δ+h ≤ 1) (hR : N*δ = R)
    (μ v : Fin (2*N+1) → ℝ)
    (hμ : ∀ i, |μ i-center N δ i| ≤ h) (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ M)
    (t : ℝ) :
    gaussianPDFReal 0 1 t *
      centralKernel N δ μ v (fun i => mass (gaussianReal 0 1) (tent (center N δ i) h)) t ≤
        (2/h * Real.exp (2*R+4)) * ((δ+h)^2+M) := by
  let K := 2/h * Real.exp (2*R+4)
  let B := (δ+h)^2+M
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hM : 0 ≤ M := (hv0 ⟨0,by omega⟩).trans (hv _)
  have hB : 0 ≤ B := add_nonneg (sq_nonneg _) hM
  unfold centralKernel
  rw [Finset.mul_sum]
  calc
    ∑ i, gaussianPDFReal 0 1 t *
        (hat N δ i t * ((1+t-μ i)^2+v i) /
          mass (gaussianReal 0 1) (tent (center N δ i) h)) ≤
        ∑ i, hat N δ i t * (K*B) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : hat N δ i t = 0
      · simp [hi]
      have ha := hat_local hδ hi
      have ht := hat_support hδ hi
      have ht' : |t| ≤ R+1 := by rw [add_mul, hR] at ht; nlinarith
      have he := density_div_mass_bound hh hsmall ha.le ht'
      have herr : |1+t-μ i| ≤ δ+h := by
        have hx : |1+t-μ i| ≤ |center N δ i-(1+t)|+|μ i-center N δ i| := by
          have := abs_add_le (center N δ i-(1+t)) (μ i-center N δ i)
          simpa only [show center N δ i-(1+t)+(μ i-center N δ i) = -(1+t-μ i) by ring_nf,
            abs_neg] using this
        linarith [hμ i]
      have hnum : (1+t-μ i)^2+v i ≤ B := by
        dsimp [B]
        nlinarith [sq_abs (1+t-μ i), abs_nonneg (1+t-μ i), hv i]
      have hnum0 : 0 ≤ (1+t-μ i)^2+v i := add_nonneg (sq_nonneg _) (hv0 i)
      calc
        _ = hat N δ i t *
          ((gaussianPDFReal 0 1 t / mass (gaussianReal 0 1) (tent (center N δ i) h)) *
            ((1+t-μ i)^2+v i)) := by ring_nf
        _ ≤ hat N δ i t * (K*B) :=
          mul_le_mul_of_nonneg_left (mul_le_mul he hnum hnum0 hK) (hat_nonneg ..)
    _ = (∑ i, hat N δ i t) * (K*B) := (Finset.sum_mul ..).symm
    _ ≤ K*B := by nlinarith [hats_sum_le_one N δ t, mul_nonneg hK hB]

theorem central_integral_bound {N : ℕ} {δ h R M : ℝ} (hδ : 0 < δ)
    (hh : 0 < h) (hsmall : δ+h ≤ 1) (hR : N*δ = R)
    (μ v : Fin (2*N+1) → ℝ)
    (hμ : ∀ i, |μ i-center N δ i| ≤ h) (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ M) :
    (∫ t, centralKernel N δ μ v
       (fun i => mass (gaussianReal 0 1) (tent (center N δ i) h)) t ∂gaussianReal 0 1) ≤
      4*(R+δ)/h * Real.exp (2*R+4) * ((δ+h)^2+M) := by
  let β := fun i => mass (gaussianReal 0 1) (tent (center N δ i) h)
  let f := fun t => gaussianPDFReal 0 1 t * centralKernel N δ μ v β t
  have hf : Integrable f volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · dsimp [f]; unfold gaussianPDFReal; fun_prop
    · exact (centralKernel_compactSupport hδ μ v β).mul_left
  have he : ∫ t in Set.Icc (-(R+δ)) (R+δ), f t = ∫ t, f t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    dsimp [f]
    rw [centralKernel_support hδ μ v β]
    · exact mul_zero _
    · by_contra hn
      have hab := abs_le.mp (le_of_not_gt hn)
      rw [add_mul, hR, one_mul] at hab
      exact ht ⟨by linarith [hab.1],hab.2⟩
  have hbound := integral_mono_ae hf.integrableOn (integrable_const
    ((2/h * Real.exp (2*R+4))*((δ+h)^2+M)))
    (ae_of_all (volume.restrict (Set.Icc (-(R+δ)) (R+δ)))
      (central_density_bound hδ hh hsmall hR μ v hμ hv0 hv))
  rw [he] at hbound
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0) ≠ 0)]
  change (∫ t, f t) ≤ _
  apply hbound.trans
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc, smul_eq_mul]
  have hn : 0 ≤ R+δ-(-(R+δ)) := by
    have : 0 ≤ (N:ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
    rw [hR] at this
    linarith
  rw [ENNReal.toReal_ofReal hn]
  ring_nf

  exact le_rfl

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

theorem gridN_pos : 0 < gridN := by norm_num [gridN]
theorem width_pos : 0 < width := by unfold width; positivity
theorem step_pos : 0 < step := by
  exact div_pos (by norm_num [radius]) (by exact_mod_cast gridN_pos)
theorem step_small : step+width ≤ 1 := by norm_num [step,radius,gridN,width]
theorem width_le_one : width ≤ 1 := by linarith [step_small,step_pos]
theorem grid_radius : (gridN:ℝ)*step = radius := by
  unfold step; field_simp [show (gridN:ℝ)≠0 by exact_mod_cast gridN_pos.ne']
theorem variance_numeric : (2*gridN+1:ℝ)*width^2 < 1/4 := by
  norm_num [gridN,width]

theorem central_numeric :
    4*(radius+step)/width * Real.exp (2*radius+4) *
      ((step+width)^2+(2*gridN+1:ℝ)*width^2) < 1/4 := by
  have he : Real.exp 196 < (3:ℝ)^196 := by
    calc Real.exp 196 = (Real.exp 1)^196 := by rw [← Real.exp_nat_mul]; norm_num
      _ < 3^196 := pow_lt_pow_left₀ (lt_trans Real.exp_one_lt_d9 (by norm_num))
        (Real.exp_pos _).le (by norm_num)
  have hp : 0 < 4*(radius+step)/width*((step+width)^2+(2*gridN+1:ℝ)*width^2) := by
    dsimp [radius,step,width,gridN]; positivity
  calc _ = Real.exp 196 * (4*(radius+step)/width*((step+width)^2+(2*gridN+1:ℝ)*width^2)) := by
           norm_num [radius]; ring_nf
    _ < 3^196 * (4*(radius+step)/width*((step+width)^2+(2*gridN+1:ℝ)*width^2)) :=
      mul_lt_mul_of_pos_right he hp
    _ < 1/4 := by norm_num [radius,step,width,gridN]

theorem tail_numeric : 972/width*Real.exp (-(radius^2/4)) < 1/4 := by
  have he : (2:ℝ)^2304 < Real.exp 2304 := by
    calc (2:ℝ)^2304 < (Real.exp 1)^2304 :=
           pow_lt_pow_left₀ (lt_trans (by norm_num) Real.exp_one_gt_d9) (by norm_num) (by norm_num)
      _ = Real.exp 2304 := by rw [← Real.exp_nat_mul]; norm_num
  have hi : Real.exp (-2304) < ((2:ℝ)^2304)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_lt_inv₀ (Real.exp_pos _) (by positivity)).mpr he
  calc _ = 972/width*Real.exp (-2304) := by norm_num [radius]
    _ < 972/width*((2:ℝ)^2304)⁻¹ := mul_lt_mul_of_pos_left hi (by unfold width; positivity)
    _ < 1/4 := by
      rw [show (2:ℝ)^2304 = ((2:ℝ)^128)^18 by rw [← pow_mul]]
      norm_num [width]

theorem beta_pos (i : Leaves) : 0 < beta i := tent_mass_pos width_pos
theorem mu_close (i : Leaves) : |mu i-center gridN step i| ≤ width :=
  (tent_moments width_pos).1
theorem sigma_nonneg (i : Leaves) : 0 ≤ sigma i := (tent_moments width_pos).2.1
theorem sigma_bound (i : Leaves) : sigma i ≤ width^2 := (tent_moments width_pos).2.2
theorem otherVariance_nonneg (i : Leaves) : 0 ≤ otherVariance i :=
  Finset.sum_nonneg (fun _ _ => sigma_nonneg _)
theorem otherVariance_bound (i : Leaves) : otherVariance i ≤ (2*gridN+1:ℝ)*width^2 := by
  calc otherVariance i ≤ ∑ j : Leaves, sigma j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun j _ _ => sigma_nonneg j)
    _ ≤ ∑ _ : Leaves, width^2 := Finset.sum_le_sum (fun j _ => sigma_bound j)
    _ = _ := by simp [Leaves]
theorem otherVariance_le_one (i : Leaves) : otherVariance i ≤ 1 :=
  (otherVariance_bound i).trans (le_trans variance_numeric.le (by norm_num))

theorem kernel_split_general (N : ℕ) (δ : ℝ) (μ v β : Fin (2*N+1) → ℝ) (t : ℝ) :
    (∑ i, weight N δ i t *((1+t-μ i)^2+v i)/β i) = centralKernel N δ μ v β t +
    residual N δ t *((1+t-μ (middle N))^2+v (middle N))/β (middle N) := by
  unfold weight centralKernel residual
  simp only [add_mul,add_div,Finset.sum_add_distrib]
  congr 1
  simp only [ite_mul,zero_mul,ite_div,zero_div,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem kernel_split (t : ℝ) : kernel t = centralKernel gridN step mu otherVariance beta t +
    residual gridN step t *((1+t-mu (middle gridN))^2+otherVariance (middle gridN))/beta (middle gridN) :=
  kernel_split_general gridN step mu otherVariance beta t

theorem J_lt_half : J < 1/2 := by
  have hc := central_integral_bound step_pos width_pos step_small grid_radius mu otherVariance
    mu_close otherVariance_nonneg otherVariance_bound
  have ht := tail_integral_bound step_pos width_pos width_le_one grid_radius
    (show |mu (middle gridN)-1| ≤ width by simpa using mu_close (middle gridN))
    (otherVariance_nonneg (middle gridN)) (otherVariance_le_one (middle gridN))
  have hb : beta (middle gridN) = mass (gaussianReal 0 1) (tent 1 width) := by
    simp [beta,leafTest]
  unfold J
  simp_rw [kernel_split]
  rw [integral_add ((centralKernel_continuous ..).integrable_of_hasCompactSupport
    (centralKernel_compactSupport step_pos ..))
      ((residual_quadratic_integrable step_pos _ _).div_const _), hb]
  change (∫ t, centralKernel gridN step mu otherVariance beta t ∂gaussianReal 0 1) + _ < _
  change (∫ t, centralKernel gridN step mu otherVariance beta t ∂gaussianReal 0 1) ≤ _ at hc
  linarith [central_numeric,tail_numeric]

theorem positive_gaussian_deficit :
    0 < (∏ i : Leaves, beta i) * (1+totalVariance-J) := by
  have hp : 0 < ∏ i : Leaves, beta i := Finset.prod_pos (fun _ _ => beta_pos _)
  have hs : 0 ≤ totalVariance := Finset.sum_nonneg (fun _ _ => sigma_nonneg _)
  exact mul_pos hp (by linarith [J_lt_half])

end GaussianGain
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.MomentTransfer ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace MomentTransfer
open SmoothGaussian SmoothSelector GaussianGain
/-- Only compact continuous test functions are passed through weak convergence. -/
theorem compact_test_tendsto {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (T : ∀ n, Ω n → ℝ) (hT : TendstoInDistribution T atTop (fun x : ℝ => x) P (gaussianReal 0 1))
    (f : ℝ → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun n => ∫ x, f (T n x) ∂P n) atTop (𝓝 (∫ x, f x ∂gaussianReal 0 1)) := by
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hT.tendsto)
    (ofCompactSupport f hf hc)
  change Tendsto (fun n => ∫ x, f x ∂(P n).map (T n)) atTop
    (𝓝 (∫ x, f x ∂(gaussianReal 0 1).map (fun x => x))) at h
  rw [Measure.map_id'] at h
  have he (n : ℕ) : (∫ x, f x ∂(P n).map (T n)) =
      ∫ x, f (T n x) ∂P n := by
    rw [integral_map (hT.forall_aemeasurable n) hf.aestronglyMeasurable]
  simpa only [he] using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gain_tendsto (l s : ℕ → Fin 3 → ι → ℝ) (l₀ s₀ : Fin 3 → ι → ℝ)
    (hl : ∀ k i, Tendsto (fun n => l n k i) atTop (𝓝 (l₀ k i)))
    (hs : ∀ k i, Tendsto (fun n => s n k i) atTop (𝓝 (s₀ k i)))
    (hb : ∀ i, l₀ 0 i ≠ 0) :
    Tendsto (fun n => gain (l n) (s n)) atTop (𝓝 (gain l₀ s₀)) := by
  have hm (i : ι) : Tendsto (fun n => means (l n) i) atTop (𝓝 (means l₀ i)) :=
    (hl 1 i).div (hl 0 i) (hb i)
  have hv (i : ι) : Tendsto (fun n => vars (l n) i) atTop (𝓝 (vars l₀ i)) :=
    ((hl 2 i).div (hl 0 i) (hb i)).sub ((hm i).pow 2)
  have hvsum := tendsto_finsetSum Finset.univ (fun i _ => hv i)
  have hother (i : ι) := tendsto_finsetSum (Finset.univ.erase i) (fun j _ => hv j)
  have hj (i : ι) : Tendsto (fun n => (s n 2 i + 2*(1-means (l n) i)*s n 1 i +
      ((1-means (l n) i)^2+∑ j ∈ Finset.univ.erase i, vars (l n) j)*s n 0 i) / l n 0 i)
      atTop (𝓝 ((s₀ 2 i + 2*(1-means l₀ i)*s₀ 1 i +
      ((1-means l₀ i)^2+∑ j ∈ Finset.univ.erase i, vars l₀ j)*s₀ 0 i) / l₀ 0 i)) := by
    exact (((hs 2 i).add ((tendsto_const_nhds.mul (tendsto_const_nhds.sub (hm i))).mul (hs 1 i))).add
      ((((tendsto_const_nhds.sub (hm i)).pow 2).add (hother i)).mul (hs 0 i))).div (hl 0 i) (hb i)
  exact (tendsto_finsetProd Finset.univ (fun i _ => hl 0 i)).mul
    ((tendsto_const_nhds.add hvsum).sub (tendsto_finsetSum Finset.univ (fun i _ => hj i)))

theorem hat_le_one (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (t : ℝ) :
    hat N δ i t ≤ 1 := by
  exact (Finset.single_le_sum (fun j _ => hat_nonneg N δ j t) (Finset.mem_univ i)).trans
    (hats_sum_le_one N δ t)

theorem hat_moment_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (T : Ω → ℝ) (hT : Measurable T) (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (k : ℕ)
    (hi : Integrable (fun x => (T x)^k) P) :
    Integrable (fun x => hat N δ i (T x)*(T x)^k) P := by
  apply hi.norm.mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hat_nonneg ..)]
  exact mul_le_of_le_one_left (abs_nonneg _) (hat_le_one ..)

theorem weight_moment_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (T : Ω → ℝ) (hT : Measurable T) (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (k : ℕ)
    (hi : Integrable (fun x => (T x)^k) P) :
    (∫ x, weight N δ i (T x)*(T x)^k ∂P) =
      (∫ x, hat N δ i (T x)*(T x)^k ∂P) +
        if i = middle N then (∫ x, (T x)^k ∂P) -
          ∑ j, ∫ x, hat N δ j (T x)*(T x)^k ∂P else 0 := by
  have hh (j) := hat_moment_integrable T hT N δ j k hi
  by_cases he : i = middle N
  · subst i
    simp only [weight,ite_true,add_mul,sub_mul,one_mul,Finset.sum_mul]
    rw [integral_add (f := fun x => hat N δ (middle N) (T x)*(T x)^k)
      (g := fun x => (T x)^k-∑ j, hat N δ j (T x)*(T x)^k)
      (hh (middle N)) (hi.sub (integrable_finsetSum Finset.univ (fun j _ => hh j))),
      integral_sub hi (integrable_finsetSum Finset.univ (fun j _ => hh j)),
      integral_finsetSum Finset.univ (fun j _ => hh j)]
  · simp only [weight,he,ite_false,add_zero]

theorem gaussian_pow_integrable (k : Fin 3) :
    Integrable (fun x : ℝ => x^(k:ℕ)) (gaussianReal 0 1) := by
  fin_cases k
  · simp only [pow_zero]; exact integrable_const _
  · change Integrable (fun x : ℝ => x^1) (gaussianReal 0 1)
    simp only [pow_one]
    exact (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl
  · exact gaussian_sq_integrable 1

theorem leaf_moments_tendsto {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (T : ∀ n, Ω n → ℝ) (hT : TendstoInDistribution T atTop (fun x : ℝ => x) P (gaussianReal 0 1))
    (k : Fin 3) (i : Leaves) :
    Tendsto (fun n => moments (P n) (T n) leafTest k i) atTop
      (𝓝 (moments (gaussianReal 0 1) id leafTest k i)) := by
  apply compact_test_tendsto P T hT
  · exact (continuous_tent _ _).mul (continuous_id.pow _)
  · exact (tent_compactSupport width_pos).mul_right

theorem selector_moments_tendsto {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (T : ∀ n, Ω n → ℝ) (hm : ∀ n, Measurable (T n))
    (hT : TendstoInDistribution T atTop (fun x : ℝ => x) P (gaussianReal 0 1))
    (hi : ∀ n (k : Fin 3), Integrable (fun x => (T n x)^(k:ℕ)) (P n))
    (hM : ∀ k : Fin 3, Tendsto (fun n => ∫ x, (T n x)^(k:ℕ) ∂P n) atTop
      (𝓝 (∫ x : ℝ, x^(k:ℕ) ∂gaussianReal 0 1))) (k : Fin 3) (i : Leaves) :
    Tendsto (fun n => moments (P n) (T n) selectorTest k i) atTop
      (𝓝 (moments (gaussianReal 0 1) id selectorTest k i)) := by
  have hh (j : Leaves) := compact_test_tendsto P T hT
    (fun x => hat gridN step j x*x^(k:ℕ))
    ((hat_continuous ..).mul (continuous_id.pow _)) ((hat_compactSupport step_pos j).mul_right)
  simp only [moments,selectorTest]
  simp_rw [weight_moment_eq (T _) (hm _) _ _ _ _ (hi _ k),
    weight_moment_eq id measurable_id _ _ _ _ (gaussian_pow_integrable k)]
  by_cases he : i = middle gridN
  · simp only [he,ite_true]
    exact (hh (middle gridN)).add ((hM k).sub (tendsto_finsetSum Finset.univ (fun j _ => hh j)))
  · simp only [he,ite_false,add_zero]
    exact hh i

theorem weight_le_one (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (t : ℝ) :
    weight N δ i t ≤ 1 := by
  calc weight N δ i t ≤ ∑ j, weight N δ j t :=
      Finset.single_le_sum (fun j _ => weight_nonneg N δ j t) (Finset.mem_univ i)
    _ = 1 := weight_sum ..

theorem gaussian_selector_integrable (k : Fin 3) (i : Leaves) :
    Integrable (fun x : ℝ => selectorTest i x*x^(k:ℕ)) (gaussianReal 0 1) := by
  apply (gaussian_pow_integrable k).norm.mono' (by dsimp [selectorTest]; fun_prop)
  filter_upwards [] with x
  change |weight gridN step i x*x^(k:ℕ)| ≤ |x^(k:ℕ)|
  rw [abs_mul,abs_of_nonneg (weight_nonneg ..)]
  exact mul_le_of_le_one_left (abs_nonneg _) (weight_le_one ..)

theorem quadratic_moment_formula {P : Measure ℝ} (w : ℝ → ℝ)
    (h0 : Integrable w P) (h1 : Integrable (fun x => w x*x) P)
    (h2 : Integrable (fun x => w x*x^2) P) (a v : ℝ) :
    (∫ x, w x*((1+x-a)^2+v) ∂P) = (∫ x, w x*x^2 ∂P) +
      2*(1-a)*(∫ x, w x*x ∂P) + ((1-a)^2+v)*(∫ x, w x ∂P) := by
  have he : (fun x => w x*((1+x-a)^2+v)) = fun x =>
      w x*x^2 + (2*(1-a))*(w x*x) + ((1-a)^2+v)*w x := by funext x; ring
  rw [he,integral_add (f := fun x => w x*x^2+(2*(1-a))*(w x*x))
    (g := fun x => ((1-a)^2+v)*w x) (h2.add (h1.const_mul _)) (h0.const_mul _),
    integral_add h2 (h1.const_mul _), integral_const_mul,integral_const_mul]

theorem gaussianGain_eq : gain gaussianLeafMoments gaussianSelectorMoments =
    (∏ i : Leaves, GaussianGain.beta i) * (1+totalVariance-J) := by
  have hi0 (i) : Integrable (selectorTest i) (gaussianReal 0 1) := by
    simpa only [Fin.val_zero,pow_zero,mul_one] using gaussian_selector_integrable 0 i
  have hi1 (i) : Integrable (fun x => selectorTest i x*x) (gaussianReal 0 1) := by
    simpa only [Fin.val_one,pow_one] using gaussian_selector_integrable 1 i
  have hi2 (i) : Integrable (fun x => selectorTest i x*x^2) (gaussianReal 0 1) :=
    gaussian_selector_integrable 2 i
  have hik (i) : Integrable (fun x => selectorTest i x*((1+x-mu i)^2+otherVariance i)/GaussianGain.beta i)
      (gaussianReal 0 1) := by
    have he : (fun x => selectorTest i x*((1+x-mu i)^2+otherVariance i)) = fun x =>
        selectorTest i x*x^2 + (2*(1-mu i))*(selectorTest i x*x) +
          ((1-mu i)^2+otherVariance i)*selectorTest i x := by funext x; ring
    apply Integrable.div_const
    rw [he]
    exact ((hi2 i).add ((hi1 i).const_mul _)).add ((hi0 i).const_mul _)
  have hJ : J = ∑ i, (gaussianSelectorMoments 2 i + 2*(1-mu i)*gaussianSelectorMoments 1 i +
      ((1-mu i)^2+otherVariance i)*gaussianSelectorMoments 0 i) / GaussianGain.beta i := by
    change (∫ t, ∑ i, selectorTest i t*((1+t-mu i)^2+otherVariance i)/GaussianGain.beta i
      ∂gaussianReal 0 1) = _
    rw [integral_finsetSum Finset.univ (fun i _ => hik i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_div,quadratic_moment_formula _ (hi0 i) (hi1 i) (hi2 i)]
    simp only [gaussianSelectorMoments,moments,Fin.val_zero,Fin.val_one,pow_zero,pow_one,mul_one,id_eq]
    rfl
  simp only [gain,gaussianLeaf_zero,gaussianLeaf_mean,gaussianLeaf_var,totalVariance,hJ,otherVariance]

theorem gaussianGain_pos : 0 < gain gaussianLeafMoments gaussianSelectorMoments := by
  rw [gaussianGain_eq]
  exact positive_gaussian_deficit

theorem eventually_positive_gain {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (T : ∀ n, Ω n → ℝ) (hm : ∀ n, Measurable (T n))
    (hT : TendstoInDistribution T atTop (fun x : ℝ => x) P (gaussianReal 0 1))
    (hi : ∀ n (k : Fin 3), Integrable (fun x => (T n x)^(k:ℕ)) (P n))
    (hM : ∀ k : Fin 3, Tendsto (fun n => ∫ x, (T n x)^(k:ℕ) ∂P n) atTop
      (𝓝 (∫ x : ℝ, x^(k:ℕ) ∂gaussianReal 0 1))) :
    ∀ᶠ n in atTop, (∀ i : Leaves, 0 < moments (P n) (T n) leafTest 0 i) ∧
      eta < gain (moments (P n) (T n) leafTest) (moments (P n) (T n) selectorTest) := by
  have hl := leaf_moments_tendsto P T hT
  have hs := selector_moments_tendsto P T hm hT hi hM
  have hg := gain_tendsto (fun n => moments (P n) (T n) leafTest)
    (fun n => moments (P n) (T n) selectorTest) gaussianLeafMoments gaussianSelectorMoments
    hl hs (fun i => by rw [gaussianLeaf_zero]; exact (beta_pos i).ne')
  have he : eta < gain gaussianLeafMoments gaussianSelectorMoments := by
    dsimp [eta]; linarith [gaussianGain_pos]
  have hge := (tendsto_order.mp hg).1 eta he
  have hp : ∀ᶠ n in atTop, ∀ i : Leaves, 0 < moments (P n) (T n) leafTest 0 i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hl 0 i).eventually (lt_mem_nhds (by
      change 0 < gaussianLeafMoments 0 i
      rw [gaussianLeaf_zero]; exact beta_pos i))
  exact hp.and hge

end MomentTransfer
end SquareRootDegree

end

end OAI

-- ---- platform node ----
open OAI OAI.SquareRootDegree OAI.SquareRootDegree.MomentTransfer
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
open SmoothGaussian SmoothSelector GaussianGain
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (T : ∀ n, Ω n → ℝ) (hm : ∀ n, Measurable (T n))
    (hT : TendstoInDistribution T atTop (fun x : ℝ => x) P (gaussianReal 0 1))
    (hi : ∀ n (k : Fin 3), Integrable (fun x => (T n x)^(k:ℕ)) (P n))
    (hM : ∀ k : Fin 3, Tendsto (fun n => ∫ x, (T n x)^(k:ℕ) ∂P n) atTop
      (𝓝 (∫ x : ℝ, x^(k:ℕ) ∂gaussianReal 0 1))) :
    ∀ᶠ n in atTop, (∀ i : Leaves, 0 < moments (P n) (T n) leafTest 0 i) ∧
      eta < gain (moments (P n) (T n) leafTest) (moments (P n) (T n) selectorTest) := by
  first
    | exact OAI.SquareRootDegree.MomentTransfer.eventually_positive_gain P T hm hT hi hM
    | exact OAI.SquareRootDegree.MomentTransfer.eventually_positive_gain
    | (apply OAI.SquareRootDegree.MomentTransfer.eventually_positive_gain <;> assumption)
    | (intros; apply OAI.SquareRootDegree.MomentTransfer.eventually_positive_gain <;> assumption)
