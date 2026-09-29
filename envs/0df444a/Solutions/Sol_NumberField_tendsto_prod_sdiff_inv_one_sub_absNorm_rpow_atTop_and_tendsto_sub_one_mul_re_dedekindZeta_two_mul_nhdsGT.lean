-- Prove2me | solution 1 for NumberField.tendsto_prod_sdiff_inv_one_sub_absNorm_rpow_atTop_and_tendsto_sub_one_mul_re_dedekindZeta_two_mul_nhdsGT
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4156b484-f074-5289-896a-f5d06945f1b9

import Theorems.Thm_NumberField_hasProd_and_tendsto_sub_one_mul_dedekindZeta_two_mul_mul_dedekindZeta_two_mul_sub_one_nhdsGT
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_tendsto_prod_sdiff_inv_one_sub_absNorm_rpow_atTop_and_tendsto_sub_one_mul_re_dedekindZeta_two_mul_nhdsGT

set_option autoImplicit false

open Filter Topology NumberField IsDedekindDomain
open scoped ENNReal

namespace EulerResidueE6

variable {K : Type} [Field K] [NumberField K]

noncomputable def q (v : HeightOneSpectrum (𝓞 K)) : ℝ := ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)

theorem one_lt_absNorm (v : HeightOneSpectrum (𝓞 K)) : 1 < (Ideal.absNorm v.asIdeal : ℕ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem one_lt_q (v : HeightOneSpectrum (𝓞 K)) : 1 < q v := by
  unfold q; exact_mod_cast one_lt_absNorm v

theorem q_pos (v : HeightOneSpectrum (𝓞 K)) : 0 < q v := lt_trans zero_lt_one (one_lt_q v)

noncomputable def rf (v : HeightOneSpectrum (𝓞 K)) (s : ℝ) : ℝ :=
  (1 - q v ^ (-(2 * s)))⁻¹ * (1 - q v ^ (1 - 2 * s))⁻¹

noncomputable def gf (v : HeightOneSpectrum (𝓞 K)) (s : ℝ) : ℝ :=
  (1 - q v ^ (-(2 * s))) * (1 - q v ^ (1 - 2 * s))

theorem sub_rpow_pos (v : HeightOneSpectrum (𝓞 K)) {z : ℝ} (hz : z < 0) : 0 < 1 - q v ^ z :=
  sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg (one_lt_q v) hz)

theorem sub_rpow_nonneg (v : HeightOneSpectrum (𝓞 K)) {z : ℝ} (hz : z ≤ 0) : 0 ≤ 1 - q v ^ z :=
  sub_nonneg.2 (Real.rpow_le_one_of_one_le_of_nonpos (one_lt_q v).le hz)

theorem sub_rpow_le_one (v : HeightOneSpectrum (𝓞 K)) (z : ℝ) : 1 - q v ^ z ≤ 1 :=
  sub_le_self _ (Real.rpow_nonneg (q_pos v).le z)

theorem gf_nonneg (v : HeightOneSpectrum (𝓞 K)) {s : ℝ} (hs : 1 / 2 ≤ s) : 0 ≤ gf v s :=
  mul_nonneg (sub_rpow_nonneg v (by linarith)) (sub_rpow_nonneg v (by linarith))

theorem gf_pos (v : HeightOneSpectrum (𝓞 K)) {s : ℝ} (hs : 1 / 2 < s) : 0 < gf v s :=
  mul_pos (sub_rpow_pos v (by linarith)) (sub_rpow_pos v (by linarith))

theorem rf_eq_inv_gf (v : HeightOneSpectrum (𝓞 K)) (s : ℝ) : rf v s = (gf v s)⁻¹ := by
  unfold rf gf; rw [mul_inv]

theorem one_le_rf (v : HeightOneSpectrum (𝓞 K)) {s : ℝ} (hs : 1 / 2 < s) : 1 ≤ rf v s := by
  rw [rf_eq_inv_gf, one_le_inv_iff₀]
  refine ⟨gf_pos v hs, ?_⟩
  unfold gf
  calc (1 - q v ^ (-(2 * s))) * (1 - q v ^ (1 - 2 * s)) ≤ 1 * 1 :=
        mul_le_mul (sub_rpow_le_one v _) (sub_rpow_le_one v _) (sub_rpow_nonneg v (by linarith))
          zero_le_one
    _ = 1 := one_mul 1

theorem rf_pos (v : HeightOneSpectrum (𝓞 K)) {s : ℝ} (hs : 1 / 2 < s) : 0 < rf v s :=
  lt_of_lt_of_le zero_lt_one (one_le_rf v hs)

theorem ennreal_q_rpow (v : HeightOneSpectrum (𝓞 K)) (z : ℝ) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ z = ENNReal.ofReal (q v ^ z) := by
  rw [show ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) = ENNReal.ofReal (q v) by
    rw [q, ENNReal.ofReal_natCast]]
  exact ENNReal.ofReal_rpow_of_pos (q_pos v)

theorem ennreal_one_sub (v : HeightOneSpectrum (𝓞 K)) (z : ℝ) :
    (1 : ℝ≥0∞) - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ z = ENNReal.ofReal (1 - q v ^ z) := by
  rw [ennreal_q_rpow, ENNReal.ofReal_sub _ (Real.rpow_nonneg (q_pos v).le z), ENNReal.ofReal_one]

theorem ennreal_gf' (v : HeightOneSpectrum (𝓞 K)) (s : ℝ) (hs : 1 / 2 ≤ s) :
    ((1 : ℝ≥0∞) - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s))) *
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s)) = ENNReal.ofReal (gf v s) := by
  rw [ennreal_one_sub, ennreal_one_sub, gf, ENNReal.ofReal_mul (sub_rpow_nonneg v (by linarith))]

theorem ennreal_rf (v : HeightOneSpectrum (𝓞 K)) (s : ℝ) (hs : 1 / 2 < s) :
    ((1 : ℝ≥0∞) - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s)))⁻¹ *
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s))⁻¹ = ENNReal.ofReal (rf v s) := by
  rw [ennreal_one_sub, ennreal_one_sub, rf,
    ENNReal.ofReal_mul (inv_nonneg.2 (sub_rpow_nonneg v (by linarith))),
    ENNReal.ofReal_inv_of_pos (sub_rpow_pos v (by linarith)),
    ENNReal.ofReal_inv_of_pos (sub_rpow_pos v (by linarith))]

theorem complex_factor_eq (v : HeightOneSpectrum (𝓞 K)) (s : ℝ) :
    (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s : ℂ))))⁻¹ *
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s : ℂ) - 1)))⁻¹ = ((rf v s : ℝ) : ℂ) := by
  have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = ((q v : ℝ) : ℂ) := by simp [q]
  have h1 : (-(2 * (s : ℂ))) = (((-(2 * s) : ℝ)) : ℂ) := by push_cast; ring
  have h2 : (-(2 * (s : ℂ) - 1)) = (((1 - 2 * s : ℝ)) : ℂ) := by push_cast; ring
  rw [hq, h1, h2, ← Complex.ofReal_cpow (q_pos v).le, ← Complex.ofReal_cpow (q_pos v).le, rf]
  push_cast
  rfl

noncomputable def W (K : Type) [Field K] [NumberField K] (s : ℝ) : ℂ :=
  dedekindZeta K (2 * (s : ℂ)) * dedekindZeta K (2 * (s : ℂ) - 1)

theorem tendsto_prod_rf_complex {s : ℝ} (hs : 1 < s) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 K)) => (((∏ v ∈ T, rf v s : ℝ)) : ℂ)) atTop
      (𝓝 (W K s)) := by
  have h := ((NumberField.hasProd_and_tendsto_sub_one_mul_dedekindZeta_two_mul_mul_dedekindZeta_two_mul_sub_one_nhdsGT
    K).1 s hs)
  rw [HasProd] at h
  refine h.congr fun T => ?_
  rw [Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun v _ => complex_factor_eq v s

theorem W_im {s : ℝ} (hs : 1 < s) : (W K s).im = 0 := by
  have h := (Complex.continuous_im.tendsto _).comp (tendsto_prod_rf_complex (K := K) hs)
  have h0 : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 K)) =>
      ((((∏ v ∈ T, rf v s : ℝ)) : ℂ)).im) atTop (𝓝 0) := by
    simp only [Complex.ofReal_im]; exact tendsto_const_nhds
  exact tendsto_nhds_unique h h0

theorem W_eq_ofReal_re {s : ℝ} (hs : 1 < s) : W K s = (((W K s).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [W_im hs])

theorem tendsto_prod_rf {s : ℝ} (hs : 1 < s) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 K)) => ∏ v ∈ T, rf v s) atTop (𝓝 (W K s).re) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_prod_rf_complex (K := K) hs)
  refine h.congr fun T => ?_
  simp only [Function.comp_apply, Complex.ofReal_re]

theorem one_le_W_re {s : ℝ} (hs : 1 < s) : 1 ≤ (W K s).re := by
  refine ge_of_tendsto' (tendsto_prod_rf hs) fun T => ?_
  calc (1 : ℝ) = ∏ _v ∈ T, (1 : ℝ) := Finset.prod_const_one.symm
    _ ≤ ∏ v ∈ T, rf v s :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) fun v _ => one_le_rf v (by linarith)

theorem W_re_pos {s : ℝ} (hs : 1 < s) : 0 < (W K s).re := lt_of_lt_of_le zero_lt_one (one_le_W_re hs)

theorem prod_rf_ne_zero (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 / 2 < s) :
    ∏ v ∈ S, rf v s ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun v _ => (rf_pos v hs).ne'

theorem prod_rf_mul_prod_gf (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 / 2 < s) :
    (∏ v ∈ S, rf v s) * ∏ v ∈ S, gf v s = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [rf_eq_inv_gf, inv_mul_cancel₀ (gf_pos v hs).ne']

section SDiff

variable [DecidableEq (HeightOneSpectrum (𝓞 K))]

theorem tendsto_prod_sdiff_rf (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 K)) => ∏ v ∈ T \ S, rf v s) atTop
      (𝓝 ((W K s).re * ∏ v ∈ S, gf v s)) := by
  have hs' : 1 / 2 < s := by linarith
  have h1 : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 K)) => (∏ v ∈ T, rf v s) * ∏ v ∈ S, gf v s)
      atTop (𝓝 ((W K s).re * ∏ v ∈ S, gf v s)) := (tendsto_prod_rf hs).mul_const _
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop S] with T hT
  rw [← Finset.prod_sdiff hT, mul_assoc, prod_rf_mul_prod_gf S hs', mul_one]

end SDiff

theorem tendsto_sub_one_mul_W_re :
    Tendsto (fun s : ℝ => (s - 1) * (W K s).re) (𝓝[>] 1)
      (𝓝 ((dedekindZeta K 2).re * (dedekindZeta_residue K / 2))) := by
  have h := (NumberField.hasProd_and_tendsto_sub_one_mul_dedekindZeta_two_mul_mul_dedekindZeta_two_mul_sub_one_nhdsGT
    K).2
  have h' := (Complex.continuous_re.tendsto _).comp h
  have hlim : (dedekindZeta K 2 * (((dedekindZeta_residue K / 2 : ℝ)) : ℂ)).re =
      (dedekindZeta K 2).re * (dedekindZeta_residue K / 2) := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hlim] at h'
  refine h'.congr fun s => ?_
  simp only [Function.comp_apply]
  rw [Complex.mul_re, show ((s : ℂ) - 1).re = s - 1 by simp, show ((s : ℂ) - 1).im = 0 by simp,
    zero_mul, sub_zero]
  rfl

theorem continuousAt_gf (v : HeightOneSpectrum (𝓞 K)) (s₀ : ℝ) : ContinuousAt (fun s => gf v s) s₀ := by
  unfold gf
  have hq : q v ≠ 0 := (q_pos v).ne'
  have h1 : ContinuousAt (fun s : ℝ => q v ^ (-(2 * s))) s₀ :=
    (Real.continuousAt_const_rpow hq).comp (by fun_prop)
  have h2 : ContinuousAt (fun s : ℝ => q v ^ (1 - 2 * s)) s₀ :=
    (Real.continuousAt_const_rpow hq).comp (by fun_prop)
  exact (continuousAt_const.sub h1).mul (continuousAt_const.sub h2)

theorem continuousAt_prod_gf (S : Finset (HeightOneSpectrum (𝓞 K))) (s₀ : ℝ) :
    ContinuousAt (fun s => ∏ v ∈ S, gf v s) s₀ :=
  tendsto_finsetProd S fun v _ => continuousAt_gf v s₀

theorem gf_one (v : HeightOneSpectrum (𝓞 K)) :
    gf v 1 = (1 - q v ^ (-(2 : ℝ))) * (1 - q v ^ (-(1 : ℝ))) := by
  unfold gf; norm_num

theorem tendsto_sub_one_mul_W_re_mul_prod_gf (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Tendsto (fun s : ℝ => (s - 1) * (W K s).re * ∏ v ∈ S, gf v s) (𝓝[>] 1)
      (𝓝 ((dedekindZeta K 2).re * (dedekindZeta_residue K / 2) * ∏ v ∈ S, gf v 1)) :=
  tendsto_sub_one_mul_W_re.mul
    ((continuousAt_prod_gf S 1).tendsto.mono_left nhdsWithin_le_nhds)

theorem ennreal_prod_gf (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 / 2 ≤ s) :
    ∏ v ∈ S, ((1 : ℝ≥0∞) - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s))) *
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s)) = ENNReal.ofReal (∏ v ∈ S, gf v s) := by
  rw [ENNReal.ofReal_prod_of_nonneg fun v _ => gf_nonneg v hs]
  exact Finset.prod_congr rfl fun v _ => ennreal_gf' v s hs

theorem ennreal_prod_rf (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 / 2 < s) :
    ∏ v ∈ S, (((1 : ℝ≥0∞) - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s)))⁻¹ *
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s))⁻¹) = ENNReal.ofReal (∏ v ∈ S, rf v s) := by
  rw [ENNReal.ofReal_prod_of_nonneg fun v _ => (rf_pos v hs).le]
  exact Finset.prod_congr rfl fun v _ => ennreal_rf v s hs

theorem ennreal_prod_gf_one (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∏ v ∈ S, ((1 : ℝ≥0∞) - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 : ℝ))) *
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(1 : ℝ))) = ENNReal.ofReal (∏ v ∈ S, gf v 1) := by
  rw [ENNReal.ofReal_prod_of_nonneg fun v _ => gf_nonneg v (by norm_num : (1:ℝ) / 2 ≤ 1)]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [gf_one, ennreal_one_sub, ennreal_one_sub,
    ENNReal.ofReal_mul (sub_rpow_nonneg v (by norm_num : (-(2:ℝ)) ≤ 0))]

theorem partA [DecidableEq (HeightOneSpectrum (𝓞 K))] (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 K)) =>
        ∏ v ∈ T \ S, (((1 : ℝ≥0∞) - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s)))⁻¹ *
          (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s))⁻¹))
      atTop
      (𝓝 (ENNReal.ofReal (W K s).re *
        ∏ v ∈ S, ((1 : ℝ≥0∞) - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s))) *
          (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s)))) := by
  have hs' : 1 / 2 < s := by linarith
  have h := ENNReal.tendsto_ofReal (tendsto_prod_sdiff_rf S hs)
  rw [ENNReal.ofReal_mul (W_re_pos hs).le] at h
  rw [ennreal_prod_gf S hs'.le]
  refine h.congr fun T => ?_
  exact (ennreal_prod_rf (T \ S) hs').symm

theorem partB (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Tendsto (fun s : ℝ => ENNReal.ofReal (s - 1) *
        (ENNReal.ofReal (W K s).re *
          ∏ v ∈ S, ((1 : ℝ≥0∞) - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s))) *
            (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s))))
      (𝓝[>] (1 : ℝ))
      (𝓝 (ENNReal.ofReal ((dedekindZeta K 2).re * (dedekindZeta_residue K / 2)) *
          ∏ v ∈ S, ((1 : ℝ≥0∞) - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 : ℝ))) *
            (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(1 : ℝ))))) := by
  have h := ENNReal.tendsto_ofReal (tendsto_sub_one_mul_W_re_mul_prod_gf (K := K) S)
  have hg1 : 0 ≤ ∏ v ∈ S, gf v 1 := Finset.prod_nonneg fun v _ => gf_nonneg v (by norm_num)
  rw [ENNReal.ofReal_mul' hg1, ← ennreal_prod_gf_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : 1 < s := hs
  have hs' : 1 / 2 < s := by linarith
  rw [ENNReal.ofReal_mul' (Finset.prod_nonneg fun v _ => gf_nonneg v hs'.le),
    ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ s - 1), ennreal_prod_gf S hs'.le, mul_assoc]

end EulerResidueE6

open EulerResidueE6 in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (∀ s : ℝ, 1 < s →
      0 < (NumberField.dedekindZeta K (2 * (s : ℂ)) * NumberField.dedekindZeta K (2 * (s : ℂ) - 1)).re) ∧
    (∀ s : ℝ, 1 < s →
      Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 K)) =>
          ∏ v ∈ T \ S, ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s)))⁻¹ *
            (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s))⁻¹))
        atTop
        (𝓝 (ENNReal.ofReal
              ((NumberField.dedekindZeta K (2 * (s : ℂ)) * NumberField.dedekindZeta K (2 * (s : ℂ) - 1)).re) *
          ∏ v ∈ S, ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s))) *
            (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s)))))) ∧
    Tendsto (fun s : ℝ => ENNReal.ofReal (s - 1) *
        (ENNReal.ofReal
            ((NumberField.dedekindZeta K (2 * (s : ℂ)) * NumberField.dedekindZeta K (2 * (s : ℂ) - 1)).re) *
          ∏ v ∈ S, ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s))) *
            (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s)))))
      (𝓝[>] (1 : ℝ))
      (𝓝 (ENNReal.ofReal ((NumberField.dedekindZeta K 2).re * (NumberField.dedekindZeta_residue K / 2)) *
          ∏ v ∈ S, ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 : ℝ))) *
            (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(1 : ℝ)))))) :=
  ⟨fun _ hs => W_re_pos hs, fun _ hs => partA S hs, partB S⟩

end S_NumberField_tendsto_prod_sdiff_inv_one_sub_absNorm_rpow_atTop_and_tendsto_sub_one_mul_re_dedekindZeta_two_mul_nhdsGT
end P2MW
export P2MW.S_NumberField_tendsto_prod_sdiff_inv_one_sub_absNorm_rpow_atTop_and_tendsto_sub_one_mul_re_dedekindZeta_two_mul_nhdsGT (solution)
