-- Prove2me | solution 1 for LinParamBandits.LowerBound.risk_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T22:36:56.362719+00:00
-- url     : https://prove2.me/submissions/af88b623-9295-4e2a-a05b-7dbaa978bc18

import Mathlib
import Definitions.Def_LinParamBandits_LowerBound_Model

open MeasureTheory ProbabilityTheory

namespace LPB22Aux
open LinParamBandits.LowerBound

lemma measurable_snoc_pair {r t : ℕ} {X : Type*} [MeasurableSpace X] {f : X → History r t}
    {a : X → Vec r × ℝ} (hf : Measurable f) (ha : Measurable a) :
    Measurable (fun x => (Fin.snoc (α := fun _ => Vec r × ℝ) (f x) (a x) : History r (t + 1))) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using ha
  · simpa using (show Measurable (fun x => f x j) from (measurable_pi_apply j).comp hf)

lemma hist_measurable {r : ℕ} (ψ : SpherePolicy r) (t : ℕ) :
    Measurable (fun ω : Ω r => hist ψ ω.1 ω.2 t) := by
  induction t with
  | zero => simp only [hist]; exact measurable_const
  | succ t ih =>
    simp only [hist]
    have h1 : Measurable (fun ω : Ω r => ψ.act t (hist ψ ω.1 ω.2 t)) :=
      (ψ.measurable_act t).comp ih
    refine measurable_snoc_pair ih (h1.prodMk ?_)
    exact (h1.inner measurable_fst).add ((measurable_pi_apply t).comp measurable_snd)

lemma arm_measurable {r : ℕ} (ψ : SpherePolicy r) (t : ℕ) :
    Measurable (fun ω : Ω r => arm ψ ω.1 ω.2 t) :=
  (ψ.measurable_act t).comp (hist_measurable ψ t)

lemma arm_eq_hist {r : ℕ} (ψ : SpherePolicy r) (z : Vec r) (η : ℕ → ℝ) :
    ∀ (T t : ℕ) (h : t < T), arm ψ z η t = (hist ψ z η T ⟨t, h⟩).1
  | 0, t, h => absurd h (Nat.not_lt_zero _)
  | T + 1, t, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · rw [arm_eq_hist ψ z η T t h']
      simp only [hist]
      rw [show (⟨t, h⟩ : Fin (T + 1)) = Fin.castSucc ⟨t, h'⟩ from rfl, Fin.snoc_castSucc]
    · subst h'
      simp only [hist]
      rw [show (⟨t, h⟩ : Fin (t + 1)) = Fin.last t from rfl, Fin.snoc_last]
      rfl

/-- Pointwise inequality behind Lemma 2.2. -/
lemma pointwise_bound {r : ℕ} (S' : Fin (r - 1) → Vec r) (hS : Orthonormal ℝ S') (z : Vec r)
    (U : ℕ → Vec r) (hU : ∀ t, ‖U t‖ = 1) (T : ℕ) :
    ∑ k, (‖z‖ * ∑ t ∈ Finset.range T, (inner ℝ (U t) (S' k)) ^ 2
        + (T : ℝ) / ‖z‖ * (inner ℝ z (S' k)) ^ 2
        - 2 * ((∑ t ∈ Finset.range T, inner ℝ (U t) (S' k)) * inner ℝ z (S' k)))
      ≤ 2 * ∑ t ∈ Finset.range T, (‖z‖ - inner ℝ (U t) z) := by
  by_cases hz : z = 0
  · subst hz; simp
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  -- per period
  have hper : ∀ t, ∑ k, (‖z‖ * (inner ℝ (U t) (S' k)) ^ 2 + (inner ℝ z (S' k)) ^ 2 / ‖z‖
      - 2 * (inner ℝ (U t) (S' k) * inner ℝ z (S' k))) ≤ 2 * (‖z‖ - inner ℝ (U t) z) := by
    intro t
    set x := U t - ‖z‖⁻¹ • z with hx
    have hb := hS.sum_inner_products_le (x := x) (s := Finset.univ)
    have hxn : ‖x‖ ^ 2 = 2 - 2 * (inner ℝ (U t) z / ‖z‖) := by
      rw [hx, @norm_sub_sq_real, hU t, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne',
        inner_smul_right]
      ring
    have hterm : ∀ k, ‖z‖ * ‖inner ℝ (S' k) x‖ ^ 2 =
        ‖z‖ * (inner ℝ (U t) (S' k)) ^ 2 + (inner ℝ z (S' k)) ^ 2 / ‖z‖
          - 2 * (inner ℝ (U t) (S' k) * inner ℝ z (S' k)) := by
      intro k
      rw [Real.norm_eq_abs, sq_abs, hx, inner_sub_right, inner_smul_right,
        real_inner_comm (U t), real_inner_comm z]
      field_simp
      ring
    have := mul_le_mul_of_nonneg_left hb hn.le
    rw [Finset.mul_sum] at this
    simp_rw [hterm] at this
    rw [hxn] at this
    calc _ ≤ ‖z‖ * (2 - 2 * (inner ℝ (U t) z / ‖z‖)) := this
      _ = 2 * (‖z‖ - inner ℝ (U t) z) := by field_simp
  calc _ = ∑ t ∈ Finset.range T, ∑ k, (‖z‖ * (inner ℝ (U t) (S' k)) ^ 2
        + (inner ℝ z (S' k)) ^ 2 / ‖z‖
        - 2 * (inner ℝ (U t) (S' k) * inner ℝ z (S' k))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_mul]
        ring
    _ ≤ ∑ t ∈ Finset.range T, 2 * (‖z‖ - inner ℝ (U t) z) := Finset.sum_le_sum (fun t _ => hper t)
    _ = _ := by rw [Finset.mul_sum]

section defs
variable {r : ℕ} (ψ : SpherePolicy r) {T : ℕ} (S : Fin (r - 1) → History r T → Vec r)

noncomputable def Xp (k : Fin (r - 1)) (ω : Ω r) : ℝ :=
  ‖ω.1‖ * ∑ t ∈ Finset.range T, (inner ℝ (arm ψ ω.1 ω.2 t) (S k (hist ψ ω.1 ω.2 T))) ^ 2
    + (T : ℝ) / ‖ω.1‖ * (inner ℝ ω.1 (S k (hist ψ ω.1 ω.2 T))) ^ 2

noncomputable def Cf (k : Fin (r - 1)) (ω : Ω r) : ℝ :=
  (∑ t ∈ Finset.range T, inner ℝ (arm ψ ω.1 ω.2 t) (S k (hist ψ ω.1 ω.2 T)))
    * inner ℝ ω.1 (S k (hist ψ ω.1 ω.2 T))

noncomputable def Gf (T : ℕ) (ω : Ω r) : ℝ :=
  ∑ t ∈ Finset.range T, (‖ω.1‖ - inner ℝ (arm ψ ω.1 ω.2 t) ω.1)

/-- The history-measurable vector `(∑_t U_t′S) S`. -/
noncomputable def Wv (k : Fin (r - 1)) (h : History r T) : Vec r :=
  (∑ i : Fin T, inner ℝ (h i).1 (S k h)) • S k h

end defs

end LPB22Aux

open LinParamBandits.LowerBound LPB22Aux in
theorem solution (r : ℕ) (hr : 2 ≤ r) (ψ : SpherePolicy r) (T : ℕ) (hT : 1 ≤ T)
    (S : Fin (r - 1) → History r T → Vec r)
    (hS_meas : ∀ k, Measurable (S k))
    (hS_orth : ∀ h, Orthonormal ℝ (fun k => S k h))
    (hS_perp : ∀ᵐ ω ∂(P r), ∀ k, inner ℝ (S k (hist ψ ω.1 ω.2 T)) (zhat ψ T ω) = 0) :
    2⁻¹ * ∑ k, ∫⁻ ω, ENNReal.ofReal
        (‖ω.1‖ * ∑ t ∈ Finset.range T, (inner ℝ (arm ψ ω.1 ω.2 t) (S k (hist ψ ω.1 ω.2 T))) ^ 2
          + (T : ℝ) / ‖ω.1‖ * (inner ℝ (ω.1 - zhat ψ T ω) (S k (hist ψ ω.1 ω.2 T))) ^ 2) ∂(P r)
      ≤ risk ψ T := by
  classical
  haveI : IsProbabilityMeasure (prior r) := by
    unfold prior; exact Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure noise := by unfold noise; infer_instance
  haveI : IsProbabilityMeasure (P r) := by unfold P; infer_instance
  have hH := hist_measurable ψ T
  have hm : histSigma ψ T ≤ (inferInstance : MeasurableSpace (Ω r)) := hH.comap_le
  have hU_meas : ∀ t, Measurable (fun ω : Ω r => arm ψ ω.1 ω.2 t) := arm_measurable ψ
  have hSk_meas : ∀ k, Measurable (fun ω : Ω r => S k (hist ψ ω.1 ω.2 T)) :=
    fun k => (hS_meas k).comp hH
  have hSn : ∀ k h, ‖S k h‖ = 1 := fun k h => (hS_orth h).1 k
  have hUn : ∀ t (ω : Ω r), ‖arm ψ ω.1 ω.2 t‖ = 1 := fun t ω => ψ.norm_act _ _
  have hUS : ∀ t k (ω : Ω r), |inner ℝ (arm ψ ω.1 ω.2 t) (S k (hist ψ ω.1 ω.2 T))| ≤ 1 := by
    intro t k ω
    have := abs_real_inner_le_norm (arm ψ ω.1 ω.2 t) (S k (hist ψ ω.1 ω.2 T))
    rwa [hUn, hSn, one_mul] at this
  have hZS : ∀ k (ω : Ω r), |inner ℝ ω.1 (S k (hist ψ ω.1 ω.2 T))| ≤ ‖ω.1‖ := by
    intro k ω
    have := abs_real_inner_le_norm ω.1 (S k (hist ψ ω.1 ω.2 T))
    rwa [hSn, mul_one] at this
  -- integrability of `Z`
  have hprior_int : Integrable (fun z : Vec r => z) (prior r) := by
    unfold prior
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    have h : Integrable (fun x : Vec r => x) (stdGaussian (Vec r)) := IsGaussian.integrable_id
    exact h.smul ((Real.sqrt r)⁻¹)
  have hZ : Integrable (fun ω : Ω r => ω.1) (P r) := hprior_int.comp_fst noise
  have hZn : Integrable (fun ω : Ω r => ‖ω.1‖) (P r) := hZ.norm
  have hTZ : Integrable (fun ω : Ω r => (2 * T : ℝ) * ‖ω.1‖) (P r) := hZn.const_mul _
  -- measurability
  have hXp_meas : ∀ k, Measurable (Xp ψ S k) := by
    intro k; unfold Xp
    have h1 := hSk_meas k
    refine (measurable_fst.norm.mul (Finset.measurable_sum _ (fun t _ =>
      ((hU_meas t).inner h1).pow_const 2))).add ?_
    exact (measurable_const.div measurable_fst.norm).mul ((measurable_fst.inner h1).pow_const 2)
  have hC_meas : ∀ k, Measurable (Cf ψ S k) := by
    intro k; unfold Cf
    have h1 := hSk_meas k
    exact (Finset.measurable_sum _ (fun t _ => (hU_meas t).inner h1)).mul
      (measurable_fst.inner h1)
  have hG_meas : Measurable (Gf ψ T) := by
    unfold Gf
    exact Finset.measurable_sum _ (fun t _ => measurable_fst.norm.sub
      ((hU_meas t).inner measurable_fst))
  -- bounds
  have hsumsq : ∀ k (ω : Ω r),
      ∑ t ∈ Finset.range T, (inner ℝ (arm ψ ω.1 ω.2 t) (S k (hist ψ ω.1 ω.2 T))) ^ 2 ≤ T := by
    intro k ω
    calc _ ≤ ∑ t ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum (fun t _ => by
            have := hUS t k ω
            have h0 := abs_nonneg (inner ℝ (arm ψ ω.1 ω.2 t) (S k (hist ψ ω.1 ω.2 T)))
            rw [← sq_abs]; nlinarith)
      _ = T := by simp
  have hsumabs : ∀ k (ω : Ω r),
      |∑ t ∈ Finset.range T, inner ℝ (arm ψ ω.1 ω.2 t) (S k (hist ψ ω.1 ω.2 T))| ≤ T := by
    intro k ω
    calc _ ≤ ∑ t ∈ Finset.range T, |inner ℝ (arm ψ ω.1 ω.2 t) (S k (hist ψ ω.1 ω.2 T))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum (fun t _ => hUS t k ω)
      _ = T := by simp
  have hsecond : ∀ k (ω : Ω r), (T : ℝ) / ‖ω.1‖ * (inner ℝ ω.1 (S k (hist ψ ω.1 ω.2 T))) ^ 2
      ≤ T * ‖ω.1‖ := by
    intro k ω
    rcases eq_or_lt_of_le (norm_nonneg ω.1) with h0 | h0
    · rw [← h0]; simp
    · have hsq : (inner ℝ ω.1 (S k (hist ψ ω.1 ω.2 T))) ^ 2 ≤ ‖ω.1‖ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hZS k ω) 2
      calc _ ≤ (T : ℝ) / ‖ω.1‖ * ‖ω.1‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = T * ‖ω.1‖ := by field_simp
  have hXp_nonneg : ∀ k ω, 0 ≤ Xp ψ S k ω := by
    intro k ω; unfold Xp
    have : 0 ≤ (T : ℝ) / ‖ω.1‖ := by positivity
    positivity
  have hXp_int : ∀ k, Integrable (Xp ψ S k) (P r) := by
    intro k
    refine Integrable.mono' hTZ (hXp_meas k).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hXp_nonneg k ω)]
    unfold Xp
    have h1 := mul_le_mul_of_nonneg_left (hsumsq k ω) (norm_nonneg ω.1)
    have h2 := hsecond k ω
    nlinarith [norm_nonneg ω.1]
  have hC_int : ∀ k, Integrable (Cf ψ S k) (P r) := by
    intro k
    refine Integrable.mono' hTZ (hC_meas k).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs]
    unfold Cf
    rw [abs_mul]
    have h1 := hsumabs k ω
    have h2 := hZS k ω
    have h3 := abs_nonneg (inner ℝ ω.1 (S k (hist ψ ω.1 ω.2 T)))
    have h4 := abs_nonneg (∑ t ∈ Finset.range T, inner ℝ (arm ψ ω.1 ω.2 t) (S k (hist ψ ω.1 ω.2 T)))
    nlinarith [norm_nonneg ω.1, mul_le_mul h1 h2 h3 (Nat.cast_nonneg T)]
  have hG_nonneg : ∀ ω, 0 ≤ Gf ψ T ω := by
    intro ω; unfold Gf
    refine Finset.sum_nonneg (fun t _ => ?_)
    have := real_inner_le_norm (arm ψ ω.1 ω.2 t) ω.1
    rw [hUn, one_mul] at this
    linarith
  have hG_int : Integrable (Gf ψ T) (P r) := by
    refine Integrable.mono' hTZ hG_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hG_nonneg ω)]
    unfold Gf
    calc _ ≤ ∑ t ∈ Finset.range T, (2 * ‖ω.1‖) := Finset.sum_le_sum (fun t _ => by
            have := neg_abs_le (inner ℝ (arm ψ ω.1 ω.2 t) ω.1)
            have h2 := abs_real_inner_le_norm (arm ψ ω.1 ω.2 t) ω.1
            rw [hUn, one_mul] at h2
            linarith)
      _ = (2 * T : ℝ) * ‖ω.1‖ := by simp; ring
  -- the cross term vanishes
  have hC_zero : ∀ k, ∫ ω, Cf ψ S k ω ∂(P r) = 0 := by
    intro k
    have hWm : StronglyMeasurable[histSigma ψ T] (fun ω : Ω r => Wv S k (hist ψ ω.1 ω.2 T)) := by
      have hW : Measurable (Wv S k) := by
        unfold Wv
        have h1 : Measurable (fun h : History r T => ∑ i : Fin T, inner ℝ (h i).1 (S k h)) :=
          Finset.measurable_sum _ (fun i _ =>
            ((measurable_fst.comp (measurable_pi_apply i)).inner (hS_meas k)))
        have h2 := hS_meas k
        fun_prop
      exact (hW.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
    have hCW : ∀ ω : Ω r, Cf ψ S k ω = innerSL ℝ ω.1 (Wv S k (hist ψ ω.1 ω.2 T)) := by
      intro ω
      unfold Cf Wv
      rw [innerSL_apply_apply, inner_smul_right, Finset.sum_range]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [arm_eq_hist ψ ω.1 ω.2 T i i.2]
    have hint : Integrable (fun ω : Ω r => innerSL ℝ ω.1 (Wv S k (hist ψ ω.1 ω.2 T))) (P r) := by
      have := hC_int k
      exact this.congr (Filter.Eventually.of_forall hCW)
    have hpull := condExp_bilin_of_stronglyMeasurable_right (innerSL ℝ) hWm hint hZ
    calc ∫ ω, Cf ψ S k ω ∂(P r)
        = ∫ ω, innerSL ℝ ω.1 (Wv S k (hist ψ ω.1 ω.2 T)) ∂(P r) :=
          integral_congr_ae (Filter.Eventually.of_forall hCW)
      _ = ∫ ω, ((P r)[fun ω : Ω r => innerSL ℝ ω.1 (Wv S k (hist ψ ω.1 ω.2 T)) | histSigma ψ T]) ω
          ∂(P r) := (integral_condExp hm).symm
      _ = ∫ ω, innerSL ℝ (zhat ψ T ω) (Wv S k (hist ψ ω.1 ω.2 T)) ∂(P r) := integral_congr_ae hpull
      _ = ∫ _ω, (0 : ℝ) ∂(P r) := by
          refine integral_congr_ae ?_
          filter_upwards [hS_perp] with ω hω
          unfold Wv
          rw [innerSL_apply_apply, inner_smul_right, real_inner_comm, hω k, mul_zero]
      _ = 0 := integral_zero _ _
  -- the risk as a single expectation
  have hrisk : risk ψ T = ENNReal.ofReal (∫ ω, Gf ψ T ω ∂(P r)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hG_int (Filter.Eventually.of_forall hG_nonneg)]
    unfold risk regret P
    rw [lintegral_prod _ (hG_meas.ennreal_ofReal.aemeasurable)]
    rfl
  -- each directional term
  have hdir : ∀ k, ∫⁻ ω, ENNReal.ofReal
        (‖ω.1‖ * ∑ t ∈ Finset.range T, (inner ℝ (arm ψ ω.1 ω.2 t) (S k (hist ψ ω.1 ω.2 T))) ^ 2
          + (T : ℝ) / ‖ω.1‖ * (inner ℝ (ω.1 - zhat ψ T ω) (S k (hist ψ ω.1 ω.2 T))) ^ 2) ∂(P r)
        = ENNReal.ofReal (∫ ω, (Xp ψ S k ω - 2 * Cf ψ S k ω) ∂(P r)) := by
    intro k
    rw [integral_sub (hXp_int k) ((hC_int k).const_mul 2), integral_const_mul, hC_zero k,
      mul_zero, sub_zero,
      ofReal_integral_eq_lintegral_ofReal (hXp_int k) (Filter.Eventually.of_forall (hXp_nonneg k))]
    refine lintegral_congr_ae ?_
    filter_upwards [hS_perp] with ω hω
    unfold Xp
    rw [inner_sub_left, real_inner_comm (S k (hist ψ ω.1 ω.2 T)) (zhat ψ T ω), hω k, sub_zero]
  simp_rw [hdir]
  have hnn : ∀ k, 0 ≤ ∫ ω, (Xp ψ S k ω - 2 * Cf ψ S k ω) ∂(P r) := by
    intro k
    rw [integral_sub (hXp_int k) ((hC_int k).const_mul 2), integral_const_mul, hC_zero k,
      mul_zero, sub_zero]
    exact integral_nonneg (hXp_nonneg k)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hnn k), hrisk,
    ← integral_finset_sum Finset.univ (f := fun k ω => Xp ψ S k ω - 2 * Cf ψ S k ω)
      (fun k _ => (hXp_int k).sub ((hC_int k).const_mul 2))]
  have hpt : ∀ ω, ∑ k, (Xp ψ S k ω - 2 * Cf ψ S k ω) ≤ 2 * Gf ψ T ω := by
    intro ω
    have := pointwise_bound (fun k => S k (hist ψ ω.1 ω.2 T)) (hS_orth _) ω.1
      (fun t => arm ψ ω.1 ω.2 t) (fun t => hUn t ω) T
    unfold Xp Cf Gf
    exact this
  have hmono : ∫ ω, ∑ k, (Xp ψ S k ω - 2 * Cf ψ S k ω) ∂(P r) ≤ ∫ ω, 2 * Gf ψ T ω ∂(P r) :=
    integral_mono (integrable_finset_sum _ (fun k _ => (hXp_int k).sub ((hC_int k).const_mul 2)))
      (hG_int.const_mul 2) hpt
  rw [integral_const_mul] at hmono
  have hG0 : 0 ≤ ∫ ω, Gf ψ T ω ∂(P r) := integral_nonneg hG_nonneg
  calc 2⁻¹ * ENNReal.ofReal (∫ ω, ∑ k, (Xp ψ S k ω - 2 * Cf ψ S k ω) ∂(P r))
      ≤ 2⁻¹ * ENNReal.ofReal (2 * ∫ ω, Gf ψ T ω ∂(P r)) := by
        gcongr
    _ = ENNReal.ofReal (∫ ω, Gf ψ T ω ∂(P r)) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ← mul_assoc,
          ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
