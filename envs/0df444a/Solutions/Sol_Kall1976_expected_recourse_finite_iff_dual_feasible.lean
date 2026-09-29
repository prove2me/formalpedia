-- Prove2me | solution 1 for Kall1976.expected_recourse_finite_iff_dual_feasible
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:49:37.907493+00:00
-- url     : https://prove2.me/submissions/4554adf9-0733-4a41-978f-4e6ab4fb8054

import Definitions.Def_Kall1976_RecourseDifferentiability
import Definitions.Def_KallMayer_Recourse_CompleteRecourse

open MeasureTheory

namespace Kall1976

open Matrix Filter Topology

theorem aux_kr_abs_dot_le {p : ℕ} (w y : Fin p → ℝ) :
    |w ⬝ᵥ y| ≤ ‖w‖ * ∑ j, |y j| := by
  unfold dotProduct
  calc |∑ j, w j * y j| ≤ ∑ j, |w j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ‖w‖ * |y j| := by
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm w j) (abs_nonneg _)
    _ = ‖w‖ * ∑ j, |y j| := by rw [Finset.mul_sum]

theorem aux_kr_weak {m p : ℕ} (W : Matrix (Fin m) (Fin p) ℝ) (q : Fin p → ℝ)
    (z : Fin m → ℝ) (hz : ∀ j, (Wᵀ *ᵥ z) j ≤ q j) (y : Fin p → ℝ) (hy : ∀ j, 0 ≤ y j) :
    z ⬝ᵥ (W *ᵥ y) ≤ q ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose]
  unfold dotProduct
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hz j) (hy j)

theorem aux_kr_dual_bound {m p : ℕ} (W : Matrix (Fin m) (Fin p) ℝ)
    (yP yM : Fin m → Fin p → ℝ)
    (hyP0 : ∀ i j, 0 ≤ yP i j) (hyP : ∀ i, W *ᵥ yP i = Pi.single i 1)
    (hyM0 : ∀ i j, 0 ≤ yM i j) (hyM : ∀ i, W *ᵥ yM i = -Pi.single i 1)
    (q : Fin p → ℝ) (z : Fin m → ℝ) (hz : ∀ j, (Wᵀ *ᵥ z) j ≤ q j) :
    ‖z‖ ≤ ‖q‖ * ∑ i, (∑ j, |yP i j| + ∑ j, |yM i j|) := by
  have hK : ∀ i, ∑ j, |yP i j| + ∑ j, |yM i j| ≤ ∑ i, (∑ j, |yP i j| + ∑ j, |yM i j|) :=
    fun i => Finset.single_le_sum (f := fun i => ∑ j, |yP i j| + ∑ j, |yM i j|)
      (fun i _ => by positivity) (Finset.mem_univ i)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_le]
  have h1 : z i ≤ q ⬝ᵥ yP i := by
    have := aux_kr_weak W q z hz (yP i) (hyP0 i)
    rwa [hyP, dotProduct_single, mul_one] at this
  have h2 : -z i ≤ q ⬝ᵥ yM i := by
    have := aux_kr_weak W q z hz (yM i) (hyM0 i)
    rwa [hyM, dotProduct_neg, dotProduct_single, mul_one] at this
  have h3 := aux_kr_abs_dot_le q (yP i)
  have h4 := aux_kr_abs_dot_le q (yM i)
  have h5 := hK i
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg _
  have h6 : ‖q‖ * (∑ j, |yP i j| + ∑ j, |yM i j|) ≤
      ‖q‖ * ∑ i, (∑ j, |yP i j| + ∑ j, |yM i j|) := mul_le_mul_of_nonneg_left h5 hq0
  have h7 : 0 ≤ ∑ j, |yP i j| := by positivity
  have h8 : 0 ≤ ∑ j, |yM i j| := by positivity
  constructor
  · nlinarith [abs_le.1 h4, abs_le.1 h3]
  · nlinarith [abs_le.1 h4, abs_le.1 h3]

theorem aux_kr_closed {m p : ℕ} (W : Matrix (Fin m) (Fin p) ℝ) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ (q : Fin p → ℝ) (z : Fin m → ℝ), (∀ j, (Wᵀ *ᵥ z) j ≤ q j) → ‖z‖ ≤ ‖q‖ * K) :
    IsClosed {q : Fin p → ℝ | ∃ z : Fin m → ℝ, ∀ j, (Wᵀ *ᵥ z) j ≤ q j} := by
  refine IsSeqClosed.isClosed ?_
  intro qs q hqs hlim
  choose zs hzs using hqs
  obtain ⟨C, hC⟩ : ∃ C, ∀ n, ‖qs n‖ ≤ C := by
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto qs hlim).exists_norm_le
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  have hb : Bornology.IsBounded (Metric.closedBall (0 : Fin m → ℝ) (C * K)) :=
    Metric.isBounded_closedBall
  have hmem : ∀ n, zs n ∈ Metric.closedBall (0 : Fin m → ℝ) (C * K) := by
    intro n
    rw [mem_closedBall_zero_iff]
    exact (hK _ _ (hzs n)).trans (mul_le_mul_of_nonneg_right (hC n) hK0)
  obtain ⟨z, -, φ, hφ, hz⟩ := tendsto_subseq_of_bounded hb hmem
  refine ⟨z, fun j => ?_⟩
  have hc : Continuous fun v : Fin m → ℝ => (Wᵀ *ᵥ v) j :=
    (continuous_apply j).comp (continuous_const.matrix_mulVec continuous_id)
  have h1 : Tendsto (fun n => (Wᵀ *ᵥ zs (φ n)) j) atTop (𝓝 ((Wᵀ *ᵥ z) j)) :=
    (hc.tendsto z).comp hz
  have h2 : Tendsto (fun n => qs (φ n) j) atTop (𝓝 (q j)) :=
    ((continuous_apply j).tendsto q).comp (hlim.comp hφ.tendsto_atTop)
  exact le_of_tendsto_of_tendsto' h1 h2 (fun n => hzs (φ n) j)

theorem aux_kr_nonneg_of (u c : ℝ) (hu : u < 0) (h : ∀ t : ℝ, 0 ≤ t → u < t * c) : 0 ≤ c := by
  by_contra hc
  replace hc := not_le.1 hc
  have := h (u / c) (div_nonneg_of_nonpos hu.le hc.le)
  rw [div_mul_cancel₀ _ hc.ne] at this
  exact lt_irrefl _ this

theorem aux_kr_farkas {m p : ℕ} (W : Matrix (Fin m) (Fin p) ℝ)
    (hS : IsClosed {q : Fin p → ℝ | ∃ z : Fin m → ℝ, ∀ j, (Wᵀ *ᵥ z) j ≤ q j})
    (q : Fin p → ℝ) (hq : ¬ ∃ z : Fin m → ℝ, ∀ j, (Wᵀ *ᵥ z) j ≤ q j) :
    ∃ y : Fin p → ℝ, (∀ j, 0 ≤ y j) ∧ W *ᵥ y = 0 ∧ q ⬝ᵥ y < 0 := by
  classical
  have hconv : Convex ℝ {q : Fin p → ℝ | ∃ z : Fin m → ℝ, ∀ j, (Wᵀ *ᵥ z) j ≤ q j} := by
    rintro a ⟨za, ha⟩ b ⟨zb, hb⟩ s t hs ht _
    refine ⟨s • za + t • zb, fun j => ?_⟩
    simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left (ha j) hs, mul_le_mul_of_nonneg_left (hb j) ht]
  obtain ⟨f, u, hfu, hS'⟩ := geometric_hahn_banach_point_closed hconv hS hq
  set y : Fin p → ℝ := fun j => f (fun k => if j = k then 1 else 0) with hy
  have hf : ∀ w, f w = w ⬝ᵥ y := by
    intro w
    have := (f : (Fin p → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_univ w
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this]
    rfl
  have hmem : ∀ w : Fin p → ℝ, (∃ z : Fin m → ℝ, ∀ j, (Wᵀ *ᵥ z) j ≤ w j) → u < f w :=
    fun w hw => hS' w hw
  have hu : u < 0 := by
    have := hmem 0 ⟨0, by simp⟩
    simpa using this
  refine ⟨y, fun j => ?_, ?_, ?_⟩
  · apply aux_kr_nonneg_of u (y j) hu
    intro t ht
    have := hmem (t • fun k => if j = k then 1 else 0) ⟨0, fun k => ?_⟩
    · rw [map_smul, smul_eq_mul] at this
      exact this
    · simp only [mulVec_zero, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp [ht]
  · ext i
    have key : ∀ t : ℝ, u < t * (W *ᵥ y) i := by
      intro t
      have := hmem (Wᵀ *ᵥ (t • Pi.single i 1)) ⟨t • Pi.single i 1, fun _ => le_rfl⟩
      rwa [hf, mulVec_smul, smul_dotProduct,
        mulVec_transpose, ← dotProduct_mulVec, single_dotProduct, one_mul,
        smul_eq_mul] at this
    have h1 := aux_kr_nonneg_of u _ hu (fun t _ => key t)
    have h2 := aux_kr_nonneg_of u (-(W *ᵥ y) i) hu (fun t _ => by
      have := key (-t); rwa [neg_mul, ← mul_neg] at this)
    simp only [Pi.zero_apply]
    linarith
  · rw [← hf]
    linarith

theorem aux_kr_primal {m p : ℕ} (W : Matrix (Fin m) (Fin p) ℝ)
    (yP yM : Fin m → Fin p → ℝ)
    (hyP0 : ∀ i j, 0 ≤ yP i j) (hyP : ∀ i, W *ᵥ yP i = Pi.single i 1)
    (hyM0 : ∀ i j, 0 ≤ yM i j) (hyM : ∀ i, W *ᵥ yM i = -Pi.single i 1)
    (q : Fin p → ℝ) (h : Fin m → ℝ) :
    ∃ y : Fin p → ℝ, (∀ j, 0 ≤ y j) ∧ W *ᵥ y = h ∧
      q ⬝ᵥ y ≤ (∑ i, |h i|) * (‖q‖ * ∑ i, (∑ j, |yP i j| + ∑ j, |yM i j|)) := by
  classical
  set K := ∑ i, (∑ j, |yP i j| + ∑ j, |yM i j|) with hKdef
  have hK : ∀ i, ∑ j, |yP i j| + ∑ j, |yM i j| ≤ K :=
    fun i => Finset.single_le_sum (f := fun i => ∑ j, |yP i j| + ∑ j, |yM i j|)
      (fun i _ => by positivity) (Finset.mem_univ i)
  refine ⟨∑ i, (max (h i) 0 • yP i + max (-h i) 0 • yM i), fun j => ?_, ?_, ?_⟩
  · simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg fun i _ => add_nonneg (mul_nonneg (le_max_right _ _) (hyP0 i j))
      (mul_nonneg (le_max_right _ _) (hyM0 i j))
  · rw [mulVec_sum]
    simp only [mulVec_add, mulVec_smul, hyP, hyM, smul_neg, ← sub_eq_add_neg, ← sub_smul,
      max_zero_sub_max_neg_zero_eq_self]
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  · rw [dotProduct_sum]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h3 := aux_kr_abs_dot_le q (yP i)
    have h4 := aux_kr_abs_dot_le q (yM i)
    have hq0 : 0 ≤ ‖q‖ := norm_nonneg _
    have h6 : ‖q‖ * (∑ j, |yP i j| + ∑ j, |yM i j|) ≤ ‖q‖ * K :=
      mul_le_mul_of_nonneg_left (hK i) hq0
    have h7 : 0 ≤ ∑ j, |yP i j| := by positivity
    have h8 : 0 ≤ ∑ j, |yM i j| := by positivity
    have e1 : q ⬝ᵥ yP i ≤ ‖q‖ * K := by nlinarith [abs_le.1 h3]
    have e2 : q ⬝ᵥ yM i ≤ ‖q‖ * K := by nlinarith [abs_le.1 h4]
    have habs := max_zero_add_max_neg_zero_eq_abs_self (h i)
    have a1 : 0 ≤ max (h i) 0 := le_max_right _ _
    have a2 : 0 ≤ max (-h i) 0 := le_max_right _ _
    rw [← habs]
    nlinarith [mul_le_mul_of_nonneg_left e1 a1, mul_le_mul_of_nonneg_left e2 a2]

theorem aux_kr_lp_upper {m p : ℕ} (W : Matrix (Fin m) (Fin p) ℝ)
    (yP yM : Fin m → Fin p → ℝ)
    (hyP0 : ∀ i j, 0 ≤ yP i j) (hyP : ∀ i, W *ᵥ yP i = Pi.single i 1)
    (hyM0 : ∀ i j, 0 ≤ yM i j) (hyM : ∀ i, W *ᵥ yM i = -Pi.single i 1)
    (q : Fin p → ℝ) (h : Fin m → ℝ) :
    KallMayer.Recourse.LPValue W q h ≤
      (((∑ i, |h i|) * (‖q‖ * ∑ i, (∑ j, |yP i j| + ∑ j, |yM i j|)) : ℝ) : EReal) := by
  obtain ⟨y, hy0, hyW, hyq⟩ := aux_kr_primal W yP yM hyP0 hyP hyM0 hyM q h
  unfold KallMayer.Recourse.LPValue
  refine le_trans (sInf_le ?_) (EReal.coe_le_coe_iff.2 hyq)
  exact ⟨y, hy0, hyW, rfl⟩

theorem aux_kr_lp_lower {m p : ℕ} (W : Matrix (Fin m) (Fin p) ℝ)
    (yP yM : Fin m → Fin p → ℝ)
    (hyP0 : ∀ i j, 0 ≤ yP i j) (hyP : ∀ i, W *ᵥ yP i = Pi.single i 1)
    (hyM0 : ∀ i j, 0 ≤ yM i j) (hyM : ∀ i, W *ᵥ yM i = -Pi.single i 1)
    (q : Fin p → ℝ) (h : Fin m → ℝ) (z : Fin m → ℝ) (hz : ∀ j, (Wᵀ *ᵥ z) j ≤ q j) :
    (((-((∑ i, |h i|) * (‖q‖ * ∑ i, (∑ j, |yP i j| + ∑ j, |yM i j|)))) : ℝ) : EReal) ≤
      KallMayer.Recourse.LPValue W q h := by
  have hzb := aux_kr_dual_bound W yP yM hyP0 hyP hyM0 hyM q z hz
  have habs := aux_kr_abs_dot_le z h
  have hS0 : 0 ≤ ∑ i, |h i| := by positivity
  have hlow : -((∑ i, |h i|) * (‖q‖ * ∑ i, (∑ j, |yP i j| + ∑ j, |yM i j|))) ≤ z ⬝ᵥ h := by
    have := mul_le_mul_of_nonneg_right hzb hS0
    nlinarith [abs_le.1 habs]
  unfold KallMayer.Recourse.LPValue
  refine le_sInf ?_
  rintro r ⟨y, hy0, hyW, rfl⟩
  refine EReal.coe_le_coe_iff.2 (hlow.trans ?_)
  have := aux_kr_weak W q z hz y hy0
  rwa [hyW] at this

theorem aux_kr_lp_bot {m p : ℕ} (W : Matrix (Fin m) (Fin p) ℝ)
    (hc : KallMayer.Recourse.CompleteRecourse W) (q : Fin p → ℝ) (h : Fin m → ℝ)
    (y : Fin p → ℝ) (hy0 : ∀ j, 0 ≤ y j) (hyW : W *ᵥ y = 0) (hyq : q ⬝ᵥ y < 0) :
    KallMayer.Recourse.LPValue W q h = ⊥ := by
  obtain ⟨y0, hy00, hy0W⟩ := hc h
  rw [EReal.eq_bot_iff_forall_lt]
  intro r
  set t : ℝ := (|q ⬝ᵥ y0 - r| + 1) / (-(q ⬝ᵥ y)) with ht
  have hpos : 0 < -(q ⬝ᵥ y) := by linarith
  have ht0 : 0 ≤ t := by positivity
  have htc : t * (q ⬝ᵥ y) = -(|q ⬝ᵥ y0 - r| + 1) := by
    have hne : q ⬝ᵥ y ≠ 0 := hyq.ne
    rw [ht, div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hne, mul_one]
  unfold KallMayer.Recourse.LPValue
  refine lt_of_le_of_lt (sInf_le ⟨y0 + t • y, fun j => ?_, ?_, rfl⟩) ?_
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (hy00 j) (mul_nonneg ht0 (hy0 j))
  · rw [mulVec_add, mulVec_smul, hyW, hy0W, smul_zero, add_zero]
  · refine EReal.coe_lt_coe_iff.2 ?_
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, htc]
    have := le_abs_self (q ⬝ᵥ y0 - r)
    linarith

theorem aux_kr_resid {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    ∑ i, |(b - A *ᵥ x) i| ≤ ((m : ℝ) * (1 + ∑ k, |x k|)) * (‖A‖ + ‖b‖) := by
  have hX : 0 ≤ ∑ k, |x k| := by positivity
  have hi : ∀ i, |(b - A *ᵥ x) i| ≤ (1 + ∑ k, |x k|) * (‖A‖ + ‖b‖) := by
    intro i
    have h1 : |(A *ᵥ x) i| ≤ ‖A i‖ * ∑ k, |x k| := aux_kr_abs_dot_le (A i) x
    have h2 : ‖A i‖ ≤ ‖A‖ := norm_le_pi_norm A i
    have h3 : |b i| ≤ ‖b‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm b i
    have h4 : |(b - A *ᵥ x) i| ≤ |b i| + |(A *ᵥ x) i| := by
      rw [Pi.sub_apply]; exact abs_sub _ _
    have h5 : ‖A i‖ * ∑ k, |x k| ≤ ‖A‖ * ∑ k, |x k| := mul_le_mul_of_nonneg_right h2 hX
    have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
    have hb0 : 0 ≤ ‖b‖ := norm_nonneg _
    nlinarith
  calc ∑ i, |(b - A *ᵥ x) i| ≤ ∑ _i : Fin m, (1 + ∑ k, |x k|) * (‖A‖ + ‖b‖) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = ((m : ℝ) * (1 + ∑ k, |x k|)) * (‖A‖ + ‖b‖) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

theorem aux_kr_integrable {m n p : ℕ} (μ : Measure (RecourseData m n p))
    [IsProbabilityMeasure μ] (hmom : recourseMomentAlternative μ) :
    Integrable (fun d : RecourseData m n p => (‖d.1‖ + ‖d.2.1‖) * ‖d.2.2‖) μ := by
  rcases hmom with ⟨h1, h2, h3⟩ | ⟨⟨q0, hq⟩, hA, hb⟩ | ⟨⟨A0, b0, hAb⟩, hq⟩ | ⟨C, hC⟩
  · exact (h1.norm.add h2.norm).integrable_mul h3.norm
  · refine ((hA.norm.add hb.norm).mul_const ‖q0‖).congr (hq.mono fun d hd => ?_)
    simp [hd]
  · refine (hq.norm.const_mul (‖(fun i => A0 i : Fin m → Fin n → ℝ)‖ + ‖b0‖)).congr
      (hAb.mono fun d hd => ?_)
    simp only [hd.1, hd.2]
  · have hcont : Continuous fun d : RecourseData m n p => (‖d.1‖ + ‖d.2.1‖) * ‖d.2.2‖ := by
      fun_prop
    refine Integrable.of_bound hcont.aestronglyMeasurable ((C + C) * C) (hC.mono fun d hd => ?_)
    obtain ⟨ha, hb, hc⟩ := hd
    have h0 : 0 ≤ C := (norm_nonneg _).trans ha
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (add_le_add ha hb) hc (norm_nonneg _) (by linarith)

end Kall1976

open Kall1976 Matrix

theorem solution
    {m n p : ℕ} (μ : Measure (RecourseData m n p)) [IsProbabilityMeasure μ]
    (W : Matrix (Fin m) (Fin p) ℝ)
    (hcomplete : KallMayer.Recourse.CompleteRecourse W)
    (hmoments : recourseMomentAlternative μ)
    (x : Fin n → ℝ) :
    (∃ v : ℝ, extendedExpectedRecourse μ W x = (v : EReal)) ↔
      (∀ᵐ d ∂μ, ∃ z : Fin m → ℝ,
        ∀ j : Fin p, Matrix.mulVec W.transpose z j ≤ d.2.2 j) := by
  classical
  have hP : ∀ i : Fin m, ∃ y : Fin p → ℝ, (∀ j, 0 ≤ y j) ∧ W *ᵥ y = Pi.single i 1 :=
    fun i => hcomplete _
  have hM : ∀ i : Fin m, ∃ y : Fin p → ℝ, (∀ j, 0 ≤ y j) ∧ W *ᵥ y = -Pi.single i 1 :=
    fun i => hcomplete _
  choose yP hyP0 hyP using hP
  choose yM hyM0 hyM using hM
  have hK0 : 0 ≤ ∑ i, (∑ j, |yP i j| + ∑ j, |yM i j|) := by positivity
  have hclosed := aux_kr_closed W _ hK0 (aux_kr_dual_bound W yP yM hyP0 hyP hyM0 hyM)
  constructor
  · rintro ⟨v, hv⟩
    by_contra hnot
    rw [ae_iff] at hnot
    set N := {d : RecourseData m n p | ¬∃ z : Fin m → ℝ, ∀ j, (Wᵀ *ᵥ z) j ≤ d.2.2 j} with hN
    have hNm : MeasurableSet N :=
      (hclosed.isOpen_compl.measurableSet).preimage (measurable_snd.comp measurable_snd)
    have hbot : ∀ d ∈ N,
        (-KallMayer.Recourse.PointwiseRecourse W d.1 d.2.1 d.2.2 x).toENNReal = ⊤ := by
      intro d hd
      obtain ⟨y, hy0, hyW, hyq⟩ := aux_kr_farkas W hclosed d.2.2 hd
      unfold KallMayer.Recourse.PointwiseRecourse
      rw [aux_kr_lp_bot W hcomplete _ _ y hy0 hyW hyq]
      simp
    have htop : ∫⁻ d, (-KallMayer.Recourse.PointwiseRecourse W d.1 d.2.1 d.2.2 x).toENNReal ∂μ
        = ⊤ := by
      refine eq_top_iff.2 ?_
      calc (⊤ : ENNReal) = ∫⁻ d, N.indicator (fun _ => (⊤ : ENNReal)) d ∂μ := by
            rw [lintegral_indicator_const hNm, ENNReal.top_mul hnot]
        _ ≤ _ := lintegral_mono fun d => by
            by_cases hd : d ∈ N
            · simp [Set.indicator_of_mem hd, hbot d hd]
            · simp [Set.indicator_of_notMem hd]
    unfold extendedExpectedRecourse at hv
    rw [htop, EReal.coe_ennreal_top, EReal.sub_top] at hv
    exact EReal.bot_ne_coe v hv
  · intro hae
    have hBint := (aux_kr_integrable μ hmoments).const_mul
      (((m : ℝ) * (1 + ∑ k, |x k|)) * ∑ i, (∑ j, |yP i j| + ∑ j, |yM i j|))
    have hbound : ∀ d : RecourseData m n p,
        (∑ i, |(d.2.1 - d.1 *ᵥ x) i|) * (‖d.2.2‖ * ∑ i, (∑ j, |yP i j| + ∑ j, |yM i j|)) ≤
        (((m : ℝ) * (1 + ∑ k, |x k|)) * ∑ i, (∑ j, |yP i j| + ∑ j, |yM i j|)) *
          ((‖d.1‖ + ‖d.2.1‖) * ‖d.2.2‖) := by
      intro d
      have h := aux_kr_resid d.1 d.2.1 x
      have hq0 : 0 ≤ ‖d.2.2‖ := norm_nonneg _
      have := mul_le_mul_of_nonneg_right h (mul_nonneg hq0 hK0)
      calc _ ≤ ((m : ℝ) * (1 + ∑ k, |x k|)) * (‖d.1‖ + ‖d.2.1‖) *
            (‖d.2.2‖ * ∑ i, (∑ j, |yP i j| + ∑ j, |yM i j|)) := this
        _ = _ := by ring
    have h1 : ∫⁻ d, (KallMayer.Recourse.PointwiseRecourse W d.1 d.2.1 d.2.2 x).toENNReal ∂μ
        < ⊤ := by
      refine lt_of_le_of_lt (lintegral_mono fun d => ?_) hBint.lintegral_lt_top
      unfold KallMayer.Recourse.PointwiseRecourse
      refine (EReal.toENNReal_le_toENNReal
        (aux_kr_lp_upper W yP yM hyP0 hyP hyM0 hyM d.2.2 (d.2.1 - d.1 *ᵥ x))).trans ?_
      rw [EReal.real_coe_toENNReal]
      exact ENNReal.ofReal_le_ofReal (hbound d)
    have h2 : ∫⁻ d, (-KallMayer.Recourse.PointwiseRecourse W d.1 d.2.1 d.2.2 x).toENNReal ∂μ
        < ⊤ := by
      refine lt_of_le_of_lt (lintegral_mono_ae (hae.mono fun d hd => ?_)) hBint.lintegral_lt_top
      obtain ⟨z, hz⟩ := hd
      have hl := aux_kr_lp_lower W yP yM hyP0 hyP hyM0 hyM d.2.2 (d.2.1 - d.1 *ᵥ x) z hz
      unfold KallMayer.Recourse.PointwiseRecourse
      have hl' := EReal.neg_le_neg_iff.2 hl
      rw [EReal.coe_neg, neg_neg] at hl'
      refine (EReal.toENNReal_le_toENNReal hl').trans ?_
      rw [EReal.real_coe_toENNReal]
      exact ENNReal.ofReal_le_ofReal (hbound d)
    refine ⟨(∫⁻ d, (KallMayer.Recourse.PointwiseRecourse W d.1 d.2.1 d.2.2 x).toENNReal ∂μ).toReal
      - (∫⁻ d, (-KallMayer.Recourse.PointwiseRecourse W d.1 d.2.1 d.2.2 x).toENNReal ∂μ).toReal,
      ?_⟩
    unfold extendedExpectedRecourse
    rw [← EReal.coe_ennreal_toReal h1.ne, ← EReal.coe_ennreal_toReal h2.ne, ← EReal.coe_sub]
