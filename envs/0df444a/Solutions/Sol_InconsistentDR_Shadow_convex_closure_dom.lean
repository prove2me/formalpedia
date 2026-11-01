-- Prove2me | solution 1 for InconsistentDR.Shadow.convex_closure_dom
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T23:52:35.749633+00:00
-- url     : https://prove2.me/submissions/036623a7-314e-46e8-b33a-2bce55c09c3a

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators

open scoped InnerProductSpace Topology
open Filter ThreeOpSplitting.Convergence

namespace DRCvxAux

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Resolvents of monotone operators are nonexpansive. -/
lemma res_nonexp (A : X → Set X) (hA : IsMonotoneOp A) (μ : ℝ) (hμ : 0 < μ) (J : X → X)
    (hJ : IsResolvent μ A J) (x y : X) : ‖J x - J y‖ ≤ ‖x - y‖ := by
  have h := hA _ _ _ _ (hJ x) (hJ y)
  rw [← smul_sub, real_inner_smul_right] at h
  have h' : 0 ≤ ⟪J x - J y, (x - J x) - (y - J y)⟫_ℝ := by
    have := (mul_nonneg_iff_of_pos_left (inv_pos.mpr hμ)).mp h
    exact this
  have e : (x - J x) - (y - J y) = (x - y) - (J x - J y) := by abel
  rw [e, inner_sub_right, real_inner_self_eq_norm_sq] at h'
  have h2 : ‖J x - J y‖ ^ 2 ≤ ‖J x - J y‖ * ‖x - y‖ :=
    (by linarith : ‖J x - J y‖ ^ 2 ≤ ⟪J x - J y, x - y⟫_ℝ).trans (real_inner_le_norm _ _)
  by_cases h0 : ‖J x - J y‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖J x - J y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

/-- From the resolvent of `μ A` to that of `(3/4) μ A` (Banach fixed point). -/
lemma res_step [CompleteSpace X] (A : X → Set X) (hA : IsMonotoneOp A) (μ : ℝ) (hμ : 0 < μ)
    (J : X → X) (hJ : IsResolvent μ A J) : ∃ J' : X → X, IsResolvent (3 / 4 * μ) A J' := by
  have hK0 : (0 : ℝ) ≤ 1 / 3 := by norm_num
  have key : ∀ x : X, ∃ y : X, J ((4 / 3 : ℝ) • x - (1 / 3 : ℝ) • y) = y := by
    intro x
    let Φ : X → X := fun y => J ((4 / 3 : ℝ) • x - (1 / 3 : ℝ) • y)
    have hlip : LipschitzWith ⟨1 / 3, hK0⟩ Φ := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      simp only [Φ, dist_eq_norm]
      show _ ≤ (1 / 3 : ℝ) * _
      refine (res_nonexp A hA μ hμ J hJ _ _).trans (le_of_eq ?_)
      have e : (4 / 3 : ℝ) • x - (1 / 3 : ℝ) • a - ((4 / 3 : ℝ) • x - (1 / 3 : ℝ) • b) =
          (-(1 / 3 : ℝ)) • (a - b) := by module
      rw [e, norm_smul]; norm_num
    have hcon : ContractingWith ⟨1 / 3, hK0⟩ Φ :=
      ⟨by exact_mod_cast (by norm_num : (1 / 3 : ℝ) < 1), hlip⟩
    exact ⟨_, hcon.fixedPoint_isFixedPt⟩
  choose J' hJ' using key
  refine ⟨J', fun x => ?_⟩
  have h := hJ ((4 / 3 : ℝ) • x - (1 / 3 : ℝ) • J' x)
  rw [hJ' x] at h
  have e : μ⁻¹ • ((4 / 3 : ℝ) • x - (1 / 3 : ℝ) • J' x - J' x) = (3 / 4 * μ)⁻¹ • (x - J' x) := by
    rw [show (4 / 3 : ℝ) • x - (1 / 3 : ℝ) • J' x - J' x = (4 / 3 : ℝ) • (x - J' x) by module,
      smul_smul]
    congr 1
    field_simp
  rw [e] at h
  exact h

lemma res_pow [CompleteSpace X] (A : X → Set X) (hA : IsMonotoneOp A) (J : X → X)
    (hJ : IsResolvent 1 A J) : ∀ k : ℕ, ∃ J' : X → X, IsResolvent ((3 / 4 : ℝ) ^ k) A J' := by
  intro k
  induction k with
  | zero => exact ⟨J, by simpa using hJ⟩
  | succ k ih =>
    obtain ⟨J', hJ'⟩ := ih
    obtain ⟨J'', hJ''⟩ := res_step A hA _ (by positivity) J' hJ'
    exact ⟨J'', by rw [pow_succ, mul_comm]; exact hJ''⟩

/-- Points of segments between points of `dom A` lie in `cl dom A`. -/
lemma segment_mem [CompleteSpace X] (A : X → Set X) (hA : IsMonotoneOp A) (J : X → X)
    (hJ : IsResolvent 1 A J) {a b : X} (ha : a ∈ dom A) (hb : b ∈ dom A) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (1 - t) • a + t • b ∈ closure (dom A) := by
  obtain ⟨as, has⟩ := ha
  obtain ⟨bs, hbs⟩ := hb
  set c := (1 - t) • a + t • b with hc
  set M := ‖as‖ + ‖bs‖ with hM
  set K := ‖c - a‖ * ‖as‖ + ‖c - b‖ * ‖bs‖ with hK
  have hM0 : 0 ≤ M := by positivity
  have hK0 : 0 ≤ K := by positivity
  rw [Metric.mem_closure_iff]
  intro ε hε
  -- a small resolvent parameter
  have hsmall : ∃ k : ℕ, (3 / 4 : ℝ) ^ k * (M ^ 2 + 2 * K + 1) < ε ^ 2 := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)).mul_const (M ^ 2 + 2 * K + 1)
    rw [zero_mul] at h
    exact (h.eventually (gt_mem_nhds (by positivity))).exists
  obtain ⟨k, hk⟩ := hsmall
  set lam := (3 / 4 : ℝ) ^ k with hlam
  have hlam0 : 0 < lam := by positivity
  have hlam1 : lam ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨Jl, hJl⟩ := res_pow A hA J hJ k
  set y := Jl c with hy
  have hyA := hJl c
  refine ⟨y, ⟨_, hyA⟩, ?_⟩
  rw [dist_eq_norm]
  -- monotonicity against `(a, as)` and `(b, bs)`
  have h1 := hA _ _ _ _ hyA has
  have h2 := hA _ _ _ _ hyA hbs
  rw [inner_sub_right, real_inner_smul_right] at h1 h2
  have e : (1 - t) • (y - a) + t • (y - b) = y - c := by rw [hc]; module
  have hcomb : ⟪y - c, c - y⟫_ℝ ≥ lam * ((1 - t) * ⟪y - a, as⟫_ℝ + t * ⟪y - b, bs⟫_ℝ) := by
    have i1 : lam * ⟪y - a, as⟫_ℝ ≤ ⟪y - a, c - y⟫_ℝ := by
      have := mul_le_mul_of_nonneg_left (by linarith : ⟪y - a, as⟫_ℝ ≤ lam⁻¹ * ⟪y - a, c - y⟫_ℝ)
        hlam0.le
      rwa [← mul_assoc, mul_inv_cancel₀ hlam0.ne', one_mul] at this
    have i2 : lam * ⟪y - b, bs⟫_ℝ ≤ ⟪y - b, c - y⟫_ℝ := by
      have := mul_le_mul_of_nonneg_left (by linarith : ⟪y - b, bs⟫_ℝ ≤ lam⁻¹ * ⟪y - b, c - y⟫_ℝ)
        hlam0.le
      rwa [← mul_assoc, mul_inv_cancel₀ hlam0.ne', one_mul] at this
    rw [← e, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    nlinarith [mul_le_mul_of_nonneg_left i1 (by linarith : (0 : ℝ) ≤ 1 - t),
      mul_le_mul_of_nonneg_left i2 ht0]
  set r := ‖c - y‖ with hr
  have hyc : ⟪y - c, c - y⟫_ℝ = -r ^ 2 := by
    rw [← neg_sub c y, inner_neg_left, real_inner_self_eq_norm_sq]
  -- bounds on the inner products
  have b1 : -⟪y - a, as⟫_ℝ ≤ (r + ‖c - a‖) * ‖as‖ := by
    have := neg_le_abs ⟪y - a, as⟫_ℝ
    have h := abs_real_inner_le_norm (y - a) as
    have hn : ‖y - a‖ ≤ r + ‖c - a‖ := by
      calc ‖y - a‖ = ‖(y - c) + (c - a)‖ := by congr 1; abel
        _ ≤ ‖y - c‖ + ‖c - a‖ := norm_add_le _ _
        _ = r + ‖c - a‖ := by rw [hr, norm_sub_rev]
    nlinarith [norm_nonneg as]
  have b2 : -⟪y - b, bs⟫_ℝ ≤ (r + ‖c - b‖) * ‖bs‖ := by
    have := neg_le_abs ⟪y - b, bs⟫_ℝ
    have h := abs_real_inner_le_norm (y - b) bs
    have hn : ‖y - b‖ ≤ r + ‖c - b‖ := by
      calc ‖y - b‖ = ‖(y - c) + (c - b)‖ := by congr 1; abel
        _ ≤ ‖y - c‖ + ‖c - b‖ := norm_add_le _ _
        _ = r + ‖c - b‖ := by rw [hr, norm_sub_rev]
    nlinarith [norm_nonneg bs]
  have hr2 : r ^ 2 ≤ lam * (M * r + K) := by
    have q1 := mul_le_mul_of_nonneg_left b1 (by linarith : (0 : ℝ) ≤ 1 - t)
    have q2 := mul_le_mul_of_nonneg_left b2 ht0
    have hr0 : 0 ≤ r := norm_nonneg _
    have q3 : (1 - t) * ((r + ‖c - a‖) * ‖as‖) + t * ((r + ‖c - b‖) * ‖bs‖) ≤ M * r + K := by
      have hX : 0 ≤ (r + ‖c - a‖) * ‖as‖ := by positivity
      have hY : 0 ≤ (r + ‖c - b‖) * ‖bs‖ := by positivity
      have i1 : (1 - t) * ((r + ‖c - a‖) * ‖as‖) ≤ (r + ‖c - a‖) * ‖as‖ := by nlinarith
      have i2 : t * ((r + ‖c - b‖) * ‖bs‖) ≤ (r + ‖c - b‖) * ‖bs‖ := by nlinarith
      have e : M * r + K = (r + ‖c - a‖) * ‖as‖ + (r + ‖c - b‖) * ‖bs‖ := by rw [hM, hK]; ring
      linarith
    nlinarith
  have hr3 : r ^ 2 ≤ lam * (M ^ 2 + 2 * K + 1) := by
    have : lam * (M * r) ≤ r ^ 2 / 2 + lam ^ 2 * M ^ 2 / 2 := by
      nlinarith [sq_nonneg (r - lam * M)]
    have hl2 : lam ^ 2 ≤ lam := by nlinarith
    have hl3 : lam ^ 2 * M ^ 2 ≤ lam * M ^ 2 := mul_le_mul_of_nonneg_right hl2 (sq_nonneg M)
    have e1 : lam * (M * r + K) = lam * (M * r) + lam * K := by ring
    have e2 : lam * (M ^ 2 + 2 * K + 1) = lam * M ^ 2 + 2 * (lam * K) + lam := by ring
    linarith
  have hr4 : r ^ 2 < ε ^ 2 := lt_of_le_of_lt hr3 hk
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hr4

end DRCvxAux

theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (A : X → Set X) (hA : IsMonotoneOp A) (J : X → X)
    (hJ : IsResolvent 1 A J) :
    Convex ℝ (closure (dom A)) := by
  intro a ha b hb s t hs ht hst
  have hcont : Continuous (fun p : X × X => s • p.1 + t • p.2) := by fun_prop
  have := map_mem_closure₂ (f := fun a b : X => s • a + t • b) (u := closure (dom A))
    (by fun_prop) ha hb (fun x hx y hy => by
      have h := DRCvxAux.segment_mem A hA J hJ hx hy ht (by linarith)
      rwa [show 1 - t = s by linarith] at h)
  rwa [closure_closure] at this
