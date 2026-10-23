-- Prove2me | solution 1 for HessianDamping.IPAHD.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T15:25:11.863789+00:00
-- url     : https://prove2.me/submissions/c6d96253-2ee6-427b-bf78-f3a50fe4ac9f

import Mathlib
import Definitions.Def_GoldenRatioVI_Shared_IsProxPoint
import Definitions.Def_HessianDamping_IPAHD_Setting

set_option autoImplicit false

namespace IPAHD4Aux

open HessianDamping.IPAHD GoldenRatioVI.Shared

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma inner_gradient (f : H → ℝ) (x v : H) :
    inner ℝ (gradient f x) v = fderiv ℝ f x v := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

lemma convex_first_order (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f)
    (hfd : Differentiable ℝ f) (x y : H) :
    f x + inner ℝ (gradient f x) (y - x) ≤ f y := by
  have hc : ConvexOn ℝ Set.univ (f ∘ (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] H)) := by
    have := hfconv.comp_affineMap (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] H)
    simpa using this
  have hd : HasDerivAt (f ∘ (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] H)) (fderiv ℝ f x (y - x)) 0 := by
    have h1 : HasDerivAt (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] H) (y - x) 0 :=
      AffineMap.hasDerivAt_lineMap
    have h2 : HasFDerivAt f (fderiv ℝ f x) ((AffineMap.lineMap x y : ℝ →ᵃ[ℝ] H) (0:ℝ)) := by
      simpa using (hfd x).hasFDerivAt
    exact h2.comp_hasDerivAt (0:ℝ) h1
  have := hc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  rw [slope_def_field] at this
  simp at this
  rw [inner_gradient, map_sub]
  linarith

lemma prox_opt (f : H → ℝ) (hfd : Differentiable ℝ f) (μ : ℝ) (y xp : H)
    (hp : IsProxPoint (fun z => ((μ * f z : ℝ) : EReal)) y xp) :
    xp = y - μ • gradient f xp := by
  set φ : H → ℝ := fun z => μ * f z + (1 / 2 : ℝ) * ‖z - y‖ ^ 2 with hφ
  have hmin : IsLocalMin φ xp := by
    refine Filter.Eventually.of_forall (fun z => ?_)
    have := hp z
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    simp only [hφ]
    linarith
  have hD := ((hfd xp).hasFDerivAt.const_mul μ).add
    ((((hasFDerivAt_id xp).sub_const y).norm_sq).const_mul (1 / 2 : ℝ))
  have h0 := hmin.hasFDerivAt_eq_zero hD
  set d : H := xp - y + μ • gradient f xp with hd
  have hz := congrArg (fun L => L d) h0
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.zero_apply,
    id_eq, smul_eq_mul, ContinuousLinearMap.id_apply, nsmul_eq_mul] at hz
  rw [← inner_gradient] at hz
  have hdd : inner ℝ d d = 0 := by
    have e : inner ℝ d d = μ * inner ℝ (gradient f xp) d + inner ℝ (xp - y) d := by
      rw [hd, inner_add_left, inner_smul_left]
      simp
      ring
    rw [e]
    push_cast at hz
    linarith
  have h00 : d = 0 := inner_self_eq_zero.mp hdd
  rw [hd] at h00
  calc xp = (xp - y + μ • gradient f xp) + y - μ • gradient f xp := by abel
    _ = y - μ • gradient f xp := by rw [h00, zero_add]

lemma v_step (f : H → ℝ) (α h : ℝ) (hh : 0 < h) (hα : 1 ≤ α) (β b : ℕ → ℝ) (x : ℕ → H)
    (xstar : H) (k : ℕ) (hk : 1 ≤ k)
    (hxk : x (k + 1) = yK f α (h ^ 2) β x k - muK α (h ^ 2) β b k • gradient f (x (k + 1))) :
    vK f α h β x xstar (k + 1) = vK f α h β x xstar k
      - (h * (b k * h * k - β (k + 1) - k * (β (k + 1) - β k))) • gradient f (x (k + 1)) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hka : (k : ℝ) + α ≠ 0 := by linarith
  have hsq : Real.sqrt (h ^ 2) = h := Real.sqrt_sq hh.le
  unfold vK
  generalize gradient f (x (k + 1)) = g' at hxk ⊢
  simp only [Nat.add_sub_cancel]
  rw [hxk]
  unfold yK muK
  rw [hsq]
  push_cast
  match_scalars <;> field_simp <;> ring

lemma energy_step (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfd : Differentiable ℝ f)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y) (α : ℝ) (hα : 1 ≤ α) (h : ℝ) (hh : 0 < h)
    (β b : ℕ → ℝ) (x : ℕ → H) (hx : IsIPAHDRun f α (h ^ 2) β b x) (k : ℕ) (hk : 1 ≤ k)
    (hD : 0 ≤ b k * h * k - β (k + 1) - k * (β (k + 1) - β k))
    (hG3 : deltaK h β b (k + 1) - deltaK h β b k ≤ (α - 1) * deltaK h β b k / ((k : ℝ) + 1)) :
    EK f α h β b x xstar (k + 1)
        + h * (deltaK h β b k * β (k + 1) * ‖gradient f (x (k + 1))‖ ^ 2)
      ≤ EK f α h β b x xstar k := by
  have hprox := prox_opt f hfd _ _ _ (hx k hk)
  have hv := v_step f α h hh hα β b x xstar k hk hprox
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  set g := gradient f (x (k + 1)) with hg
  set D := h * (b k * h * k - β (k + 1) - k * (β (k + 1) - β k)) with hDdef
  have hD0 : 0 ≤ D := mul_nonneg hh.le hD
  have hdelta : deltaK h β b k = D * ((k : ℝ) + 1) := by simp only [deltaK, hDdef]
  have hG3' : deltaK h β b (k + 1) - D * ((k : ℝ) + 1) ≤ (α - 1) * D := by
    rw [hdelta] at hG3
    rwa [show (α - 1) * (D * ((k : ℝ) + 1)) / ((k : ℝ) + 1) = (α - 1) * D by field_simp] at hG3
  have hinner : inner ℝ g (vK f α h β x xstar (k + 1))
      = (α - 1) * inner ℝ g (x (k + 1) - xstar) + ((k : ℝ) + 1) * inner ℝ g (x (k + 1) - x k)
        + ((k : ℝ) + 1) * (β (k + 1) * h) * ‖g‖ ^ 2 := by
    simp only [vK, Nat.add_sub_cancel, inner_add_right, inner_smul_right, ← hg,
      real_inner_self_eq_norm_sq]
    push_cast
    ring
  have hnorm : ‖vK f α h β x xstar k‖ ^ 2 = ‖vK f α h β x xstar (k + 1)‖ ^ 2
      + 2 * D * inner ℝ g (vK f α h β x xstar (k + 1)) + D ^ 2 * ‖g‖ ^ 2 := by
    have : vK f α h β x xstar k = vK f α h β x xstar (k + 1) + D • g := by rw [hv]; abel
    rw [this, norm_add_sq_real, norm_smul, inner_smul_right, real_inner_comm,
      Real.norm_eq_abs, abs_of_nonneg hD0]
    ring
  have hc1 := convex_first_order f hfconv hfd (x (k + 1)) xstar
  have hc2 := convex_first_order f hfconv hfd (x (k + 1)) (x k)
  have e1 : inner ℝ g (xstar - x (k + 1)) = - inner ℝ g (x (k + 1) - xstar) := by
    rw [← inner_neg_right, neg_sub]
  have e2 : inner ℝ g (x k - x (k + 1)) = - inner ℝ g (x (k + 1) - x k) := by
    rw [← inner_neg_right, neg_sub]
  rw [e1] at hc1
  rw [e2] at hc2
  have hF' : 0 ≤ f (x (k + 1)) - f xstar := sub_nonneg.mpr (hxstar _)
  have hα1 : 0 ≤ α - 1 := by linarith
  have m1 := mul_le_mul_of_nonneg_left
    (show f (x (k + 1)) - f xstar ≤ inner ℝ g (x (k + 1) - xstar) by linarith)
    (mul_nonneg hD0 hα1)
  have m2 := mul_le_mul_of_nonneg_left
    (show f (x (k + 1)) - f (x k) ≤ inner ℝ g (x (k + 1) - x k) by linarith)
    (mul_nonneg hD0 (by positivity : (0:ℝ) ≤ (k : ℝ) + 1))
  have m3 := mul_le_mul_of_nonneg_right hG3' hF'
  have m4 : 0 ≤ D ^ 2 * ‖g‖ ^ 2 := by positivity
  unfold EK
  rw [hdelta]
  have hinnerD := congrArg (fun t => D * t) hinner
  linarith [hnorm, hinnerD, m1, m2, m3, m4]

end IPAHD4Aux

open HessianDamping.IPAHD in
theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC1 : ContDiff ℝ 1 f)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (α : ℝ) (hα : 1 ≤ α)
    (h s : ℝ) (hh : 0 < h) (hs : s = h ^ 2)
    (β b : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (hb : ∀ k, 0 ≤ b k)
    (x : ℕ → H) (hx : IsIPAHDRun f α s β b x)
    (k₀ : ℕ) (hk₀ : 1 ≤ k₀)
    (hG2 : ∀ k : ℕ, k₀ ≤ k → 0 < b k * h * k - β (k + 1) - k * (β (k + 1) - β k))
    (hG3 : ∀ k : ℕ, k₀ ≤ k →
      deltaK h β b (k + 1) - deltaK h β b k ≤ (α - 1) * deltaK h β b k / ((k : ℝ) + 1)) :
    (∀ k : ℕ, k₀ ≤ k → 0 < deltaK h β b k) ∧
    (fun k : ℕ => f (x k) - f xstar) =O[Filter.atTop] (fun k : ℕ => 1 / deltaK h β b k) ∧
    Summable (fun k : ℕ => deltaK h β b k * β (k + 1) * ‖gradient f (x (k + 1))‖ ^ 2) := by
  subst hs
  have hfd : Differentiable ℝ f := hfC1.differentiable (by norm_num)
  have hδpos : ∀ k, k₀ ≤ k → 0 < deltaK h β b k := fun k hk => by
    unfold deltaK
    exact mul_pos (mul_pos hh (hG2 k hk)) (by positivity)
  set E : ℕ → ℝ := fun k => EK f α h β b x xstar k with hE
  set a : ℕ → ℝ := fun k => deltaK h β b k * β (k + 1) * ‖gradient f (x (k + 1))‖ ^ 2 with ha
  have hstep : ∀ k, k₀ ≤ k → E (k + 1) + h * a k ≤ E k := fun k hk =>
    IPAHD4Aux.energy_step f hfconv hfd xstar hxstar α hα h hh β b x hx k (hk₀.trans hk)
      (hG2 k hk).le (hG3 k hk)
  have ha0 : ∀ k, k₀ ≤ k → 0 ≤ a k := fun k hk => by
    simp only [ha]
    have := hδpos k hk
    have := hβ (k + 1)
    positivity
  have hdF : ∀ k, k₀ ≤ k → deltaK h β b k * (f (x k) - f xstar) ≤ E k := fun k hk => by
    simp only [hE, EK]
    have : 0 ≤ 1 / 2 * ‖vK f α h β x xstar k‖ ^ 2 := by positivity
    linarith
  have hsum : ∀ n, h * (∑ i ∈ Finset.range n, a (i + k₀)) + E (n + k₀) ≤ E k₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add]
      have := hstep (n + k₀) (by omega)
      rw [show n + 1 + k₀ = n + k₀ + 1 by omega]
      linarith
  have hEnn : ∀ k, k₀ ≤ k → 0 ≤ E k := fun k hk => by
    have := hdF k hk
    have := mul_nonneg (hδpos k hk).le (sub_nonneg.mpr (hxstar (x k)))
    linarith
  refine ⟨hδpos, ?_, ?_⟩
  · refine Asymptotics.IsBigO.of_bound (E k₀) (Filter.eventually_atTop.2 ⟨k₀, fun k hk => ?_⟩)
    have hδ := hδpos k hk
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
    have h1 := hsum n
    have h2 := hdF (k₀ + n) hk
    have h3 : 0 ≤ ∑ i ∈ Finset.range n, a (i + k₀) :=
      Finset.sum_nonneg (fun i _ => ha0 _ (by omega))
    rw [show n + k₀ = k₀ + n by omega] at h1
    have h4 : 0 ≤ h * ∑ i ∈ Finset.range n, a (i + k₀) := mul_nonneg hh.le h3
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hxstar _)),
      abs_of_pos (by positivity), mul_one_div, le_div_iff₀ hδ]
    linarith
  · have hs : Summable (fun n => a (n + k₀)) := by
      refine summable_of_sum_range_le (c := E k₀ / h) (fun n => ha0 _ (by omega)) (fun n => ?_)
      have h1 := hsum n
      have h2 := hEnn (n + k₀) (by omega)
      rw [le_div_iff₀ hh]
      linarith
    exact (summable_nat_add_iff k₀).mp hs
