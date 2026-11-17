-- Prove2me | solution 1 for N25.laurent_order_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:23.193937+00:00
-- url     : https://prove2.me/submissions/c317b520-685e-4b30-8858-71f02c451bf8

import Mathlib
import Definitions.Def_ModularCurve_QAdicPlace

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

namespace N25

private theorem cancel_laurent_coefficient
    {K : Type*} [Field K] (a b : LaurentSeries K) (n : ℤ)
    (ha : n ≤ a.order) (hb : b.order = n) (hb0 : b ≠ 0) :
    let c := a.coeff n / b.coeff n
    a - c • b = 0 ∨ n < (a - c • b).order := by
  classical
  dsimp only
  have hbn : b.coeff n ≠ 0 := by
    rw [← hb]
    exact HahnSeries.coeff_order_eq_zero.not.mpr hb0
  have below (k : ℤ) (hk : k < n) : a.coeff k = 0 ∧ b.coeff k = 0 := by
    constructor
    · by_contra h
      have := HahnSeries.order_le_of_coeff_ne_zero h
      omega
    · by_contra h
      have := HahnSeries.order_le_of_coeff_ne_zero h
      omega
  have vanished (k : ℤ) (hk : k ≤ n) :
      (a - (a.coeff n / b.coeff n) • b).coeff k = 0 := by
    change a.coeff k - (a.coeff n / b.coeff n) * b.coeff k = 0
    rcases lt_or_eq_of_le hk with hk | rfl
    · rw [(below k hk).1,(below k hk).2,mul_zero,sub_self]
    · rw [div_mul_cancel₀ _ hbn,sub_self]
  by_cases hzero : a - (a.coeff n / b.coeff n) • b = 0
  · exact Or.inl hzero
  · right
    by_contra h
    have hn : (a - (a.coeff n / b.coeff n) • b).order ≤ n := by omega
    have hcoeff := vanished _ hn
    exact (HahnSeries.coeff_order_eq_zero.not.mpr hzero) hcoeff

private theorem qSeries_smul
    {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K))
    (c : K) (x : F) :
    qSeriesBar K F (c • x) = c • qSeriesBar K F x := by
  rw [Algebra.smul_def,qSeriesBar_mul,qSeriesBar_algebraMap]
  exact HahnSeries.C_mul_eq_smul

private theorem fixed_laurent_approximations
    {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K))
    (τ : F ≃ₐ[K] F) (t : F)
    (ht : (qSeriesBar K F t).order = 1) (hτt : τ t = t)
    (x : F) (hx : 0 ≤ (qSeriesBar K F x).order) :
    ∀ n : ℕ, ∃ y : F, τ y = y ∧
      (x = y ∨ (n : ℤ) ≤ (qSeriesBar K F (x-y)).order) := by
  have ht0 : t ≠ 0 := by
    intro h
    rw [h,qSeriesBar_zero,HahnSeries.order_zero] at ht
    norm_num at ht
  intro n
  induction n with
  | zero =>
    refine ⟨0,map_zero τ,Or.inr ?_⟩
    simpa only [sub_zero,Nat.cast_zero] using hx
  | succ n ih =>
    obtain ⟨y,hy,hxy⟩ := ih
    rcases hxy with hxy | hxy
    · exact ⟨y,hy,Or.inl hxy⟩
    · have hpow : (qSeriesBar K F (t^n)).order = (n : ℤ) := by
        rw [qSeriesBar_pow,order_pow_of_ne_zero_bar (qSeriesBar_ne_zero ht0),ht,mul_one]
      have hpow0 : qSeriesBar K F (t^n) ≠ 0 := qSeriesBar_ne_zero (pow_ne_zero n ht0)
      let c : K := (qSeriesBar K F (x-y)).coeff (n:ℤ) /
        (qSeriesBar K F (t^n)).coeff (n:ℤ)
      let z : F := y+c • t^n
      have hz : τ z = z := by
        dsimp [z]
        simp only [map_add,Algebra.smul_def,map_mul,AlgEquiv.commutes,map_pow,hy,hτt]
      have he : x-z = (x-y)-c • t^n := by dsimp [z]; abel
      have hcancel := cancel_laurent_coefficient
        (qSeriesBar K F (x-y)) (qSeriesBar K F (t^n)) (n:ℤ) hxy hpow hpow0
      dsimp only at hcancel
      have hmap : qSeriesBar K F (x-z) =
          qSeriesBar K F (x-y) - c • qSeriesBar K F (t^n) := by
        rw [he,qSeriesBar_sub,qSeries_smul]
      refine ⟨z,hz,?_⟩
      rcases hcancel with hzero | horder
      · left
        exact sub_eq_zero.mp (qSeriesBar_eq_zero_iff.mp (hmap.trans hzero))
      · right
        have hh : (n:ℤ) < (qSeriesBar K F (x-z)).order := by
          rw [hmap]
          exact horder
        omega

/-- An automorphism of a Laurent-series subfield fixing an order-one element
and preserving Laurent order is the identity. Finite coefficient cancellation
suffices; no completion or generic residue-field comparison is assumed. -/
theorem _root_.solution
    (K : Type*) [Field K] (F : IntermediateField K (LaurentSeries K))
    (τ : F ≃ₐ[K] F) (t : F)
    (ht : (qSeriesBar K F t).order = 1)
    (hτt : τ t = t)
    (hord : ∀ x : F, (qSeriesBar K F (τ x)).order =
      (qSeriesBar K F x).order) :
    τ = 1 := by
  classical
  have integral_fixed (x : F) (hx : 0 ≤ (qSeriesBar K F x).order) : τ x = x := by
    by_contra hne
    have he0 : τ x-x ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨n,hn⟩ := exists_nat_gt (qSeriesBar K F (τ x-x)).order
    obtain ⟨y,hy,happrox⟩ := fixed_laurent_approximations F τ t ht hτt x hx n
    rcases happrox with hxy | happrox
    · apply hne
      rw [hxy]
      exact hy
    · have he : τ x-x = τ (x-y)-(x-y) := by rw [map_sub,hy]; abel
      have hdiff : qSeriesBar K F (τ (x-y)) + -(qSeriesBar K F (x-y)) ≠ 0 := by
        rw [← qSeriesBar_neg,← qSeriesBar_add]
        rw [← sub_eq_add_neg]
        rw [← he]
        exact qSeriesBar_ne_zero he0
      have hbound := HahnSeries.min_order_le_order_add hdiff
      rw [HahnSeries.order_neg,hord,min_self] at hbound
      rw [← sub_eq_add_neg,← qSeriesBar_sub] at hbound
      rw [← he] at hbound
      omega
  have ht0 : t ≠ 0 := by
    intro h
    rw [h,qSeriesBar_zero,HahnSeries.order_zero] at ht
    norm_num at ht
  apply AlgEquiv.ext
  intro x
  change τ x = x
  by_cases hx : 0 ≤ (qSeriesBar K F x).order
  · exact integral_fixed x hx
  · have hx0 : x ≠ 0 := by
      intro h
      rw [h,qSeriesBar_zero,HahnSeries.order_zero] at hx
      omega
    let n := (-(qSeriesBar K F x).order).toNat
    have hn : (n : ℤ) = -(qSeriesBar K F x).order :=
      Int.toNat_of_nonneg (by omega)
    have hy : (qSeriesBar K F (t^n*x)).order = 0 := by
      rw [order_qSeriesBar_mul (pow_ne_zero n ht0) hx0,qSeriesBar_pow,
        order_pow_of_ne_zero_bar (qSeriesBar_ne_zero ht0),ht,mul_one,hn]
      ring
    have hfix := integral_fixed (t^n*x) (by rw [hy])
    rw [map_mul,map_pow,hτt] at hfix
    exact mul_left_cancel₀ (pow_ne_zero n ht0) hfix

end N25
