-- Prove2me | solution 1 for NestedLogitVariants.PowersDelta.nonempty_case
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:21:12.406413+00:00
-- url     : https://prove2.me/submissions/bf3c0ade-d1fb-4477-9bbb-f30abd65a4d8

import Mathlib
import Definitions.Def_NestedLogitVariants_PowersDelta_Levels

set_option autoImplicit false

namespace NestedLogitVariants.PowersDelta

private theorem prep_V_nonneg {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (S : Finset (Fin n)) : 0 ≤ V I i S :=
  add_nonneg (hI.vnp_nonneg i) (Finset.sum_nonneg fun j _ => (hI.v_pos i j).le)

private theorem prep_R_nonneg {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (S : Finset (Fin n)) : 0 ≤ R I i S := by
  exact div_nonneg (Finset.sum_nonneg fun j _ =>
    mul_nonneg (hI.r_nonneg i j) (hI.v_pos i j).le) (prep_V_nonneg I hI i S)

private theorem prep_lp4_opt_nonneg {ι : Type*} [Fintype ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (A : ι → Set (Finset (Fin n))) (xh : ℝ) (yh : ι → ℝ)
    (hopt : LP4Optimal I A xh yh) : 0 ≤ xh := by
  have hfeas : LP4Feasible I A (2 * xh) (fun i => 2 * yh i) := by
    constructor
    · rw [← Finset.mul_sum]
      nlinarith [hopt.1.1]
    · intro i S hS
      have hc := hopt.1.2 i S hS
      have hwr : 0 ≤ nestWeight I i S * R I i S :=
        mul_nonneg (Real.rpow_nonneg (prep_V_nonneg I hI i S) _) (prep_R_nonneg I hI i S)
      nlinarith
  have hm := hopt.2 (2 * xh) (fun i => 2 * yh i) hfeas
  linarith

private theorem xh_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n] (I : Instance ι n)
    (hI : I.Standing) (γbar : ℝ) (hγbar : IsGreatest (Set.range I.γ) γbar) (hγbar1 : 1 < γbar)
    (δ : ℝ) (hδ : 1 < δ)
    (Sh : ι → ℤ → Finset (Fin n)) (hSh : IsPowersFamily I δ Sh)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (powersCandidates I δ Sh) xh yh) :
    0 ≤ xh :=
  prep_lp4_opt_nonneg I hI _ xh yh hopt

private theorem exists_level {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n] (I : Instance ι n)
    (hI : I.Standing) (γbar : ℝ) (hγbar : IsGreatest (Set.range I.γ) γbar) (hγbar1 : 1 < γbar)
    (δ : ℝ) (hδ : 1 < δ)
    (i : ι) (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∃ l : ℤ, lL I i δ ≤ l ∧ l ≤ lU I i δ ∧ InLevel I i δ l S := by
  have hvL : 0 < vL I i := by
    apply add_pos_of_nonneg_of_pos (hI.vnp_nonneg i)
    exact (Finset.lt_inf'_iff _).2 fun j _ => hI.v_pos i j
  have hlow : vL I i ≤ V I i S := by
    obtain ⟨j, hj⟩ := hS
    apply add_le_add le_rfl
    exact (Finset.inf'_le _ (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => (hI.v_pos i k).le) hj)
  have hupp : V I i S ≤ vU I i := by
    apply add_le_add le_rfl
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun j _ _ => (hI.v_pos i j).le)
  have hv : 0 < V I i S := hvL.trans_le hlow
  refine ⟨⌈Real.logb δ (V I i S)⌉, ?_, ?_, ?_, ?_⟩
  · exact Int.ceil_mono (Real.logb_le_logb_of_le hδ hvL hlow)
  · exact Int.ceil_mono (Real.logb_le_logb_of_le hδ hv hupp)
  · rw [← Real.rpow_intCast]
    apply (Real.le_logb_iff_rpow_le hδ hv).mp
    have hc := Int.ceil_lt_add_one (Real.logb δ (V I i S))
    push_cast
    linarith
  · rw [← Real.rpow_intCast]
    exact (Real.logb_le_iff_le_rpow hδ hv).mp (Int.le_ceil _)

private theorem rpow_lower_bound_hat (δ γ a : ℝ) (l : ℤ) (hδ : 1 < δ) (hγ : 0 < γ)
    (ha1 : δ ^ (l - 1) ≤ a) (ha2 : a ≤ δ ^ l) :
    (δ ^ l) ^ (γ - 1) * δ ^ (-max (γ - 1) 0) ≤ a ^ (γ - 1) := by
  have hδ0 : 0 < δ := lt_trans zero_lt_one hδ
  have hz : 0 < δ ^ (l - 1) := zpow_pos hδ0 _
  have ha0 : 0 < a := lt_of_lt_of_le hz ha1
  by_cases hg : 0 ≤ γ - 1
  · rw [max_eq_left hg]
    calc
      (δ ^ l) ^ (γ - 1) * δ ^ (-(γ - 1)) =
          (δ ^ (l - 1)) ^ (γ - 1) := by
        rw [← Real.rpow_intCast δ l, ← Real.rpow_mul hδ0.le,
          ← Real.rpow_add hδ0, ← Real.rpow_intCast δ (l - 1),
          ← Real.rpow_mul hδ0.le]
        congr 1
        push_cast
        ring
      _ ≤ a ^ (γ - 1) := Real.rpow_le_rpow hz.le ha1 hg
  · have hg' : γ - 1 ≤ 0 := le_of_not_ge hg
    rw [max_eq_right hg', neg_zero, Real.rpow_zero, mul_one]
    exact Real.rpow_le_rpow_of_nonpos ha0 ha2 hg'

private theorem rpow_lower_bound_level (δ γ a : ℝ) (l : ℤ) (hδ : 1 < δ) (hγ : 0 < γ)
    (ha1 : δ ^ (l - 1) ≤ a) (ha2 : a ≤ δ ^ l) :
    δ ^ (-max (1 - γ) 0) * a ^ (γ - 1) ≤ (δ ^ l) ^ (γ - 1) := by
  have hδ0 : 0 < δ := lt_trans zero_lt_one hδ
  have hz : 0 < δ ^ (l - 1) := zpow_pos hδ0 _
  have ha0 : 0 < a := lt_of_lt_of_le hz ha1
  by_cases hg : 0 ≤ γ - 1
  · rw [max_eq_right (by linarith : 1 - γ ≤ 0), neg_zero, Real.rpow_zero, one_mul]
    exact Real.rpow_le_rpow ha0.le ha2 hg
  · have hg' : γ - 1 ≤ 0 := le_of_not_ge hg
    rw [max_eq_left (by linarith : 0 ≤ 1 - γ)]
    calc
      δ ^ (-(1 - γ)) * a ^ (γ - 1) ≤
          δ ^ (-(1 - γ)) * (δ ^ (l - 1)) ^ (γ - 1) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hz ha1 hg')
          (Real.rpow_nonneg hδ0.le _)
      _ = (δ ^ l) ^ (γ - 1) := by
        rw [← Real.rpow_intCast δ (l - 1), ← Real.rpow_mul hδ0.le,
          ← Real.rpow_add hδ0, ← Real.rpow_intCast δ l,
          ← Real.rpow_mul hδ0.le]
        congr 1
        push_cast
        ring

private theorem exponent_ge_one (δ γ γbar : ℝ) (hδ : 1 < δ) (hγ : 0 < γ)
    (hγle : γ ≤ γbar) (hγbar1 : 1 < γbar) :
    1 ≤ δ ^ γbar * δ ^ (-max (γ - 1) 0) * δ ^ (-max (1 - γ) 0) ∧
      δ ^ (γbar + γ + 1) ≤ δ ^ (2 * γbar + 1) := by
  have hδ0 : 0 < δ := lt_trans zero_lt_one hδ
  constructor
  · rw [← Real.rpow_add hδ0, ← Real.rpow_add hδ0]
    have he : 0 ≤ γbar + -max (γ - 1) 0 + -max (1 - γ) 0 := by
      by_cases hg : 1 ≤ γ
      · rw [max_eq_left (by linarith : 0 ≤ γ - 1),
          max_eq_right (by linarith : 1 - γ ≤ 0)]
        linarith
      · rw [max_eq_right (by linarith : γ - 1 ≤ 0),
          max_eq_left (by linarith : 0 ≤ 1 - γ)]
        linarith
    simpa using Real.rpow_le_rpow_of_exponent_le hδ.le he
  · exact Real.rpow_le_rpow_of_exponent_le hδ.le (by linarith)

private theorem prep_weight_revenue {ι : Type*} {n : ℕ} (I : Instance ι n)
    (i : ι) (S : Finset (Fin n)) (hV : 0 < V I i S) :
    nestWeight I i S * R I i S =
      V I i S ^ (I.γ i - 1) * (∑ j ∈ S, I.r i j * I.v i j) := by
  unfold nestWeight R
  rw [Real.rpow_sub hV, Real.rpow_one]
  ring

end NestedLogitVariants.PowersDelta

open NestedLogitVariants.PowersDelta

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n] (I : Instance ι n)
    (hI : I.Standing) (γbar : ℝ) (hγbar : IsGreatest (Set.range I.γ) γbar) (hγbar1 : 1 < γbar)
    (δ : ℝ) (hδ : 1 < δ)
    (Sh : ι → ℤ → Finset (Fin n)) (hSh : IsPowersFamily I δ Sh)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (powersCandidates I δ Sh) xh yh)
    (i : ι) (S : Finset (Fin n)) (hS : S.Nonempty) :
    nestWeight I i S * (R I i S - δ ^ (2 * γbar + 1) * xh) ≤ δ ^ (γbar + 1) * yh i := by
  have hδ0 : 0 < δ := zero_lt_one.trans hδ
  have hx : 0 ≤ xh := xh_nonneg I hI γbar hγbar hγbar1 δ hδ Sh hSh xh yh hopt
  obtain ⟨l, hlL, hlU, hlS⟩ := exists_level I hI γbar hγbar hγbar1 δ hδ i S hS
  obtain ⟨hlA, hnum⟩ := hSh i l hlL hlU ⟨S, hlS⟩
  have hA : 0 < V I i (Sh i l) := (zpow_pos hδ0 (l - 1)).trans_le hlA.1
  have hB : 0 < V I i S := (zpow_pos hδ0 (l - 1)).trans_le hlS.1
  have hγ := hI.γ_pos i
  have hγle : I.γ i ≤ γbar := hγbar.2 ⟨i, rfl⟩
  have hc := exponent_ge_one δ (I.γ i) γbar hδ hγ hγle hγbar1
  have hhat := rpow_lower_bound_hat δ (I.γ i) (V I i (Sh i l)) l hδ hγ hlA.1 hlA.2
  have hlevel := rpow_lower_bound_level δ (I.γ i) (V I i S) l hδ hγ hlS.1 hlS.2
  have hcoeff : V I i S ^ (I.γ i - 1) ≤ δ ^ γbar * V I i (Sh i l) ^ (I.γ i - 1) := by
    calc
      V I i S ^ (I.γ i - 1) = 1 * V I i S ^ (I.γ i - 1) := (one_mul _).symm
      _ ≤ (δ ^ γbar * δ ^ (-max (I.γ i - 1) 0) * δ ^ (-max (1 - I.γ i) 0)) *
          V I i S ^ (I.γ i - 1) :=
        mul_le_mul_of_nonneg_right hc.1 (Real.rpow_nonneg hB.le _)
      _ = δ ^ γbar * ((δ ^ (-max (1 - I.γ i) 0) * V I i S ^ (I.γ i - 1)) *
          δ ^ (-max (I.γ i - 1) 0)) := by ring
      _ ≤ δ ^ γbar * ((δ ^ l) ^ (I.γ i - 1) * δ ^ (-max (I.γ i - 1) 0)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hlevel (Real.rpow_nonneg hδ0.le _))
          (Real.rpow_nonneg hδ0.le _)
      _ ≤ δ ^ γbar * V I i (Sh i l) ^ (I.γ i - 1) :=
        mul_le_mul_of_nonneg_left hhat (Real.rpow_nonneg hδ0.le _)
  have hC : δ ^ (γbar + 1) = δ ^ γbar * δ := by
    rw [Real.rpow_add hδ0, Real.rpow_one]
  have hpositive :
      V I i S ^ (I.γ i - 1) * (∑ j ∈ S, I.r i j * I.v i j) ≤
        δ ^ (γbar + 1) * (V I i (Sh i l) ^ (I.γ i - 1) *
          (∑ j ∈ Sh i l, I.r i j * I.v i j)) := by
    calc
      _ ≤ (δ ^ γbar * V I i (Sh i l) ^ (I.γ i - 1)) *
          (∑ j ∈ S, I.r i j * I.v i j) :=
        mul_le_mul_of_nonneg_right hcoeff
          (Finset.sum_nonneg fun j _ => mul_nonneg (hI.r_nonneg i j) (hI.v_pos i j).le)
      _ ≤ (δ ^ γbar * V I i (Sh i l) ^ (I.γ i - 1)) *
          (δ * ∑ j ∈ Sh i l, I.r i j * I.v i j) :=
        mul_le_mul_of_nonneg_left (hnum S hlS)
          (mul_nonneg (Real.rpow_nonneg hδ0.le _) (Real.rpow_nonneg hA.le _))
      _ = _ := by rw [hC]; ring
  have hstep : δ ^ l = δ * δ ^ (l - 1) := by
    rw [← Real.rpow_intCast δ l, ← Real.rpow_intCast δ (l - 1)]
    calc
      δ ^ (l : ℝ) = δ ^ (1 + ((l - 1 : ℤ) : ℝ)) := by
        congr 1
        push_cast
        ring
      _ = δ * δ ^ ((l - 1 : ℤ) : ℝ) := by
        rw [Real.rpow_add hδ0, Real.rpow_one]
  have hAB : V I i (Sh i l) ≤ δ * V I i S := by
    calc
      _ ≤ δ ^ l := hlA.2
      _ = δ * δ ^ (l - 1) := hstep
      _ ≤ δ * V I i S := mul_le_mul_of_nonneg_left hlS.1 hδ0.le
  have hweight :
      δ ^ (γbar + 1) * nestWeight I i (Sh i l) ≤
        δ ^ (2 * γbar + 1) * nestWeight I i S := by
    unfold nestWeight
    calc
      _ ≤ δ ^ (γbar + 1) * (δ * V I i S) ^ I.γ i :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hA.le hAB hγ.le)
          (Real.rpow_nonneg hδ0.le _)
      _ = δ ^ (γbar + I.γ i + 1) * V I i S ^ I.γ i := by
        rw [Real.mul_rpow hδ0.le hB.le, ← mul_assoc, ← Real.rpow_add hδ0]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc.2 (Real.rpow_nonneg hB.le _)
  have hnegative := mul_le_mul_of_nonneg_right hweight hx
  have hfeas := hopt.1.2 i (Sh i l) (Or.inl ⟨l, hlL, hlU, rfl⟩)
  have hscaled := mul_le_mul_of_nonneg_left hfeas (Real.rpow_nonneg hδ0.le (γbar + 1))
  rw [← prep_weight_revenue I i S hB, ← prep_weight_revenue I i (Sh i l) hA] at hpositive
  nlinarith
