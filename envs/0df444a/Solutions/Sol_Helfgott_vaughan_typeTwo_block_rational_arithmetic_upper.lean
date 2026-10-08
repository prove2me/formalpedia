-- Prove2me | solution 1 for Helfgott.vaughan_typeTwo_block_rational_arithmetic_upper
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T13:37:53.769639+00:00
-- url     : https://prove2.me/submissions/dc167013-7b1b-47a5-bd68-36e63ad77223

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Module
import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_Helfgott_VaughanData
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Chebyshev

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Finset Real
open scoped BigOperators Classical

namespace Helfgott

noncomputable def centeredCircleRep (α : AddCircle (1 : ℝ)) : ℝ :=
  AddCircle.equivIco (1 : ℝ) (-(1/2 : ℝ)) α

lemma centeredCircleRep_coe (α : AddCircle (1 : ℝ)) :
    (centeredCircleRep α : AddCircle (1 : ℝ)) = α := AddCircle.coe_equivIco

lemma centeredCircleRep_abs_le (α : AddCircle (1 : ℝ)) : |centeredCircleRep α| ≤ 1/2 := by
  have hh := (AddCircle.equivIco (1 : ℝ) (-(1/2 : ℝ)) α).property
  change -(1/2 : ℝ) ≤ centeredCircleRep α ∧ centeredCircleRep α < -(1/2 : ℝ)+1 at hh
  exact abs_le.mpr ⟨hh.1,by linarith [hh.2]⟩

lemma centeredCircleRep_norm (α : AddCircle (1 : ℝ)) : ‖α‖ = |centeredCircleRep α| := by
  calc
    ‖α‖ = ‖(centeredCircleRep α : AddCircle (1 : ℝ))‖ := by rw [centeredCircleRep_coe]
    _ = _ := (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr (by
      simpa using centeredCircleRep_abs_le α)

noncomputable def circleReciprocalBucket (q : ℕ) (α : AddCircle (1 : ℝ)) : Bool × ℕ :=
  (decide (0 ≤ centeredCircleRep α),Nat.floor (2*(q : ℝ)*‖α‖))

lemma circleReciprocalBucket_mem (q : ℕ) (α : AddCircle (1 : ℝ)) :
    circleReciprocalBucket q α ∈ (Finset.univ : Finset Bool) ×ˢ Finset.range (q+1) := by
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_univ _,Finset.mem_range.mpr ?_⟩
  have hn : ‖α‖ ≤ (1/2 : ℝ) := by simpa using AddCircle.norm_le_half_period (1 : ℝ) (by norm_num) (x := α)
  have hbound : 2*(q : ℝ)*‖α‖ ≤ q := by nlinarith [show (0 : ℝ) ≤ q by positivity]
  have hh : Nat.floor (2*(q : ℝ)*‖α‖) ≤ q := by
    calc
      _ ≤ Nat.floor (q : ℝ) := Nat.floor_mono hbound
      _ = q := by simp
  change Nat.floor (2*(q : ℝ)*‖α‖) < q+1
  omega

lemma same_circleReciprocalBucket_close (q : ℕ) (hq : 0 < q)
    (α β : AddCircle (1 : ℝ))
    (he : circleReciprocalBucket q α = circleReciprocalBucket q β) :
    dist α β < 1/(2*(q : ℝ)) := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have hsign : decide (0 ≤ centeredCircleRep α) = decide (0 ≤ centeredCircleRep β) := congrArg Prod.fst he
  have hfloor : Nat.floor (2*(q : ℝ)*‖α‖) = Nat.floor (2*(q : ℝ)*‖β‖) := congrArg Prod.snd he
  have ha0 := Nat.floor_le (show (0 : ℝ) ≤ 2*(q : ℝ)*‖α‖ by positivity)
  have hb0 := Nat.floor_le (show (0 : ℝ) ≤ 2*(q : ℝ)*‖β‖ by positivity)
  have ha1 := Nat.lt_floor_add_one (2*(q : ℝ)*‖α‖)
  have hb1 := Nat.lt_floor_add_one (2*(q : ℝ)*‖β‖)
  rw [←hfloor] at hb0 hb1
  simp only [centeredCircleRep_norm] at ha0 ha1 hb0 hb1
  have hnum : (1/(2*(q : ℝ)))*(2*(q : ℝ)) = 1 := by field_simp
  have hab : |centeredCircleRep α-centeredCircleRep β| < 1/(2*(q : ℝ)) := by
    by_cases ha : 0 ≤ centeredCircleRep α
    · have hb : 0 ≤ centeredCircleRep β := by
        by_contra hh
        simp [ha,hh] at hsign
      simp only [abs_of_nonneg ha,abs_of_nonneg hb] at ha0 ha1 hb0 hb1
      apply abs_lt.mpr
      constructor <;> nlinarith
    · have hb : ¬0 ≤ centeredCircleRep β := by
        intro hh
        simp [ha,hh] at hsign
      simp only [abs_of_neg (lt_of_not_ge ha),abs_of_neg (lt_of_not_ge hb)] at ha0 ha1 hb0 hb1
      apply abs_lt.mpr
      constructor <;> nlinarith
  have hdist : dist α β ≤ |centeredCircleRep α-centeredCircleRep β| := by
    calc
      dist α β = dist (centeredCircleRep α : AddCircle (1 : ℝ)) (centeredCircleRep β : AddCircle (1 : ℝ)) := by rw [centeredCircleRep_coe,centeredCircleRep_coe]
      _ = ‖((centeredCircleRep α-centeredCircleRep β : ℝ) : AddCircle (1 : ℝ))‖ := by rw [dist_eq_norm,←QuotientAddGroup.mk_sub]
      _ ≤ _ := by simpa only [Real.norm_eq_abs] using (QuotientAddGroup.norm_mk_le_norm (m := centeredCircleRep α-centeredCircleRep β) (S := AddSubgroup.zmultiples (1 : ℝ)))
  exact hdist.trans_lt hab

lemma zero_split_reciprocal_sum (q : ℕ) (L C : ℝ) :
    (∑ k ∈ Finset.range (q+1),if k=0 then L else C/(k : ℝ)) = L+C*(harmonic q : ℝ) := by
  induction q with
  | zero => simp [harmonic_zero]
  | succ q ih =>
    rw [Finset.sum_range_succ,ih,harmonic_succ]
    simp only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false,Rat.cast_add,Rat.cast_inv,Rat.cast_natCast]
    ring

noncomputable def reciprocalBucketUpper (q : ℕ) (L : ℝ) (b : Bool × ℕ) : ℝ :=
  if b.2=0 then L else 4*(q : ℝ)/(b.2 : ℝ)

lemma circle_reciprocal_bound_by_bucket (q : ℕ) (hq : 0 < q) (L : ℝ) (hL : 0 ≤ L)
    (α : AddCircle (1 : ℝ)) :
    (if α=0 then L else min L (2/‖α‖)) ≤ reciprocalBucketUpper q L (circleReciprocalBucket q α) := by
  unfold reciprocalBucketUpper circleReciprocalBucket
  by_cases hk : Nat.floor (2*(q : ℝ)*‖α‖) = 0
  · rw [if_pos hk]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  · rw [if_neg hk]
    have hk0 : 0 < (Nat.floor (2*(q : ℝ)*‖α‖) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hα : α ≠ 0 := by intro he;subst α;simp at hk
    have hn : 0 < ‖α‖ := norm_pos_iff.mpr hα
    rw [if_neg hα]
    apply (min_le_right _ _).trans
    apply (div_le_div_iff₀ hn hk0).mpr
    have hh := Nat.floor_le (show (0 : ℝ) ≤ 2*(q : ℝ)*‖α‖ by positivity)
    nlinarith

theorem separated_circle_reciprocal_sum_bound {ι : Type*} (D : Finset ι)
    (γ : ι → AddCircle (1 : ℝ)) (q : ℕ) (hq : 0 < q) (L : ℝ) (hL : 0 ≤ L)
    (hsep : ∀ i ∈ D,∀ j ∈ D,i ≠ j → 1/(2*(q : ℝ)) ≤ dist (γ i) (γ j)) :
    (∑ i ∈ D,if γ i=0 then L else min L (2/‖γ i‖)) ≤ 2*L+8*(q : ℝ)*(harmonic q : ℝ) := by
  let e : ι → Bool × ℕ := fun i => circleReciprocalBucket q (γ i)
  have hinj : Set.InjOn e (D : Set ι) := by
    intro i hi j hj he
    by_contra hij
    exact (not_lt_of_ge (hsep i hi j hj hij)) (same_circleReciprocalBucket_close q hq (γ i) (γ j) he)
  have hsub : D.image e ⊆ (Finset.univ : Finset Bool) ×ˢ Finset.range (q+1) := by
    intro b hb
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb
    exact circleReciprocalBucket_mem q (γ i)
  have hnonneg (b : Bool × ℕ) : 0 ≤ reciprocalBucketUpper q L b := by
    unfold reciprocalBucketUpper
    split_ifs
    · exact hL
    · positivity
  calc
    _ ≤ ∑ i ∈ D,reciprocalBucketUpper q L (e i) := Finset.sum_le_sum (fun i hi => circle_reciprocal_bound_by_bucket q hq L hL (γ i))
    _ = ∑ b ∈ D.image e,reciprocalBucketUpper q L b := by
      rw [Finset.sum_image (fun i hi j hj he => hinj hi hj he)]
    _ ≤ ∑ b ∈ (Finset.univ : Finset Bool) ×ˢ Finset.range (q+1),reciprocalBucketUpper q L b :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => hnonneg b)
    _ = _ := by
      rw [Finset.sum_product]
      simp only [reciprocalBucketUpper,zero_split_reciprocal_sum]
      simp
      ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Real

namespace Helfgott

lemma rational_multiple_norm_lower (a q k : ℕ) (hq : 0 < q) (ha : Nat.Coprime a q)
    (hk : 0 < k) (hkq : k < q) :
    1/(q : ℝ) ≤ ‖k • ((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ))‖ := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have hnd : ¬q ∣ a*k := by
    intro hd
    have hh : q ∣ k := ha.symm.dvd_of_dvd_mul_left hd
    have he := Nat.le_of_dvd hk hh
    omega
  have hm0 : 0 < (a*k)%q := Nat.pos_of_ne_zero (by
    intro he
    exact hnd (Nat.dvd_of_mod_eq_zero he))
  have hmq : (a*k)%q < q := Nat.mod_lt _ hq
  have hmin : 1 ≤ min ((a*k)%q) (q-(a*k)%q) := by omega
  have he : k • ((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ)) =
      (((a*k : ℕ) : ℝ)/(q : ℝ) : AddCircle (1 : ℝ)) := by
    rw [←QuotientAddGroup.mk_nsmul]
    congr 1
    simp only [nsmul_eq_mul,Nat.cast_mul]
    ring
  rw [he]
  have hn := AddCircle.norm_div_natCast (p := (1 : ℝ)) (m := a*k) (n := q)
  simp only [mul_one,one_mul] at hn
  rw [hn]
  apply div_le_div_of_nonneg_right _ hq0.le
  exact_mod_cast hmin

theorem rational_approx_short_multiple_lower (a q k : ℕ) (hq : 0 < q)
    (ha : Nat.Coprime a q) (hk : 0 < k) (hkq : 2*k ≤ q)
    (α : AddCircle (1 : ℝ))
    (hα : ‖α-((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ))‖ ≤ 1/(q : ℝ)^2) :
    1/(2*(q : ℝ)) ≤ ‖k • α‖ := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have hkr : (2 : ℝ)*k ≤ q := by exact_mod_cast hkq
  let γ : AddCircle (1 : ℝ) := ((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ))
  have hrat : 1/(q : ℝ) ≤ ‖k • γ‖ := rational_multiple_norm_lower a q k hq ha hk (by omega)
  have herr : ‖k • γ-k • α‖ ≤ (k : ℝ)/(q : ℝ)^2 := by
    have hh : ‖k • (γ-α)‖ ≤ (k : ℝ)*‖γ-α‖ := norm_nsmul_le
    rw [smul_sub] at hh
    have hγα : ‖γ-α‖ ≤ 1/(q : ℝ)^2 := by
      rw [norm_sub_rev]
      exact hα
    exact hh.trans (by simpa only [div_eq_mul_inv,one_mul] using
      mul_le_mul_of_nonneg_left hγα (show (0 : ℝ) ≤ k by positivity))
  have he : (k : ℝ)/(q : ℝ)^2 ≤ 1/(2*(q : ℝ)) := by
    apply (div_le_iff₀ (pow_pos hq0 2)).mpr
    have hdiv : (q : ℝ)^2/(2*(q : ℝ)) = (q : ℝ)/2 := by field_simp
    rw [show 1/(2*(q : ℝ))*(q : ℝ)^2 = (q : ℝ)^2/(2*(q : ℝ)) by ring,hdiv]
    linarith
  have hn := norm_sub_norm_le (k • γ) (k • α)
  have hnum : 1/(q : ℝ) = 2*(1/(2*(q : ℝ))) := by field_simp
  linarith

theorem rational_approx_progression_separation (a q : ℕ) (hq : 0 < q)
    (ha : Nat.Coprime a q) (α : AddCircle (1 : ℝ))
    (hα : ‖α-((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ))‖ ≤ 1/(q : ℝ)^2)
    (m n : ℕ) (hmn : m < n) (hblock : 2*(n-m) ≤ q) :
    1/(2*(q : ℝ)) ≤ dist (m • α) (n • α) := by
  have hh := rational_approx_short_multiple_lower a q (n-m) hq ha (by omega) hblock α hα
  rw [dist_eq_norm,norm_sub_rev]
  have he : n • α-m • α = (n-m) • α := by
    have he : n • α = (n-m) • α+m • α := by
      rw [←add_nsmul,Nat.sub_add_cancel hmn.le]
    rw [he,add_sub_cancel_right]
  rw [he]
  exact hh

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Finset Real
open scoped BigOperators Classical

namespace Helfgott

theorem rational_approx_block_reciprocal_sum (a q : ℕ) (hq : 0 < q)
    (ha : Nat.Coprime a q) (α β : AddCircle (1 : ℝ))
    (hα : ‖α-((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ))‖ ≤ 1/(q : ℝ)^2)
    (A B : ℕ) (hblock : 2*(B-A) ≤ q) (L : ℝ) (hL : 0 ≤ L) :
    (∑ d ∈ Finset.Ico A B,if d • α-β=0 then L else min L (2/‖d • α-β‖)) ≤
      2*L+8*(q : ℝ)*(harmonic q : ℝ) := by
  apply separated_circle_reciprocal_sum_bound _ _ q hq L hL
  intro i hi j hj hij
  have hi' := Finset.mem_Ico.mp hi
  have hj' := Finset.mem_Ico.mp hj
  rw [dist_sub_right]
  by_cases hlt : i < j
  · exact rational_approx_progression_separation a q hq ha α hα i j hlt (by omega)
  · have hlt' : j < i := by omega
    rw [dist_comm]
    exact rational_approx_progression_separation a q hq ha α hα j i hlt' (by omega)

lemma sum_Ico_equal_blocks (f : ℕ → ℝ) (A H K : ℕ) :
    (∑ d ∈ Finset.Ico A (A+K*H),f d) =
      ∑ k ∈ Finset.range K,∑ d ∈ Finset.Ico (A+k*H) (A+(k+1)*H),f d := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ,←ih]
    have h1 : A ≤ A+K*H := Nat.le_add_right _ _
    have h2 : A+K*H ≤ A+(K+1)*H := Nat.add_le_add_left (Nat.mul_le_mul_right H (Nat.le_succ K)) A
    exact (Finset.sum_Ico_consecutive f h1 h2).symm

theorem rational_approx_reciprocal_sum (a q : ℕ) (hq : 2 ≤ q)
    (ha : Nat.Coprime a q) (α β : AddCircle (1 : ℝ))
    (hα : ‖α-((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ))‖ ≤ 1/(q : ℝ)^2)
    (A B : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (∑ d ∈ Finset.Ico A B,if d • α-β=0 then L else min L (2/‖d • α-β‖)) ≤
      (((B-A)/(q/2)+1 : ℕ) : ℝ)*(2*L+8*(q : ℝ)*(harmonic q : ℝ)) := by
  have hqpos : 0 < q := by omega
  have hH : 0 < q/2 := Nat.div_pos hq (by norm_num)
  let f : ℕ → ℝ := fun d => if d • α-β=0 then L else min L (2/‖d • α-β‖)
  have hf (d : ℕ) : 0 ≤ f d := by dsimp [f];split_ifs;exact hL;exact le_min hL (by positivity)
  have hT : 0 ≤ 2*L+8*(q : ℝ)*(harmonic q : ℝ) := by
    have hh : (0 : ℝ) ≤ (harmonic q : ℝ) := by
      unfold harmonic
      push_cast
      positivity
    positivity
  by_cases hAB : A ≤ B
  · let K := (B-A)/(q/2)+1
    have hcover : B ≤ A+K*(q/2) := by
      have he := Nat.mod_add_div (B-A) (q/2)
      have hm := Nat.mod_lt (B-A) hH
      dsimp [K]
      rw [Nat.add_mul,Nat.one_mul]
      rw [Nat.mul_comm (q/2) ((B-A)/(q/2))] at he
      omega
    calc
      _ ≤ ∑ d ∈ Finset.Ico A (A+K*(q/2)),f d :=
        Finset.sum_le_sum_of_subset_of_nonneg (by intro d hd;exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hd).1,(Finset.mem_Ico.mp hd).2.trans_le hcover⟩)
          (fun d _ _ => hf d)
      _ = ∑ k ∈ Finset.range K,∑ d ∈ Finset.Ico (A+k*(q/2)) (A+(k+1)*(q/2)),f d := sum_Ico_equal_blocks f A (q/2) K
      _ ≤ ∑ k ∈ Finset.range K,(2*L+8*(q : ℝ)*(harmonic q : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        apply rational_approx_block_reciprocal_sum a q hqpos ha α β hα _ _ _ L hL
        have he : A+(k+1)*(q/2)-(A+k*(q/2)) = q/2 := by
          rw [Nat.add_mul,Nat.one_mul]
          omega
        rw [he]
        simpa only [Nat.mul_comm] using Nat.div_mul_le_self q 2
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul];rfl
  · have hBA : B ≤ A := by omega
    simp only [Finset.Ico_eq_empty_of_le hBA,Finset.sum_empty]
    exact mul_nonneg (by positivity) hT

theorem rational_approx_reciprocal_sum_scaled (a q : ℕ) (hq : 2 ≤ q)
    (ha : Nat.Coprime a q) (α β : AddCircle (1 : ℝ))
    (hα : ‖α-((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ))‖ ≤ 1/(q : ℝ)^2)
    (A B : ℕ) (L C : ℝ) (hL : 0 ≤ L) (hC : 0 < C) :
    (∑ d ∈ Finset.Ico A B,if d • α-β=0 then L else min L (C/‖d • α-β‖)) ≤
      (((B-A)/(q/2)+1 : ℕ) : ℝ)*(2*L+4*C*(q : ℝ)*(harmonic q : ℝ)) := by
  have hh := mul_le_mul_of_nonneg_left
    (rational_approx_reciprocal_sum a q hq ha α β hα A B (2*L/C) (by positivity))
    (show (0 : ℝ) ≤ C/2 by positivity)
  have he (d : ℕ) : (C/2)*(if d • α-β=0 then 2*L/C else min (2*L/C) (2/‖d • α-β‖)) =
      if d • α-β=0 then L else min L (C/‖d • α-β‖) := by
    by_cases hz : d • α-β=0
    · rw [if_pos hz,if_pos hz]
      field_simp
    · rw [if_neg hz,if_neg hz,mul_min_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ C/2)]
      congr 1 <;> field_simp <;> ring
  rw [Finset.mul_sum] at hh
  simp_rw [he] at hh
  apply hh.trans_eq
  field_simp
  ring

theorem rational_approx_reciprocal_sum_bounds (a q : ℕ) (hq : 2 ≤ q)
    (ha : Nat.Coprime a q) (α β : AddCircle (1 : ℝ))
    (hα : ‖α-((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ))‖ ≤ 1/(q : ℝ)^2)
    (A B : ℕ) (L C : ℝ) (hL : 0 ≤ L) (hC : 0 < C) :
    ((∑ d ∈ Finset.Ico A B,if d • α-β=0 then L else min L (C/‖d • α-β‖)) ≤
      (((B-A)/(q/2)+1 : ℕ) : ℝ)*(2*L+4*C*(q : ℝ)*(harmonic q : ℝ))) ∧
    ((∑ d ∈ Finset.Ico A B,if d • α-β=0 then L else min L (C/‖d • α-β‖)) ≤
      (((B-A)/(q/2)+1 : ℕ) : ℝ)*(2*L+4*C*(q : ℝ)*(1+Real.log (q : ℝ)))) := by
  have hh := rational_approx_reciprocal_sum_scaled a q hq ha α β hα A B L C hL hC
  refine ⟨hh,hh.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_right
  exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log q) (by positivity)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Finset Real
open scoped BigOperators Classical

namespace Helfgott

lemma unit_geometric_interval_bound (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1)
    (A B : ℕ) :
    ‖∑ n ∈ Finset.Ico A B, z^n‖ ≤ min ((B-A : ℕ) : ℝ) (2/‖z-1‖) := by
  apply le_min
  · calc
      ‖∑ n ∈ Finset.Ico A B, z^n‖ ≤ ∑ n ∈ Finset.Ico A B, ‖z^n‖ := norm_sum_le _ _
      _ = ((B-A : ℕ) : ℝ) := by simp [norm_pow,hz]
  · by_cases hAB : A ≤ B
    · rw [geom_sum_Ico hz1 hAB,norm_div]
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      calc
        ‖z^B-z^A‖ ≤ ‖z^B‖+‖z^A‖ := norm_sub_le _ _
        _ = 2 := by simp [norm_pow,hz];norm_num
    · have hBA : B ≤ A := le_of_lt (lt_of_not_ge hAB)
      simp only [Finset.Ico_eq_empty_of_le hBA,Finset.sum_empty,norm_zero]
      positivity

lemma fourier_nat_power (α : AddCircle (1 : ℝ)) (n : ℕ) :
    fourier (n : ℤ) α = (fourier 1 α)^n := by
  induction n with
  | zero => simp only [Nat.cast_zero,fourier_zero,pow_zero]
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,fourier_add,ih,pow_succ]

lemma circle_chord_lower (α : AddCircle (1 : ℝ)) : 4*‖α‖ ≤ ‖fourier 1 α-1‖ := by
  let r : ℝ := AddCircle.equivIco (1 : ℝ) (-(1/2 : ℝ)) α
  have hr : r ∈ Set.Ico (-(1/2 : ℝ)) (-(1/2 : ℝ)+1) :=
    (AddCircle.equivIco (1 : ℝ) (-(1/2 : ℝ)) α).property
  have hrabs : |r| ≤ 1/2 := by
    apply abs_le.mpr
    constructor
    · exact hr.1
    · linarith [hr.2]
  have hrα : (r : AddCircle (1 : ℝ)) = α := AddCircle.coe_equivIco
  have hnorm : ‖α‖ = |r| := by
    rw [← hrα]
    exact (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr (by simpa using hrabs)
  have he : fourier 1 α = Complex.exp (Complex.I*((2*Real.pi*r : ℝ) : ℂ)) := by
    rw [← hrα,fourier_coe_apply]
    congr 1
    push_cast
    ring
  have hs := Real.mul_abs_le_abs_sin (x := Real.pi*r) (by
    rw [abs_mul,abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos])
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hs' : 2*|r| ≤ |Real.sin (Real.pi*r)| := by
    rw [abs_mul,abs_of_pos Real.pi_pos] at hs
    have hc : 2/Real.pi*(Real.pi*|r|) = 2*|r| := by field_simp
    rwa [hc] at hs
  rw [hnorm,he,Complex.norm_exp_I_mul_ofReal_sub_one]
  have hc : (2*Real.pi*r)/2 = Real.pi*r := by ring
  rw [hc,Real.norm_eq_abs,abs_mul]
  norm_num
  linarith

theorem fourier_interval_cancellation (α : AddCircle (1 : ℝ)) (hα : α ≠ 0) (A B : ℕ) :
    ‖∑ n ∈ Finset.Ico A B, fourier (n : ℤ) α‖ ≤
      min ((B-A : ℕ) : ℝ) (1/(2*‖α‖)) := by
  have hn : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hz : ‖fourier 1 α‖ = 1 := Circle.norm_coe _
  have hc := circle_chord_lower α
  have hz1 : fourier 1 α ≠ 1 := by
    intro h
    rw [h,sub_self,norm_zero] at hc
    linarith
  have hb := unit_geometric_interval_bound (fourier 1 α) hz hz1 A B
  simp only [← fourier_nat_power] at hb
  apply hb.trans
  apply min_le_min_left
  calc
    2/‖fourier 1 α-1‖ ≤ 2/(4*‖α‖) := by
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hc
    _ = 1/(2*‖α‖) := by field_simp;ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Finset
open scoped BigOperators Classical

namespace Helfgott

lemma weighted_range_prefix_norm_bound (f : ℕ → ℝ) (g : ℕ → ℂ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hg : ∀ k ≤ N, ‖∑ i ∈ Finset.range k, g i‖ ≤ C) :
    ‖∑ i ∈ Finset.range N, f i • g i‖ ≤
      (|f (N-1)|+∑ i ∈ Finset.range (N-1), |f (i+1)-f i|)*C := by
  rw [Finset.sum_range_by_parts]
  calc
    ‖f (N-1) • (∑ i ∈ Finset.range N,g i)-
        ∑ i ∈ Finset.range (N-1),(f (i+1)-f i) • (∑ j ∈ Finset.range (i+1),g j)‖ ≤
      ‖f (N-1) • (∑ i ∈ Finset.range N,g i)‖+
        ∑ i ∈ Finset.range (N-1),‖(f (i+1)-f i) • (∑ j ∈ Finset.range (i+1),g j)‖ :=
      (norm_sub_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ |f (N-1)| *C+∑ i ∈ Finset.range (N-1),|f (i+1)-f i| *C := by
      apply add_le_add
      · rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hg N le_rfl) (abs_nonneg _)
      · apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul,Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact hg (i+1) (by have := Finset.mem_range.mp hi;omega)
    _ = _ := by rw [← Finset.sum_mul];ring

lemma weighted_range_antitone_norm_bound (f : ℕ → ℝ) (g : ℕ → ℂ) (N : ℕ)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ k ≤ N, ‖∑ i ∈ Finset.range k,g i‖ ≤ C)
    (hf : ∀ i ≤ N, 0 ≤ f i)
    (hmono : ∀ i j, i ≤ j → j < N → f j ≤ f i) :
    ‖∑ i ∈ Finset.range N,f i • g i‖ ≤ f 0*C := by
  by_cases hN : N=0
  · simp only [hN,Finset.range_zero,Finset.sum_empty,norm_zero]
    exact mul_nonneg (hf 0 (by omega)) hC
  · have hlast : N-1 < N := by omega
    have hd : (∑ i ∈ Finset.range (N-1), |f (i+1)-f i|) = f 0-f (N-1) := by
      calc
        _ = ∑ i ∈ Finset.range (N-1), (f i-f (i+1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hm := hmono i (i+1) (by omega) (by have := Finset.mem_range.mp hi;omega)
          rw [abs_of_nonpos (sub_nonpos.mpr hm)]
          ring
        _ = _ := Finset.sum_range_sub' f (N-1)
    have hh := weighted_range_prefix_norm_bound f g N C hC hg
    rwa [abs_of_nonneg (hf (N-1) (by omega)),hd,add_sub_cancel] at hh

lemma sum_range_by_parts_tail (f : ℕ → ℝ) (g : ℕ → ℂ) (N : ℕ) :
    (∑ i ∈ Finset.range N,f i • g i) =
      f 0 • (∑ i ∈ Finset.range N,g i)+
      ∑ i ∈ Finset.range (N-1),(f (i+1)-f i) •
        ((∑ j ∈ Finset.range N,g j)-(∑ j ∈ Finset.range (i+1),g j)) := by
  rw [Finset.sum_range_by_parts]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib,← Finset.sum_smul,Finset.sum_range_sub,sub_smul]
  abel

lemma weighted_range_monotone_norm_bound (f : ℕ → ℝ) (g : ℕ → ℂ) (N : ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ k ≤ N, ‖(∑ i ∈ Finset.range N,g i)-(∑ i ∈ Finset.range k,g i)‖ ≤ C)
    (hf : ∀ i ≤ N, 0 ≤ f i)
    (hmono : ∀ i j, i ≤ j → j < N → f i ≤ f j) :
    ‖∑ i ∈ Finset.range N,f i • g i‖ ≤ f (N-1)*C := by
  rw [sum_range_by_parts_tail]
  calc
    _ ≤ ‖f 0 • (∑ i ∈ Finset.range N,g i)‖+
        ∑ i ∈ Finset.range (N-1),‖(f (i+1)-f i) •
          ((∑ j ∈ Finset.range N,g j)-(∑ j ∈ Finset.range (i+1),g j))‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ f 0*C+∑ i ∈ Finset.range (N-1),(f (i+1)-f i)*C := by
      apply add_le_add
      · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hf 0 (by omega))]
        exact mul_le_mul_of_nonneg_left (by simpa using hg 0 (by omega)) (hf 0 (by omega))
      · apply Finset.sum_le_sum
        intro i hi
        have hiN : i+1 < N := by have := Finset.mem_range.mp hi;omega
        have hd : 0 ≤ f (i+1)-f i := sub_nonneg.mpr (hmono i (i+1) (by omega) hiN)
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_left (hg (i+1) (by omega)) hd
    _ = _ := by rw [← Finset.sum_mul,Finset.sum_range_sub];ring

lemma sum_range_shift_Ico (g : ℕ → ℂ) (A k : ℕ) :
    (∑ i ∈ Finset.range k,g (A+i)) = ∑ i ∈ Finset.Ico A (A+k),g i := by
  simpa only [Finset.range_eq_Ico,zero_add,add_zero,Nat.add_comm k A] using Finset.sum_Ico_add g 0 k A

theorem monotone_weighted_fourier_interval_bound (f : ℕ → ℝ)
    (α : AddCircle (1 : ℝ)) (hα : α ≠ 0) (A B : ℕ)
    (hf : ∀ i, 0 ≤ f i)
    (hmono : ∀ i j, A ≤ i → i ≤ j → j < B → f i ≤ f j) :
    ‖∑ i ∈ Finset.Ico A B,f i • fourier (i : ℤ) α‖ ≤ f (B-1)/(2*‖α‖) := by
  have hC : 0 ≤ 1/(2*‖α‖) := by positivity
  by_cases hAB : A < B
  · have hshift : A+(B-A) = B := by omega
    have hg : ∀ k ≤ B-A,
        ‖(∑ i ∈ Finset.range (B-A),fourier ((A+i : ℕ) : ℤ) α)-
          (∑ i ∈ Finset.range k,fourier ((A+i : ℕ) : ℤ) α)‖ ≤ 1/(2*‖α‖) := by
      intro k hk
      rw [sum_range_shift_Ico (fun i => fourier (i : ℤ) α) A (B-A),sum_range_shift_Ico (fun i => fourier (i : ℤ) α) A k,hshift]
      have hsum := Finset.sum_Ico_consecutive (fun i => fourier (i : ℤ) α)
        (show A ≤ A+k by omega) (show A+k ≤ B by omega)
      rw [← hsum,add_sub_cancel_left]
      exact (fourier_interval_cancellation α hα (A+k) B).trans (min_le_right _ _)
    have hh := weighted_range_monotone_norm_bound (fun i => f (A+i))
      (fun i => fourier ((A+i : ℕ) : ℤ) α) (B-A) (1/(2*‖α‖)) hC hg
      (fun i _ => hf _) (by
        intro i j hij hj
        exact hmono (A+i) (A+j) (by omega) (by omega) (by omega))
    rw [sum_range_shift_Ico (fun i => f i • fourier (i : ℤ) α),hshift] at hh
    have hlast : A+(B-A-1) = B-1 := by omega
    simpa only [hlast,div_eq_mul_inv,one_mul] using hh
  · have hBA : B ≤ A := by omega
    simp only [Finset.Ico_eq_empty_of_le hBA,Finset.sum_empty,norm_zero]
    exact div_nonneg (hf _) (by positivity)

theorem antitone_weighted_fourier_interval_bound (f : ℕ → ℝ)
    (α : AddCircle (1 : ℝ)) (hα : α ≠ 0) (A B : ℕ)
    (hf : ∀ i, 0 ≤ f i)
    (hmono : ∀ i j, A ≤ i → i ≤ j → j < B → f j ≤ f i) :
    ‖∑ i ∈ Finset.Ico A B,f i • fourier (i : ℤ) α‖ ≤ f A/(2*‖α‖) := by
  have hC : 0 ≤ 1/(2*‖α‖) := by positivity
  by_cases hAB : A ≤ B
  · have hshift : A+(B-A) = B := by omega
    have hg : ∀ k ≤ B-A,
        ‖∑ i ∈ Finset.range k,fourier ((A+i : ℕ) : ℤ) α‖ ≤ 1/(2*‖α‖) := by
      intro k hk
      rw [sum_range_shift_Ico (fun i => fourier (i : ℤ) α) A k]
      exact (fourier_interval_cancellation α hα A (A+k)).trans (min_le_right _ _)
    have hh := weighted_range_antitone_norm_bound (fun i => f (A+i))
      (fun i => fourier ((A+i : ℕ) : ℤ) α) (B-A) (1/(2*‖α‖)) hC hg
      (fun i _ => hf _) (by
        intro i j hij hj
        exact hmono (A+i) (A+j) (by omega) (by omega) (by omega))
    rw [sum_range_shift_Ico (fun i => f i • fourier (i : ℤ) α),hshift] at hh
    simpa only [add_zero,div_eq_mul_inv,one_mul] using hh
  · have hBA : B ≤ A := by omega
    simp only [Finset.Ico_eq_empty_of_le hBA,Finset.sum_empty,norm_zero]
    exact div_nonneg (hf _) (by positivity)

end Helfgott
end

section
open MeasureTheory Set
open scoped Interval

namespace Helfgott

lemma etaTwo_nonneg (t : ℝ) : 0 ≤ etaTwo t := by
  unfold etaTwo
  split_ifs <;> positivity

lemma etaTwo_le (t : ℝ) : etaTwo t ≤ 4 * Real.log 2 := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  unfold etaTwo
  split_ifs
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact max_le (sub_le_self _ (abs_nonneg _)) hlog
  · positivity

lemma etaTwo_eq_zero_of_not_mem (t : ℝ) (ht : t ∉ Set.Icc (1/4 : ℝ) 1) :
    etaTwo t = 0 := by
  by_cases hpos : 0 < t
  · unfold etaTwo
    rw [if_pos hpos]
    have htwopos : 0 < 2*t := by positivity
    have hm : Real.log 2 - |Real.log (2*t)| ≤ 0 := by
      rcases (not_and_or.mp ht) with hlo | hhi
      · have hlt : 2*t ≤ (1/2 : ℝ) := by push_neg at hlo; linarith
        have hlog := Real.log_le_log htwopos hlt
        have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by
          rw [one_div, Real.log_inv]
        rw [hhalf] at hlog
        linarith [neg_le_abs (Real.log (2*t))]
      · have hlt : (2 : ℝ) ≤ 2*t := by push_neg at hhi; linarith
        have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hlt
        linarith [le_abs_self (Real.log (2*t))]
    rw [max_eq_right hm, mul_zero]
  · simp [etaTwo,hpos]

lemma etaTwo_eq_lower (t : ℝ) (ht : t ∈ Set.Icc (1/4 : ℝ) (1/2)) :
    etaTwo t = 4 * Real.log (4*t) := by
  have hpos : 0 < t := by linarith [ht.1]
  have hprod : 0 < 2*t := by positivity
  have hlogneg : Real.log (2*t) ≤ 0 := Real.log_nonpos (le_of_lt hprod) (by linarith [ht.2])
  have hsum : Real.log 2 + Real.log (2*t) = Real.log (4*t) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hprod)]
    congr 1; ring
  have hn : 0 ≤ Real.log (4*t) := Real.log_nonneg (by linarith [ht.1])
  unfold etaTwo
  rw [if_pos hpos, abs_of_nonpos hlogneg, sub_neg_eq_add, hsum, max_eq_left hn]

lemma etaTwo_eq_upper (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) :
    etaTwo t = -4 * Real.log t := by
  have hpos : 0 < t := by linarith [ht.1]
  have hlogpos : 0 ≤ Real.log (2*t) := Real.log_nonneg (by linarith [ht.1])
  have hlogneg : Real.log t ≤ 0 := Real.log_nonpos (le_of_lt hpos) ht.2
  have hlog : Real.log (2*t) = Real.log 2 + Real.log t :=
    Real.log_mul (by norm_num) (ne_of_gt hpos)
  unfold etaTwo
  rw [if_pos hpos, abs_of_nonneg hlogpos, hlog]
  have hm : Real.log 2 - (Real.log 2 + Real.log t) = -Real.log t := by ring
  rw [hm, max_eq_left (neg_nonneg.mpr hlogneg)]
  ring

lemma etaTwo_continuousOn_pos : ContinuousOn etaTwo (Set.Ioi (0 : ℝ)) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have hg : ContinuousAt (fun s : ℝ => 4 * max (Real.log 2 - |Real.log (2*s)|) 0) t := by
    have hpos : 0 < t := ht
    have hn : 2*t ≠ 0 := by positivity
    fun_prop
  apply hg.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  simp only [etaTwo, if_pos (show 0 < x from hx)]

theorem etaTwo_mass_interval : (∫ t in (1/4 : ℝ)..1, etaTwo t) = 1 := by
  have hint (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : IntervalIntegrable etaTwo volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply etaTwo_continuousOn_pos.mono
    intro t ht
    exact lt_of_lt_of_le (lt_min ha hb) ht.1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint (1/4) (1/2) (by norm_num) (by norm_num))
    (hint (1/2) 1 (by norm_num) (by norm_num))]
  have hlo : (∫ t in (1/4 : ℝ)..(1/2), etaTwo t) =
      ∫ t in (1/4 : ℝ)..(1/2), 4 * (Real.log 4 + Real.log t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hmem : t ∈ Set.Icc (1/4 : ℝ) (1/2) := by
      have h := Set.uIcc_of_le (by norm_num : (1/4 : ℝ) ≤ 1/2)
      rw [h] at ht
      exact ht
    rw [etaTwo_eq_lower t hmem, Real.log_mul (by norm_num) (by linarith [hmem.1] : t ≠ 0)]
  have hhi : (∫ t in (1/2 : ℝ)..1, etaTwo t) = ∫ t in (1/2 : ℝ)..1, -4 * Real.log t := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply etaTwo_eq_upper
    rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
    exact ht
  rw [hlo,hhi,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (intervalIntegrable_const) (intervalIntegral.intervalIntegrable_log'),
    intervalIntegral.integral_const,integral_log,integral_log]
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  have hquarter : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by rw [one_div,Real.log_inv,h4]
  rw [h4,hhalf,hquarter,Real.log_one]
  norm_num
  ring

lemma etaTwo_continuous : Continuous etaTwo := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : 0 < t
  · exact (etaTwo_continuousOn_pos t ht).continuousAt (Ioi_mem_nhds ht)
  · have hlo : t < (1/4 : ℝ) := by linarith
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlo] with x hx
    apply etaTwo_eq_zero_of_not_mem
    intro h; exact (not_lt_of_ge h.1) hx

lemma etaTwo_hasCompactSupport : HasCompactSupport etaTwo := by
  apply HasCompactSupport.intro (K := Set.Icc (1/4 : ℝ) 1) isCompact_Icc
  exact etaTwo_eq_zero_of_not_mem

lemma etaTwo_integrable : Integrable etaTwo :=
  etaTwo_continuous.integrable_of_hasCompactSupport etaTwo_hasCompactSupport

theorem etaTwo_mass : (∫ t : ℝ, etaTwo t) = 1 := by
  have hind : (Set.Icc (1/4 : ℝ) 1).indicator etaTwo = etaTwo := by
    funext t
    by_cases ht : t ∈ Set.Icc (1/4 : ℝ) 1
    · exact Set.indicator_of_mem ht etaTwo
    · rw [Set.indicator_of_notMem ht,etaTwo_eq_zero_of_not_mem t ht]
  calc
    (∫ t : ℝ, etaTwo t) = ∫ t : ℝ, (Set.Icc (1/4 : ℝ) 1).indicator etaTwo t := by rw [hind]
    _ = ∫ t in Set.Icc (1/4 : ℝ) 1, etaTwo t := integral_indicator measurableSet_Icc
    _ = ∫ t in (1/4 : ℝ)..1, etaTwo t := by
      rw [intervalIntegral.integral_of_le (by norm_num),integral_Icc_eq_integral_Ioc]
    _ = 1 := etaTwo_mass_interval

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Finset Real
open scoped BigOperators Classical

namespace Helfgott

lemma etaTwo_monotone_lower (s t : ℝ) (hst : s ≤ t) (ht : t ≤ 1/2) :
    etaTwo s ≤ etaTwo t := by
  by_cases hs : 0 < s
  · have ht0 : 0 < t := hs.trans_le hst
    have hls : Real.log (2*s) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
    have hlt : Real.log (2*t) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
    have hlog : Real.log (2*s) ≤ Real.log (2*t) := Real.log_le_log (by positivity) (by linarith)
    simp only [etaTwo,if_pos hs,if_pos ht0,abs_of_nonpos hls,abs_of_nonpos hlt]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply max_le_max_right
    linarith
  · simpa [etaTwo,hs] using etaTwo_nonneg t

lemma etaTwo_antitone_upper (s t : ℝ) (hst : s ≤ t) (hs : 1/2 ≤ s) :
    etaTwo t ≤ etaTwo s := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := hs0.trans_le hst
  have hls : 0 ≤ Real.log (2*s) := Real.log_nonneg (by linarith)
  have hlt : 0 ≤ Real.log (2*t) := Real.log_nonneg (by linarith)
  have hlog : Real.log (2*s) ≤ Real.log (2*t) := Real.log_le_log (by positivity) (by linarith)
  simp only [etaTwo,if_pos hs0,if_pos ht0,abs_of_nonneg hls,abs_of_nonneg hlt]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply max_le_max_right
  linarith

theorem etaTwo_fourier_interval_cancellation (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) (hα : α ≠ 0) (A B : ℕ) :
    ‖∑ n ∈ Finset.Ico A B,(etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α‖ ≤
      4*Real.log 2/‖α‖ := by
  have hn : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  by_cases hAB : A ≤ B
  · let K := min B (max A (Nat.floor (y/2)+1))
    have hAK : A ≤ K := le_min hAB (le_max_left _ _)
    have hKB : K ≤ B := min_le_left _ _
    have hl := monotone_weighted_fourier_interval_bound (fun n => etaTwo ((n : ℝ)/y)) α hα A K
      (fun n => etaTwo_nonneg _) (by
        intro i j hi hij hj
        apply etaTwo_monotone_lower
        · exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hy.le
        · have hjf : j ≤ Nat.floor (y/2) := by dsimp [K] at hj;omega
          have hjcast : (j : ℝ) ≤ (Nat.floor (y/2) : ℝ) := by exact_mod_cast hjf
          have hjreal : (j : ℝ) ≤ y/2 := hjcast.trans (Nat.floor_le (by positivity))
          apply (div_le_iff₀ hy).mpr
          linarith)
    have hu := antitone_weighted_fourier_interval_bound (fun n => etaTwo ((n : ℝ)/y)) α hα K B
      (fun n => etaTwo_nonneg _) (by
        intro i j hi hij hj
        apply etaTwo_antitone_upper
        · exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hy.le
        · have hfi : Nat.floor (y/2)+1 ≤ i := by dsimp [K] at hi;omega
          have hir : y/2 ≤ (i : ℝ) := by
            have hh := Nat.lt_floor_add_one (y/2)
            exact hh.le.trans (by exact_mod_cast hfi)
          apply (le_div_iff₀ hy).mpr
          linarith)
    have hs := Finset.sum_Ico_consecutive
      (fun n => (etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α) hAK hKB
    rw [← hs]
    have hl' : ‖∑ n ∈ Finset.Ico A K,(etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α‖ ≤
        4*Real.log 2/(2*‖α‖) := by
      simp only [Complex.real_smul] at hl
      exact hl.trans (div_le_div_of_nonneg_right (etaTwo_le _) (by positivity))
    have hu' : ‖∑ n ∈ Finset.Ico K B,(etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α‖ ≤
        4*Real.log 2/(2*‖α‖) := by
      simp only [Complex.real_smul] at hu
      exact hu.trans (div_le_div_of_nonneg_right (etaTwo_le _) (by positivity))
    calc
      _ ≤ ‖∑ n ∈ Finset.Ico A K,(etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α‖+
        ‖∑ n ∈ Finset.Ico K B,(etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α‖ := norm_add_le _ _
      _ ≤ 4*Real.log 2/(2*‖α‖)+4*Real.log 2/(2*‖α‖) := add_le_add hl' hu'
      _ = _ := by field_simp;ring
  · have hBA : B ≤ A := by omega
    simp only [Finset.Ico_eq_empty_of_le hBA,Finset.sum_empty,norm_zero]
    positivity

theorem etaTwo_log_fourier_cancellation (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) (hα : α ≠ 0) (B : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 B,
      ((Real.log (n : ℝ)*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)*fourier (n : ℤ) α‖ ≤
      (4*Real.log 2)*max (Real.log (B : ℝ)) 0/‖α‖ := by
  let f : ℕ → ℝ := fun i => max (Real.log ((1+i : ℕ) : ℝ)) 0
  let g : ℕ → ℂ := fun i => (etaTwo (((1+i : ℕ) : ℝ)/y) : ℂ)*fourier ((1+i : ℕ) : ℤ) α
  have hC : 0 ≤ 4*Real.log 2/‖α‖ := by positivity
  have hg : ∀ k ≤ B,
      ‖(∑ i ∈ Finset.range B,g i)-(∑ i ∈ Finset.range k,g i)‖ ≤ 4*Real.log 2/‖α‖ := by
    intro k hk
    dsimp only [g]
    rw [sum_range_shift_Ico (fun n => (etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α) 1 B,
      sum_range_shift_Ico (fun n => (etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α) 1 k]
    have hs := Finset.sum_Ico_consecutive
      (fun n => (etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α)
      (show 1 ≤ 1+k by omega) (show 1+k ≤ 1+B by omega)
    rw [← hs,add_sub_cancel_left]
    exact etaTwo_fourier_interval_cancellation y hy α hα _ _
  have hf : ∀ i ≤ B,0 ≤ f i := by intro i hi;exact le_max_right _ _
  have hm : ∀ i j,i ≤ j → j < B → f i ≤ f j := by
    intro i j hij hj
    apply max_le_max_right
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_left hij 1)
  have hh := weighted_range_monotone_norm_bound f g B (4*Real.log 2/‖α‖) hC hg hf hm
  by_cases hB : B=0
  · simp [hB]
  · have hlast : 1+(B-1) = B := by omega
    have heq : (∑ i ∈ Finset.range B,f i • g i) =
        ∑ n ∈ Finset.Icc 1 B,
          ((Real.log (n : ℝ)*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)*fourier (n : ℤ) α := by
      have hf' : ∀ i, f i = Real.log ((1+i : ℕ) : ℝ) := by
        intro i
        apply max_eq_left
        exact Real.log_nonneg (by
          have hi : (1 : ℕ) ≤ 1+i := by omega
          exact_mod_cast hi)
      simp only [hf',g,Complex.real_smul,← mul_assoc,← Complex.ofReal_mul]
      rw [sum_range_shift_Ico (fun n => ((Real.log (n : ℝ)*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)*
        fourier (n : ℤ) α)]
      rw [Nat.add_comm 1 B,Finset.Ico_add_one_right_eq_Icc]
    rw [heq] at hh
    dsimp only [f] at hh
    rw [hlast] at hh
    convert hh using 1 <;> ring

theorem etaTwo_compact_fourier_cancellation (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) (hα : α ≠ 0) (A B : ℕ) :
    (‖∑ n ∈ Finset.Ico A B,(etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α‖ ≤
      4*Real.log 2/‖α‖) ∧
    (‖∑ n ∈ Finset.Icc 1 B,
      ((Real.log (n : ℝ)*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)*fourier (n : ℤ) α‖ ≤
      (4*Real.log 2)*max (Real.log (B : ℝ)) 0/‖α‖) :=
  ⟨etaTwo_fourier_interval_cancellation y hy α hα A B,etaTwo_log_fourier_cancellation y hy α hα B⟩

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Finset
open scoped BigOperators Classical ComplexConjugate

namespace Helfgott

lemma finite_complex_cauchy_square {ι : Type*} (s : Finset ι) (a F : ι → ℂ) :
    ‖∑ d ∈ s,a d*F d‖^2 ≤ (∑ d ∈ s,‖a d‖^2)*(∑ d ∈ s,‖F d‖^2) := by
  have ht : ‖∑ d ∈ s,a d*F d‖ ≤ ∑ d ∈ s,‖a d‖*‖F d‖ := by
    simpa only [norm_mul] using norm_sum_le s (fun d => a d*F d)
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans (sum_mul_sq_le_sq_mul_sq s (fun d => ‖a d‖) (fun d => ‖F d‖))

lemma finite_correlation_energy_identity {ι κ : Type*} (D : Finset ι) (M : Finset κ)
    (b : κ → ℂ) (K : ι → κ → ℂ) :
    ((∑ d ∈ D,‖∑ m ∈ M,b m*K d m‖^2 : ℝ) : ℂ) =
      ∑ m ∈ M,∑ n ∈ M,b m*conj (b n)*(∑ d ∈ D,K d m*conj (K d n)) := by
  have hz (z : ℂ) : ((‖z‖^2 : ℝ) : ℂ) = z*conj z := by
    rw [Complex.sq_norm,Complex.mul_conj]
  simp_rw [Complex.ofReal_sum,hz,map_sum,Finset.sum_mul,Finset.mul_sum,map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro d hd
  ring

lemma finite_correlation_energy_bound {ι κ : Type*} (D : Finset ι) (M : Finset κ)
    (b : κ → ℂ) (K : ι → κ → ℂ) (C : κ → κ → ℝ)
    (hC : ∀ m ∈ M,∀ n ∈ M,‖∑ d ∈ D,K d m*conj (K d n)‖ ≤ C m n) :
    (∑ d ∈ D,‖∑ m ∈ M,b m*K d m‖^2) ≤
      ∑ m ∈ M,∑ n ∈ M,‖b m‖*‖b n‖*C m n := by
  have h0 : 0 ≤ ∑ d ∈ D,‖∑ m ∈ M,b m*K d m‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    _ = ‖((∑ d ∈ D,‖∑ m ∈ M,b m*K d m‖^2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h0]
    _ = ‖∑ m ∈ M,∑ n ∈ M,b m*conj (b n)*(∑ d ∈ D,K d m*conj (K d n))‖ := by
      rw [finite_correlation_energy_identity]
    _ ≤ ∑ m ∈ M,∑ n ∈ M,‖b m*conj (b n)*(∑ d ∈ D,K d m*conj (K d n))‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m hm => norm_sum_le _ _))
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      simp only [norm_mul,Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (hC m hm n hn) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

lemma finite_bilinear_correlation_bound {ι κ : Type*} (D : Finset ι) (M : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (K : ι → κ → ℂ) (C : κ → κ → ℝ)
    (hC : ∀ m ∈ M,∀ n ∈ M,‖∑ d ∈ D,K d m*conj (K d n)‖ ≤ C m n) :
    ‖∑ d ∈ D,∑ m ∈ M,a d*b m*K d m‖^2 ≤
      (∑ d ∈ D,‖a d‖^2)*(∑ m ∈ M,∑ n ∈ M,‖b m‖*‖b n‖*C m n) := by
  have hc := finite_complex_cauchy_square D a (fun d => ∑ m ∈ M,b m*K d m)
  have he : (∑ d ∈ D,a d*(∑ m ∈ M,b m*K d m)) =
      ∑ d ∈ D,∑ m ∈ M,a d*b m*K d m := by
    simp_rw [Finset.mul_sum,mul_assoc]
  rw [he] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left (finite_correlation_energy_bound D M b K C hC)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

lemma fourier_product_correlation (α : AddCircle (1 : ℝ)) (d m n : ℕ) :
    fourier ((d*m : ℕ) : ℤ) α*conj (fourier ((d*n : ℕ) : ℤ) α) =
      fourier (d : ℤ) (((m : ℤ)-(n : ℤ)) • α) := by
  rw [←fourier_neg,←fourier_add]
  have he : ((d*m : ℕ) : ℤ)+ -((d*n : ℕ) : ℤ) = (d : ℤ)*((m : ℤ)-(n : ℤ)) := by
    push_cast
    ring
  rw [he]
  simp only [fourier_apply,smul_smul]

theorem rectangular_bilinear_fourier_cancellation (α : AddCircle (1 : ℝ))
    (A B : ℕ) (M : Finset ℕ) (a b : ℕ → ℂ) :
    ‖∑ d ∈ Finset.Ico A B,∑ m ∈ M,a d*b m*fourier ((d*m : ℕ) : ℤ) α‖^2 ≤
      (∑ d ∈ Finset.Ico A B,‖a d‖^2)*
      (∑ m ∈ M,∑ n ∈ M,‖b m‖*‖b n‖*
        (if ((m : ℤ)-(n : ℤ)) • α = 0 then ((B-A : ℕ) : ℝ)
         else min ((B-A : ℕ) : ℝ) (1/(2*‖((m : ℤ)-(n : ℤ)) • α‖)))) := by
  apply finite_bilinear_correlation_bound
  intro m hm n hn
  simp_rw [fourier_product_correlation]
  by_cases hz : ((m : ℤ)-(n : ℤ)) • α = 0
  · simp [hz,fourier_eval_zero]
  · rw [if_neg hz]
    exact fourier_interval_cancellation _ hz A B

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Real
open scoped BigOperators Classical ComplexConjugate

namespace Helfgott

lemma monotone_weighted_interval_norm_bound (f : ℕ → ℝ) (g : ℕ → ℂ)
    (A B : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ P Q,‖∑ i ∈ Finset.Ico P Q,g i‖ ≤ C)
    (hf : ∀ i,0 ≤ f i)
    (hmono : ∀ i j,A ≤ i → i ≤ j → j < B → f i ≤ f j) :
    ‖∑ i ∈ Finset.Ico A B,f i • g i‖ ≤ f (B-1)*C := by
  by_cases hAB : A < B
  · have hshift : A+(B-A) = B := by omega
    have hhg : ∀ k ≤ B-A,
        ‖(∑ i ∈ Finset.range (B-A),g (A+i))-(∑ i ∈ Finset.range k,g (A+i))‖ ≤ C := by
      intro k hk
      rw [sum_range_shift_Ico g A (B-A),sum_range_shift_Ico g A k,hshift]
      have hs := Finset.sum_Ico_consecutive g (show A ≤ A+k by omega) (show A+k ≤ B by omega)
      rw [←hs,add_sub_cancel_left]
      exact hg (A+k) B
    have hh := weighted_range_monotone_norm_bound (fun i => f (A+i))
      (fun i => g (A+i)) (B-A) C hC hhg (fun i _ => hf _) (by
        intro i j hij hj
        exact hmono (A+i) (A+j) (by omega) (by omega) (by omega))
    rw [sum_range_shift_Ico (fun i => f i • g i),hshift] at hh
    have hlast : A+(B-A-1) = B-1 := by omega
    simpa only [hlast] using hh
  · have hBA : B ≤ A := by omega
    simp only [Finset.Ico_eq_empty_of_le hBA,Finset.sum_empty,norm_zero]
    exact mul_nonneg (hf _) hC

lemma antitone_weighted_interval_norm_bound (f : ℕ → ℝ) (g : ℕ → ℂ)
    (A B : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ P Q,‖∑ i ∈ Finset.Ico P Q,g i‖ ≤ C)
    (hf : ∀ i,0 ≤ f i)
    (hmono : ∀ i j,A ≤ i → i ≤ j → j < B → f j ≤ f i) :
    ‖∑ i ∈ Finset.Ico A B,f i • g i‖ ≤ f A*C := by
  by_cases hAB : A ≤ B
  · have hshift : A+(B-A) = B := by omega
    have hhg : ∀ k ≤ B-A,‖∑ i ∈ Finset.range k,g (A+i)‖ ≤ C := by
      intro k hk
      rw [sum_range_shift_Ico g A k]
      exact hg A (A+k)
    have hh := weighted_range_antitone_norm_bound (fun i => f (A+i))
      (fun i => g (A+i)) (B-A) C hC hhg (fun i _ => hf _) (by
        intro i j hij hj
        exact hmono (A+i) (A+j) (by omega) (by omega) (by omega))
    rw [sum_range_shift_Ico (fun i => f i • g i),hshift] at hh
    simpa only [add_zero] using hh
  · have hBA : B ≤ A := by omega
    simp only [Finset.Ico_eq_empty_of_le hBA,Finset.sum_empty,norm_zero]
    exact mul_nonneg (hf _) hC

theorem etaTwo_pair_fourier_interval_cancellation (y z : ℝ) (hy : 0 < y) (hz : 0 < z)
    (α : AddCircle (1 : ℝ)) (hα : α ≠ 0) (A B : ℕ) :
    ‖∑ d ∈ Finset.Ico A B,((etaTwo ((d : ℝ)/y)*etaTwo ((d : ℝ)/z) : ℝ) : ℂ)*
      fourier (d : ℤ) α‖ ≤ 2*(4*Real.log 2)^2/‖α‖ := by
  have hn : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  let g : ℕ → ℂ := fun d => (etaTwo ((d : ℝ)/z) : ℂ)*fourier (d : ℤ) α
  have hg : ∀ P Q,‖∑ d ∈ Finset.Ico P Q,g d‖ ≤ 4*Real.log 2/‖α‖ :=
    fun P Q => etaTwo_fourier_interval_cancellation z hz α hα P Q
  have hC : 0 ≤ 4*Real.log 2/‖α‖ := by positivity
  by_cases hAB : A ≤ B
  · let K := min B (max A (Nat.floor (y/2)+1))
    have hAK : A ≤ K := le_min hAB (le_max_left _ _)
    have hKB : K ≤ B := min_le_left _ _
    have hl := monotone_weighted_interval_norm_bound (fun d => etaTwo ((d : ℝ)/y)) g A K _ hC hg
      (fun d => etaTwo_nonneg _) (by
        intro i j hi hij hj
        apply etaTwo_monotone_lower
        · exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hy.le
        · have hjf : j ≤ Nat.floor (y/2) := by dsimp [K] at hj;omega
          have hjcast : (j : ℝ) ≤ (Nat.floor (y/2) : ℝ) := by exact_mod_cast hjf
          have hjreal : (j : ℝ) ≤ y/2 := hjcast.trans (Nat.floor_le (by positivity))
          apply (div_le_iff₀ hy).mpr
          linarith)
    have hu := antitone_weighted_interval_norm_bound (fun d => etaTwo ((d : ℝ)/y)) g K B _ hC hg
      (fun d => etaTwo_nonneg _) (by
        intro i j hi hij hj
        apply etaTwo_antitone_upper
        · exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hy.le
        · have hfi : Nat.floor (y/2)+1 ≤ i := by dsimp [K] at hi;omega
          have hir : y/2 ≤ (i : ℝ) := (Nat.lt_floor_add_one (y/2)).le.trans (by exact_mod_cast hfi)
          apply (le_div_iff₀ hy).mpr
          linarith)
    have hs := Finset.sum_Ico_consecutive (fun d => etaTwo ((d : ℝ)/y) • g d) hAK hKB
    have he (P Q : ℕ) : (∑ d ∈ Finset.Ico P Q,etaTwo ((d : ℝ)/y) • g d) =
        ∑ d ∈ Finset.Ico P Q,((etaTwo ((d : ℝ)/y)*etaTwo ((d : ℝ)/z) : ℝ) : ℂ)*fourier (d : ℤ) α := by
      simp only [g,Complex.real_smul,←mul_assoc,←Complex.ofReal_mul]
    have hl' := hl.trans (mul_le_mul_of_nonneg_right (etaTwo_le _) hC)
    have hu' := hu.trans (mul_le_mul_of_nonneg_right (etaTwo_le _) hC)
    rw [←he A B,←hs]
    calc
      _ ≤ ‖∑ d ∈ Finset.Ico A K,etaTwo ((d : ℝ)/y) • g d‖+
        ‖∑ d ∈ Finset.Ico K B,etaTwo ((d : ℝ)/y) • g d‖ := norm_add_le _ _
      _ ≤ (4*Real.log 2)*(4*Real.log 2/‖α‖)+(4*Real.log 2)*(4*Real.log 2/‖α‖) := add_le_add hl' hu'
      _ = _ := by ring
  · have hBA : B ≤ A := by omega
    simp only [Finset.Ico_eq_empty_of_le hBA,Finset.sum_empty,norm_zero]
    positivity

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Real
open scoped BigOperators Classical ComplexConjugate

namespace Helfgott

lemma etaTwo_pair_fourier_all_frequencies (y z : ℝ) (hy : 0 < y) (hz : 0 < z)
    (α : AddCircle (1 : ℝ)) (A B : ℕ) :
    ‖∑ d ∈ Finset.Ico A B,((etaTwo ((d : ℝ)/y)*etaTwo ((d : ℝ)/z) : ℝ) : ℂ)*
      fourier (d : ℤ) α‖ ≤ (4*Real.log 2)^2*
        (if α = 0 then ((B-A : ℕ) : ℝ) else min ((B-A : ℕ) : ℝ) (2/‖α‖)) := by
  have hM : 0 ≤ 4*Real.log (2 : ℝ) := by positivity
  have htrivial : ‖∑ d ∈ Finset.Ico A B,((etaTwo ((d : ℝ)/y)*etaTwo ((d : ℝ)/z) : ℝ) : ℂ)*
      fourier (d : ℤ) α‖ ≤ (4*Real.log 2)^2*((B-A : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ d ∈ Finset.Ico A B,‖((etaTwo ((d : ℝ)/y)*etaTwo ((d : ℝ)/z) : ℝ) : ℂ)*fourier (d : ℤ) α‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.Ico A B,(4*Real.log 2)^2 := by
        apply Finset.sum_le_sum
        intro d hd
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (etaTwo_nonneg _) (etaTwo_nonneg _)),
          show ‖fourier (d : ℤ) α‖ = 1 from Circle.norm_coe _,mul_one]
        simpa only [pow_two] using mul_le_mul (etaTwo_le _) (etaTwo_le _) (etaTwo_nonneg _) hM
      _ = _ := by simp [mul_comm]
  by_cases hα : α = 0
  · simpa only [if_pos hα] using htrivial
  · rw [if_neg hα,mul_min_of_nonneg _ _ (sq_nonneg _)]
    apply le_min htrivial
    calc
      _ ≤ 2*(4*Real.log 2)^2/‖α‖ := etaTwo_pair_fourier_interval_cancellation y z hy hz α hα A B
      _ = (4*Real.log 2)^2*(2/‖α‖) := by ring

lemma compact_bilinear_kernel_correlation (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) (A B m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ‖∑ d ∈ Finset.Ico A B,
      ((etaTwo (((d*m : ℕ) : ℝ)/y) : ℂ)*fourier ((d*m : ℕ) : ℤ) α)*
      conj ((etaTwo (((d*n : ℕ) : ℝ)/y) : ℂ)*fourier ((d*n : ℕ) : ℤ) α)‖ ≤
      (4*Real.log 2)^2*
        (if ((m : ℤ)-(n : ℤ)) • α = 0 then ((B-A : ℕ) : ℝ)
         else min ((B-A : ℕ) : ℝ) (2/‖((m : ℤ)-(n : ℤ)) • α‖)) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have he (d : ℕ) :
      ((etaTwo (((d*m : ℕ) : ℝ)/y) : ℂ)*fourier ((d*m : ℕ) : ℤ) α)*
      conj ((etaTwo (((d*n : ℕ) : ℝ)/y) : ℂ)*fourier ((d*n : ℕ) : ℤ) α) =
      ((etaTwo ((d : ℝ)/(y/(m : ℝ)))*etaTwo ((d : ℝ)/(y/(n : ℝ))) : ℝ) : ℂ)*
        fourier (d : ℤ) (((m : ℤ)-(n : ℤ)) • α) := by
    have hem : ((d*m : ℕ) : ℝ)/y = (d : ℝ)/(y/(m : ℝ)) := by
      push_cast
      field_simp
    have hen : ((d*n : ℕ) : ℝ)/y = (d : ℝ)/(y/(n : ℝ)) := by
      push_cast
      field_simp
    rw [map_mul,Complex.conj_ofReal,hem,hen,Complex.ofReal_mul]
    rw [show ((etaTwo ((d : ℝ)/(y/(m : ℝ))) : ℂ)*fourier ((d*m : ℕ) : ℤ) α)*
        ((etaTwo ((d : ℝ)/(y/(n : ℝ))) : ℂ)*conj (fourier ((d*n : ℕ) : ℤ) α)) =
        ((etaTwo ((d : ℝ)/(y/(m : ℝ))) : ℂ)*(etaTwo ((d : ℝ)/(y/(n : ℝ))) : ℂ))*
          (fourier ((d*m : ℕ) : ℤ) α*conj (fourier ((d*n : ℕ) : ℤ) α)) by ring]
    rw [fourier_product_correlation]
  simp_rw [he]
  exact etaTwo_pair_fourier_all_frequencies (y/(m : ℝ)) (y/(n : ℝ))
    (div_pos hy hm0) (div_pos hy hn0) _ A B

theorem compact_bilinear_fourier_cancellation (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) (A B : ℕ) (M : Finset ℕ)
    (hM : ∀ m ∈ M,0 < m) (a b : ℕ → ℂ) :
    ‖∑ d ∈ Finset.Ico A B,∑ m ∈ M,a d*b m*
      ((etaTwo (((d*m : ℕ) : ℝ)/y) : ℂ)*fourier ((d*m : ℕ) : ℤ) α)‖^2 ≤
      (∑ d ∈ Finset.Ico A B,‖a d‖^2)*
      (∑ m ∈ M,∑ n ∈ M,‖b m‖*‖b n‖*((4*Real.log 2)^2*
        (if ((m : ℤ)-(n : ℤ)) • α = 0 then ((B-A : ℕ) : ℝ)
         else min ((B-A : ℕ) : ℝ) (2/‖((m : ℤ)-(n : ℤ)) • α‖)))) := by
  apply finite_bilinear_correlation_bound
  intro m hm n hn
  exact compact_bilinear_kernel_correlation y hy α A B m n (hM m hm) (hM n hn)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Real
open scoped BigOperators Classical

namespace Helfgott

lemma symmetric_finite_correlation_schur {ι : Type*} (M : Finset ι) (u : ι → ℝ)
    (C : ι → ι → ℝ) (R : ℝ) (hC : ∀ m n,0 ≤ C m n)
    (hsym : ∀ m n,C m n=C n m)
    (hrow : ∀ m ∈ M,(∑ n ∈ M,C m n) ≤ R) :
    (∑ m ∈ M,∑ n ∈ M,u m*u n*C m n) ≤ R*(∑ m ∈ M,(u m)^2) := by
  have hp : (∑ m ∈ M,∑ n ∈ M,(2*u m*u n)*C m n) ≤
      ∑ m ∈ M,∑ n ∈ M,((u m)^2+(u n)^2)*C m n := by
    apply Finset.sum_le_sum
    intro m hm
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (u m-u n)]) (hC m n)
  have hleft : (∑ m ∈ M,∑ n ∈ M,(2*u m*u n)*C m n) =
      2*(∑ m ∈ M,∑ n ∈ M,u m*u n*C m n) := by
    simp_rw [show ∀ m n,(2*u m*u n)*C m n = 2*(u m*u n*C m n) by intro m n;ring,←Finset.mul_sum]
  have hright : (∑ m ∈ M,∑ n ∈ M,((u m)^2+(u n)^2)*C m n) =
      2*(∑ m ∈ M,(u m)^2*(∑ n ∈ M,C m n)) := by
    simp_rw [add_mul,Finset.sum_add_distrib]
    have he : (∑ m ∈ M,∑ n ∈ M,(u n)^2*C m n) =
        ∑ m ∈ M,∑ n ∈ M,(u m)^2*C m n := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [hsym n m]
    rw [he]
    simp_rw [←Finset.mul_sum]
    ring
  have hr : (∑ m ∈ M,(u m)^2*(∑ n ∈ M,C m n)) ≤ R*(∑ m ∈ M,(u m)^2) := by
    calc
      _ ≤ ∑ m ∈ M,(u m)^2*R := Finset.sum_le_sum (fun m hm => mul_le_mul_of_nonneg_left (hrow m hm) (sq_nonneg _))
      _ = _ := by rw [←Finset.sum_mul];ring
  rw [hleft,hright] at hp
  linarith

lemma multiple_distance_kernel_symmetric (α : AddCircle (1 : ℝ)) (L C : ℝ) (m n : ℕ) :
    (if ((m : ℤ)-(n : ℤ)) • α=0 then L else min L (C/‖((m : ℤ)-(n : ℤ)) • α‖)) =
    (if ((n : ℤ)-(m : ℤ)) • α=0 then L else min L (C/‖((n : ℤ)-(m : ℤ)) • α‖)) := by
  have he : ((n : ℤ)-(m : ℤ)) • α = -(((m : ℤ)-(n : ℤ)) • α) := by
    rw [←neg_smul]
    congr 1
    ring
  rw [he]
  simp only [neg_eq_zero,norm_neg]

theorem compact_bilinear_rational_energy_bound (y : ℝ) (hy : 0 < y)
    (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q)
    (α : AddCircle (1 : ℝ))
    (hα : ‖α-((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ))‖ ≤ 1/(q : ℝ)^2)
    (A B C D : ℕ) (hC : 1 ≤ C) (u v : ℕ → ℂ) :
    ‖∑ d ∈ Finset.Ico A B,∑ m ∈ Finset.Ico C D,u d*v m*
      ((etaTwo (((d*m : ℕ) : ℝ)/y) : ℂ)*fourier ((d*m : ℕ) : ℤ) α)‖^2 ≤
      (∑ d ∈ Finset.Ico A B,‖u d‖^2)*(∑ m ∈ Finset.Ico C D,‖v m‖^2)*
      ((4*Real.log 2)^2*(((D-C)/(q/2)+1 : ℕ) : ℝ)*
        (2*((B-A : ℕ) : ℝ)+8*(q : ℝ)*(harmonic q : ℝ))) := by
  let K : ℕ → ℕ → ℝ := fun m n =>
    (4*Real.log 2)^2*(if ((m : ℤ)-(n : ℤ)) • α=0 then ((B-A : ℕ) : ℝ)
      else min ((B-A : ℕ) : ℝ) (2/‖((m : ℤ)-(n : ℤ)) • α‖))
  let R : ℝ := (4*Real.log 2)^2*(((D-C)/(q/2)+1 : ℕ) : ℝ)*
    (2*((B-A : ℕ) : ℝ)+8*(q : ℝ)*(harmonic q : ℝ))
  have hK (m n : ℕ) : 0 ≤ K m n := by dsimp [K];split_ifs <;> positivity
  have hsym (m n : ℕ) : K m n=K n m := by dsimp [K];rw [multiple_distance_kernel_symmetric α _ _ m n]
  have hrow (m : ℕ) (hm : m ∈ Finset.Ico C D) : (∑ n ∈ Finset.Ico C D,K m n) ≤ R := by
    have hh := rational_approx_reciprocal_sum a q hq ha α (m • α) hα C D ((B-A : ℕ) : ℝ) (by positivity)
    have he (n : ℕ) : ((n : ℤ)-(m : ℤ)) • α=n • α-m • α := by simp only [sub_smul,natCast_zsmul]
    dsimp [K,R]
    simp_rw [multiple_distance_kernel_symmetric α _ _ m,he]
    rw [←Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hh (sq_nonneg _)).trans_eq (by ring)
  have hschur := symmetric_finite_correlation_schur (Finset.Ico C D) (fun m => ‖v m‖) K R hK hsym hrow
  have hh := compact_bilinear_fourier_cancellation y hy α A B (Finset.Ico C D)
    (by intro m hm;have := (Finset.mem_Ico.mp hm).1;omega) u v
  apply hh.trans
  apply (mul_le_mul_of_nonneg_left hschur (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans_eq
  dsimp [R]
  ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem finite_divisor_weight_square_energy (M U : ℕ) (c : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 M,(∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2) =
      ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*((M/(Nat.lcm d e) : ℕ) : ℝ) := by
  have hpoint (n : ℕ) : (∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2 =
      ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        if Nat.lcm d e ∣ n then c d*c e else 0 := by
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hdvd : d ∣ n <;> by_cases hevd : e ∣ n <;>
      simp [hdvd,hevd,Nat.lcm_dvd_iff]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,smul_eq_mul]
  have hi : (Finset.Icc 1 M).filter (fun n => Nat.lcm d e ∣ n) =
      (Finset.Ioc 0 M).filter (fun n => Nat.lcm d e ∣ n) := by
    congr 1
  rw [hi,Nat.Ioc_filter_dvd_card_eq_div]
  ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
open ArithmeticFunction MeasureTheory Set Finset
open scoped BigOperators Classical

namespace Helfgott

lemma arithmeticCutoff_add_tail (U : ℕ) (f : ArithmeticFunction ℝ) :
    arithmeticCutoff U f+arithmeticTail U f = f := by
  unfold arithmeticTail
  abel

theorem vaughan_arithmetic_identity (U V : ℕ) :
    (vonMangoldt : ArithmeticFunction ℝ) = vaughanTypeOne U-vaughanCorrection U V+
      arithmeticCutoff V vonMangoldt+vaughanTypeTwo U V := by
  let ml : ArithmeticFunction ℝ := arithmeticCutoff U (moebius : ArithmeticFunction ℝ)
  let mh : ArithmeticFunction ℝ := arithmeticTail U (moebius : ArithmeticFunction ℝ)
  let ll : ArithmeticFunction ℝ := arithmeticCutoff V vonMangoldt
  let lh : ArithmeticFunction ℝ := arithmeticTail V vonMangoldt
  have hm : ml+mh = (moebius : ArithmeticFunction ℝ) := arithmeticCutoff_add_tail U _
  have hl : ll+lh = (vonMangoldt : ArithmeticFunction ℝ) := arithmeticCutoff_add_tail V _
  have hz : (ml+mh)*(zeta : ArithmeticFunction ℝ) = 1 := by
    rw [hm,coe_moebius_mul_coe_zeta]
  change (vonMangoldt : ArithmeticFunction ℝ) = ml*log-ml*ll*zeta+ll+mh*lh*zeta
  rw [←vonMangoldt_mul_zeta,←hl]
  calc
    ll+lh = ll+((ml+mh)*zeta)*lh := by rw [hz,one_mul]
    _ = _ := by ring

lemma etaTwo_arithmetic_eq_zero (f : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y) (n : ℕ)
    (hn : n ∉ Finset.Ioc 0 (Nat.floor y)) : f n*etaTwo ((n : ℝ)/y) = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hfloor : Nat.floor y < n := by simpa [Finset.mem_Ioc,hnpos] using hn
    have hlarge : y < (n : ℝ) := Nat.lt_of_floor_lt hfloor
    have hz : etaTwo ((n : ℝ)/y) = 0 := by
      apply etaTwo_eq_zero_of_not_mem
      intro hm
      have hh := (div_le_iff₀ hy).mp hm.2
      linarith
    rw [hz,mul_zero]

lemma etaTwo_arithmetic_summable (f : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℕ => ((f n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) := by
  apply summable_of_ne_finset_zero (s := Finset.Ioc 0 (Nat.floor y))
  intro n hn
  rw [etaTwo_arithmetic_eq_zero f y hy n hn]
  simp

lemma etaTwo_arithmetic_expSum_finite (f : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => ((f n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      ∑ n ∈ Finset.Ioc 0 (Nat.floor y), ((f n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)*fourier (n : ℤ) α := by
  unfold expSum
  apply tsum_eq_sum
  intro n hn
  dsimp only
  rw [etaTwo_arithmetic_eq_zero f y hy n hn]
  simp

theorem vaughan_etaTwo_expSum_identity (U V : ℕ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => ((vonMangoldt n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      expSum (fun n => ((vaughanTypeOne U n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α-
      expSum (fun n => ((vaughanCorrection U V n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α+
      expSum (fun n => ((arithmeticCutoff V vonMangoldt n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α+
      expSum (fun n => ((vaughanTypeTwo U V n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α := by
  simp_rw [etaTwo_arithmetic_expSum_finite _ y hy α]
  rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  have hn := congrArg (fun f : ArithmeticFunction ℝ => f n) (vaughan_arithmetic_identity U V)
  simp only [sub_eq_add_neg,ArithmeticFunction.add_apply,ArithmeticFunction.neg_apply] at hn
  rw [hn]
  push_cast
  ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Finset
open scoped BigOperators Classical

namespace Helfgott

theorem truncated_divisor_sum_complex (B : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ q ∈ Icc 1 B, ∑ d ∈ q.divisors, F d (q/d)) =
      ∑ d ∈ Icc 1 B, ∑ r ∈ Icc 1 (B/d), F d r := by
  classical
  rw [← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.2 (i.1/i.2)),
    ← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.1 i.2)]
  refine sum_bij (fun i _ => (⟨i.2, i.1/i.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    rcases mem_sigma.mp hi with ⟨hq, hd⟩
    have hdq := (Nat.mem_divisors.mp hd).1
    have hqpos : 0 < i.1 := (mem_Icc.mp hq).1
    have hdpos := Nat.pos_of_dvd_of_pos hdq hqpos
    apply mem_sigma.mpr
    constructor
    · exact mem_Icc.mpr ⟨hdpos, (Nat.le_of_dvd hqpos hdq).trans (mem_Icc.mp hq).2⟩
    · apply mem_Icc.mpr
      exact ⟨Nat.div_pos (Nat.le_of_dvd hqpos hdq) hdpos,
        Nat.div_le_div_right (mem_Icc.mp hq).2⟩
  · intro i hi j hj he
    rcases mem_sigma.mp hi with ⟨_, hdi⟩
    rcases mem_sigma.mp hj with ⟨_, hdj⟩
    have hd : i.2 = j.2 := congrArg Sigma.fst he
    have hr : i.1/i.2 = j.1/j.2 := congrArg (fun k : Σ _ : ℕ, ℕ => k.2) he
    have hq : i.1 = j.1 := by
      calc
        i.1 = i.2*(i.1/i.2) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hdi).1).symm
        _ = j.2*(j.1/j.2) := by rw [hr, hd]
        _ = j.1 := Nat.mul_div_cancel' (Nat.mem_divisors.mp hdj).1
    exact Sigma.ext hq (by simpa using hd)
  · intro j hj
    rcases mem_sigma.mp hj with ⟨hd, hr⟩
    have hdpos : 0 < j.1 := (mem_Icc.mp hd).1
    have hrpos : 0 < j.2 := (mem_Icc.mp hr).1
    have hprod : j.1*j.2 ≤ B := by
      calc
        _ ≤ j.1*(B/j.1) := Nat.mul_le_mul_left j.1 (mem_Icc.mp hr).2
        _ ≤ B := by simpa only [mul_comm] using Nat.div_mul_le_self B j.1
    refine ⟨⟨j.1*j.2, j.1⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hdpos hrpos, hprod⟩,
      Nat.mem_divisors.mpr ⟨Nat.dvd_mul_right j.1 j.2, (Nat.mul_pos hdpos hrpos).ne'⟩⟩, ?_⟩
    change (⟨j.1, (j.1*j.2)/j.1⟩ : Σ _ : ℕ, ℕ) = j
    rw [Nat.mul_div_right j.2 hdpos]
  · intro _ _
    rfl

lemma etaTwo_convolution_expSum_hyperbola (f g : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => (((f*g) n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      ∑ d ∈ Finset.Icc 1 (Nat.floor y), ∑ m ∈ Finset.Icc 1 (Nat.floor (y/(d : ℝ))),
        ((f d*g m*etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α := by
  have hindex : Finset.Ioc 0 (Nat.floor y) = Finset.Icc 1 (Nat.floor y) := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_Icc]
    omega
  let F (d m : ℕ) : ℂ :=
    ((f d*g m*etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α
  rw [etaTwo_arithmetic_expSum_finite _ y hy α,hindex]
  have hinner (k : ℕ) :
      (((f*g) k*etaTwo ((k : ℝ)/y) : ℝ) : ℂ)*fourier (k : ℤ) α =
      ∑ d ∈ k.divisors, F d (k/d) := by
    rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun a b => f a*g b)]
    rw [Complex.ofReal_mul,Complex.ofReal_sum,Finset.sum_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    have he : d*(k/d) = k := Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1
    simp only [F,he,Complex.ofReal_mul]
  simp_rw [hinner]
  rw [truncated_divisor_sum_complex]
  apply Finset.sum_congr rfl
  intro d _
  rw [Nat.floor_div_natCast]

lemma arithmeticTail_zero_of_le (U n : ℕ) (f : ArithmeticFunction ℝ) (hn : n ≤ U) :
    arithmeticTail U f n = 0 := by
  change f n-(if n ≤ U then f n else 0) = 0
  simp [hn]

lemma arithmeticTail_self_of_gt (U n : ℕ) (f : ArithmeticFunction ℝ) (hn : U < n) :
    arithmeticTail U f n = f n := by
  change f n-(if n ≤ U then f n else 0) = f n
  simp [not_le_of_gt hn]

lemma vaughan_bilinear_coefficient_zero (U n : ℕ) (hn : n ≤ U) :
    (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) n = 0 := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hdn : d ≤ n := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.mem_divisors.mp hd).1
  exact arithmeticTail_zero_of_le U d _ (hdn.trans hn)

lemma vaughan_bilinear_coefficient_short_moebius (U n : ℕ) (hn : n ≠ 1) :
    (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) n =
      -(∑ d ∈ n.divisors.filter (fun d => d ≤ U), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) := by
  have he : arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta =
      1-arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta := by
    unfold arithmeticTail
    rw [sub_mul,ArithmeticFunction.coe_moebius_mul_coe_zeta]
  rw [he]
  simp only [sub_eq_add_neg,ArithmeticFunction.add_apply,ArithmeticFunction.neg_apply,
    ArithmeticFunction.one_apply_ne hn,zero_add]
  rw [ArithmeticFunction.coe_mul_zeta_apply,Finset.sum_filter]
  congr 1

lemma sum_Icc_of_low_zero (F : ℕ → ℂ) (U B : ℕ) (hF : ∀ n ≤ U, F n = 0) :
    (∑ n ∈ Finset.Icc 1 B, F n) = ∑ n ∈ Finset.Icc (U+1) B, F n := by
  symm
  apply Finset.sum_subset
  · intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨h1,h2⟩
    exact Finset.mem_Icc.mpr ⟨by omega,h2⟩
  · intro n hn hnot
    rcases Finset.mem_Icc.mp hn with ⟨h1,h2⟩
    have hnU : n ≤ U := by
      by_contra h
      exact hnot (Finset.mem_Icc.mpr ⟨by omega,h2⟩)
    exact hF n hnU

theorem vaughan_typeTwo_bilinear_expSum (U V : ℕ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => ((vaughanTypeTwo U V n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      ∑ d ∈ Finset.Icc (V+1) (Nat.floor y), ∑ m ∈ Finset.Icc (U+1) (Nat.floor (y/(d : ℝ))),
        ((ArithmeticFunction.vonMangoldt d*
          (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m*
          etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α := by
  have he : vaughanTypeTwo U V = arithmeticTail V ArithmeticFunction.vonMangoldt*
      (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) := by
    unfold vaughanTypeTwo
    ring
  rw [he,etaTwo_convolution_expSum_hyperbola _ _ y hy α]
  rw [sum_Icc_of_low_zero (U := V)]
  · apply Finset.sum_congr rfl
    intro d hd
    rw [sum_Icc_of_low_zero (U := U)]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [arithmeticTail_self_of_gt V d _ (by have := (Finset.mem_Icc.mp hd).1;omega)]
    · intro m hm
      rw [vaughan_bilinear_coefficient_zero U m hm]
      simp
  · intro d hd
    rw [arithmeticTail_zero_of_le V d _ hd]
    simp

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma short_moebius_divisor_sum (U n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors.filter (fun d => d ≤ U),((ArithmeticFunction.moebius d : ℤ) : ℝ)) =
      ∑ d ∈ Finset.Icc 1 U,if d ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0 := by
  have he : n.divisors.filter (fun d => d ≤ U) = (Finset.Icc 1 U).filter (fun d => d ∣ n) := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors,Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd,hn0⟩,hdU⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn,hdU⟩,hd⟩
    · rintro ⟨⟨hdpos,hdU⟩,hd⟩
      exact ⟨⟨hd,hn.ne'⟩,hdU⟩
  rw [he,Finset.sum_filter]

lemma vaughan_mobius_energy_pointwise (U n : ℕ) (hU : 1 ≤ U) (hn : 0 < n) :
    ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) n)^2 =
      (∑ d ∈ Finset.Icc 1 U,if d ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)^2-
      (if n=1 then 1 else 0) := by
  by_cases hn1 : n=1
  · subst n
    rw [vaughan_bilinear_coefficient_zero U 1 hU]
    have hs : (∑ d ∈ Finset.Icc 1 U,if d ∣ 1 then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) = 1 := by
      rw [←short_moebius_divisor_sum U 1 (by norm_num)]
      rw [Nat.divisors_one,Finset.filter_singleton]
      simp [hU]
    rw [hs]
    norm_num
  · rw [vaughan_bilinear_coefficient_short_moebius U n hn1,short_moebius_divisor_sum U n hn,if_neg hn1]
    ring

theorem vaughan_mobius_tail_square_energy (U M : ℕ) (hU : 1 ≤ U) :
    (∑ m ∈ Finset.Icc (U+1) M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) =
      (∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)*
        ((M/(Nat.lcm d e) : ℕ) : ℝ))-(if 1 ≤ M then 1 else 0) := by
  have hs : (∑ m ∈ Finset.Icc (U+1) M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) =
      (∑ m ∈ Finset.Icc 1 M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) := by
    apply Finset.sum_subset
    · intro m hm
      exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hm).1;omega,(Finset.mem_Icc.mp hm).2⟩
    · intro m hm hnot
      have hmU : m ≤ U := by
        have hml := (Finset.mem_Icc.mp hm).1
        have hmh := (Finset.mem_Icc.mp hm).2
        have hnot' : ¬(U+1 ≤ m ∧ m ≤ M) := by simpa only [Finset.mem_Icc] using hnot
        omega
      rw [vaughan_bilinear_coefficient_zero U m hmU]
      simp
  rw [hs]
  have he : (∑ m ∈ Finset.Icc 1 M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) =
      ∑ m ∈ Finset.Icc 1 M,
        ((∑ d ∈ Finset.Icc 1 U,if d ∣ m then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)^2-
          (if m=1 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact vaughan_mobius_energy_pointwise U m hU (Finset.mem_Icc.mp hm).1
  rw [he,Finset.sum_sub_distrib,finite_divisor_weight_square_energy]
  congr 1
  simp only [Finset.sum_ite_eq',Finset.mem_Icc]
  simp

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat Real
open scoped BigOperators Classical

namespace Helfgott

lemma nat_div_cast_error_le_one (M k : ℕ) (hk : 0 < k) :
    |((M/k : ℕ) : ℝ)-(M : ℝ)/(k : ℝ)| ≤ 1 := by
  have hlo : ((M/k : ℕ) : ℝ) ≤ (M : ℝ)/(k : ℝ) := Nat.cast_div_le
  have hmod : ((M%k : ℕ) : ℝ) < (k : ℝ) := by exact_mod_cast Nat.mod_lt M hk
  have he : (k : ℝ)*((M/k : ℕ) : ℝ)+((M%k : ℕ) : ℝ)=(M : ℝ) := by exact_mod_cast Nat.div_add_mod M k
  rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
  have hkR : (0 : ℝ)<k := by exact_mod_cast hk
  have hupper : (M : ℝ)/(k : ℝ) ≤ ((M/k : ℕ) : ℝ)+1 := (div_le_iff₀ hkR).mpr (by nlinarith)
  linarith

theorem finite_divisor_weight_square_energy_approximation (M U : ℕ) (c : ℕ → ℝ) :
    |(∑ n ∈ Finset.Icc 1 M,(∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2)-
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ))| ≤
        (∑ d ∈ Finset.Icc 1 U,|c d|)^2 := by
  rw [finite_divisor_weight_square_energy]
  have he : (∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*((M/(Nat.lcm d e) : ℕ) : ℝ))-
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ)) =
      ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*
        (((M/(Nat.lcm d e) : ℕ) : ℝ)-(M : ℝ)/(Nat.lcm d e : ℝ)) := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e he
    ring
  rw [he]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 U,|∑ e ∈ Finset.Icc 1 U,c d*c e*
        (((M/(Nat.lcm d e) : ℕ) : ℝ)-(M : ℝ)/(Nat.lcm d e : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,|c d| * |c e| := by
      apply Finset.sum_le_sum
      intro d hd
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro e he
      have hk : 0 < Nat.lcm d e := Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
      rw [abs_mul,abs_mul]
      exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (nat_div_cast_error_le_one M _ hk)
    _ = _ := by rw [pow_two,Finset.sum_mul];apply Finset.sum_congr rfl;intro d hd;rw [Finset.mul_sum]

theorem finite_divisor_weight_leading_quadratic_nonneg (U : ℕ) (c : ℕ → ℝ) :
    0 ≤ ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ) := by
  let M := U.factorial
  have hM : (0:ℝ)<M := by exact_mod_cast Nat.factorial_pos U
  have hexact : (∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*((M/(Nat.lcm d e) : ℕ) : ℝ)) =
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hdM : d ∣ M := Nat.dvd_factorial (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2
    have heM : e ∣ M := Nat.dvd_factorial (Finset.mem_Icc.mp he).1 (Finset.mem_Icc.mp he).2
    rw [Nat.cast_div (Nat.lcm_dvd hdM heM)] <;> try exact_mod_cast (Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1).ne'
    ring
  have h := finite_divisor_weight_square_energy M U c
  rw [hexact] at h
  have hnonneg : 0 ≤ (∑ n ∈ Finset.Icc 1 M,(∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2) :=
    Finset.sum_nonneg (fun n hn => sq_nonneg _)
  rw [h] at hnonneg
  exact nonneg_of_mul_nonneg_right hnonneg hM

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem vaughan_mobius_tail_energy_asymptotic (U M : ℕ) (hU : 1 ≤ U) :
    (0 ≤ ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ)) ∧
    |(∑ m ∈ Finset.Icc (U+1) M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2)+
      (if 1 ≤ M then 1 else 0)-
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ))| ≤ (U : ℝ)^2 := by
  refine ⟨finite_divisor_weight_leading_quadratic_nonneg U _,?_⟩
  have hsum : (∑ d ∈ Finset.Icc 1 U,|((ArithmeticFunction.moebius d : ℤ) : ℝ)|) ≤ (U : ℝ) := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 U,(1:ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      _ = _ := by simp
  have h := finite_divisor_weight_square_energy_approximation M U (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ))
  have he := vaughan_mobius_tail_square_energy U M hU
  have hfull := finite_divisor_weight_square_energy M U (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ))
  rw [hfull] at h
  rw [he,sub_add_cancel]
  refine h.trans ?_
  nlinarith [Finset.sum_nonneg (fun d (_ : d ∈ Finset.Icc 1 U) => abs_nonneg (((ArithmeticFunction.moebius d : ℤ) : ℝ)))]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem vonMangoldt_square_interval_energy (A B : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B) :
    (∑ d ∈ Finset.Ico A B,(vonMangoldt d)^2) ≤
      Real.log (B : ℝ)*(Real.log 4*(B : ℝ)+2*Real.sqrt (B : ℝ)*Real.log (B : ℝ)) := by
  have hBR : (1:ℝ) ≤ B := by exact_mod_cast hB
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg hBR
  have hpoint (d : ℕ) (hd : d ∈ Finset.Ico A B) :
      (vonMangoldt d)^2 ≤ Real.log (B : ℝ)*vonMangoldt d := by
    have hdpos : (0:ℝ)<d := by exact_mod_cast (show 0<d from by have := (Finset.mem_Ico.mp hd).1;omega)
    have hdB : (d : ℝ) ≤ B := by exact_mod_cast (Finset.mem_Ico.mp hd).2.le
    have hl := (vonMangoldt_le_log (n := d)).trans (Real.log_le_log hdpos hdB)
    nlinarith [vonMangoldt_nonneg (n := d)]
  have hsubset : Finset.Ico A B ⊆ Finset.Icc 1 B := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨hA.trans (Finset.mem_Ico.mp hd).1,(Finset.mem_Ico.mp hd).2.le⟩
  have hpsi : (∑ d ∈ Finset.Icc 1 B,vonMangoldt d) = Chebyshev.psi (B : ℝ) := by
    rw [Chebyshev.psi_eq_sum_Icc]
    simp only [Nat.floor_natCast]
    apply Finset.sum_subset
    · intro d hd
      exact Finset.mem_Icc.mpr ⟨by omega,(Finset.mem_Icc.mp hd).2⟩
    · intro d hd hnot
      have hd0 : d=0 := by
        have hdB := (Finset.mem_Icc.mp hd).2
        have hnot' : ¬(1 ≤ d ∧ d ≤ B) := by simpa only [Finset.mem_Icc] using hnot
        omega
      subst d
      simp
  calc
    _ ≤ ∑ d ∈ Finset.Ico A B,Real.log (B : ℝ)*vonMangoldt d := Finset.sum_le_sum hpoint
    _ = Real.log (B : ℝ)*(∑ d ∈ Finset.Ico A B,vonMangoldt d) := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.log (B : ℝ)*(∑ d ∈ Finset.Icc 1 B,vonMangoldt d) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun d _ _ => vonMangoldt_nonneg)) hlogB
    _ = Real.log (B : ℝ)*Chebyshev.psi (B : ℝ) := by rw [hpsi]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Chebyshev.psi_le hBR) hlogB

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2500000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma vaughan_mobius_interval_energy_upper (U C D : ℕ) (hU : 1 ≤ U) (hC : U+1 ≤ C) :
    (∑ m ∈ Finset.Ico C D,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) ≤
      (D : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ))+(U : ℝ)^2 := by
  have hsubset : Finset.Ico C D ⊆ Finset.Icc (U+1) D := by
    intro m hm
    exact Finset.mem_Icc.mpr ⟨hC.trans (Finset.mem_Ico.mp hm).1,(Finset.mem_Ico.mp hm).2.le⟩
  have h := (vaughan_mobius_tail_energy_asymptotic U D hU).2
  have hupper := (le_abs_self _).trans h
  have hδ : (0:ℝ) ≤ (if 1 ≤ D then 1 else 0) := by split_ifs <;> norm_num
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun m _ _ => sq_nonneg _)).trans ?_
  linarith

theorem vaughan_typeTwo_block_rational_arithmetic_upper_complete
    (U A B C D a q : ℕ) (hU : 1 ≤ U) (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : U+1 ≤ C)
    (hq : 2 ≤ q) (ha : Nat.Coprime a q) (y : ℝ) (hy : 0 < y) (α : AddCircle (1 : ℝ))
    (hα : ‖α-((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ))‖ ≤ 1/(q : ℝ)^2) :
    ‖∑ d ∈ Finset.Ico A B,∑ m ∈ Finset.Ico C D,(vonMangoldt d : ℂ)*
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m : ℂ)*
      ((etaTwo (((d*m : ℕ) : ℝ)/y) : ℂ)*fourier ((d*m : ℕ) : ℤ) α)‖^2 ≤
      (Real.log (B : ℝ)*(Real.log 4*(B : ℝ)+2*Real.sqrt (B : ℝ)*Real.log (B : ℝ)))*
      ((D : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ))+(U : ℝ)^2)*
      ((4*Real.log 2)^2*(((D-C)/(q/2)+1 : ℕ) : ℝ)*
        (2*((B-A : ℕ) : ℝ)+8*(q : ℝ)*(1+Real.log (q : ℝ)))) := by
  have hCpos : 1 ≤ C := by omega
  have hh := compact_bilinear_rational_energy_bound y hy a q hq ha α hα A B C D hCpos
    (fun d => (vonMangoldt d : ℂ))
    (fun m => ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m : ℂ))
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs] at hh
  have hΛ := vonMangoldt_square_interval_energy A B hA hB
  have hμ := vaughan_mobius_interval_energy_upper U C D hU hC
  have hΛnonneg : 0 ≤ Real.log (B : ℝ)*(Real.log 4*(B : ℝ)+2*Real.sqrt (B : ℝ)*Real.log (B : ℝ)) :=
    (Finset.sum_nonneg (fun d (_ : d ∈ Finset.Ico A B) => sq_nonneg (vonMangoldt d))).trans hΛ
  have hμnonneg : 0 ≤ (D : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ))+(U : ℝ)^2 :=
    (Finset.sum_nonneg (fun m (_ : m ∈ Finset.Ico C D) => sq_nonneg _)).trans hμ
  have hprod := mul_le_mul hΛ hμ (Finset.sum_nonneg (fun m (_ : m ∈ Finset.Ico C D) => sq_nonneg _)) hΛnonneg
  have hHnonneg : (0:ℝ) ≤ (harmonic q : ℝ) := by
    simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    apply Finset.sum_nonneg
    intro i hi
    positivity
  refine hh.trans ((mul_le_mul_of_nonneg_right hprod (by positivity)).trans ?_)
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hΛnonneg hμnonneg)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_right
  exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log q) (by positivity)

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction

theorem solution 
    (U A B C D a q : ℕ) (hU : 1 ≤ U) (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : U+1 ≤ C)
    (hq : 2 ≤ q) (ha : Nat.Coprime a q) (y : ℝ) (hy : 0 < y) (α : AddCircle (1 : ℝ))
    (hα : ‖α-((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ))‖ ≤ 1/(q : ℝ)^2) :
    ‖∑ d ∈ Finset.Ico A B,∑ m ∈ Finset.Ico C D,(vonMangoldt d : ℂ)*
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m : ℂ)*
      ((etaTwo (((d*m : ℕ) : ℝ)/y) : ℂ)*fourier ((d*m : ℕ) : ℤ) α)‖^2 ≤
      (Real.log (B : ℝ)*(Real.log 4*(B : ℝ)+2*Real.sqrt (B : ℝ)*Real.log (B : ℝ)))*
      ((D : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ))+(U : ℝ)^2)*
      ((4*Real.log 2)^2*(((D-C)/(q/2)+1 : ℕ) : ℝ)*
        (2*((B-A : ℕ) : ℝ)+8*(q : ℝ)*(1+Real.log (q : ℝ)))) := Helfgott.vaughan_typeTwo_block_rational_arithmetic_upper_complete U A B C D a q hU hA hB hC hq ha y hy α hα

#print axioms solution
