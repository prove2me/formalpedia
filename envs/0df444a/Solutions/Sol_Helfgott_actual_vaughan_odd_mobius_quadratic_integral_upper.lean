-- Prove2me | solution 1 for Helfgott.actual_vaughan_odd_mobius_quadratic_integral_upper
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T16:01:12.819259+00:00
-- url     : https://prove2.me/submissions/50bdc832-4cc8-484c-af03-e67ce464565f

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import Definitions.Def_Helfgott_VaughanData
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Divisors
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem divisor_pair_gcd_reindex (m : ℕ) (hm : 0<m) (F : ℕ → ℕ → ℝ) :
    (∑ d ∈ m.divisors,∑ e ∈ m.divisors,F d e)=
      ∑ t ∈ ((Finset.Icc 1 m)×ˢ((Finset.Icc 1 m)×ˢ(Finset.Icc 1 m))).filter
        (fun t : ℕ×(ℕ×ℕ) => t.1*t.2.1*t.2.2 ∣ m ∧ Nat.Coprime t.2.1 t.2.2),
        F (t.1*t.2.1) (t.1*t.2.2) := by
  rw [←Finset.sum_product (f:=fun p : ℕ×ℕ => F p.1 p.2)]
  symm
  refine Finset.sum_bij (fun t _ => (t.1*t.2.1,t.1*t.2.2)) ?_ ?_ ?_ ?_
  · intro t ht
    rcases Finset.mem_filter.mp ht with ⟨hmem,hdvd,hcop⟩
    rcases Finset.mem_product.mp hmem with ⟨hg,hrs⟩
    rcases Finset.mem_product.mp hrs with ⟨hr,hs⟩
    apply Finset.mem_product.mpr
    constructor
    · exact Nat.mem_divisors.mpr ⟨dvd_trans (dvd_mul_right (t.1*t.2.1) t.2.2) hdvd,hm.ne'⟩
    · have h : t.1*t.2.2 ∣ t.1*t.2.1*t.2.2 := by
        refine ⟨t.2.1,?_⟩
        ring
      exact Nat.mem_divisors.mpr ⟨h.trans hdvd,hm.ne'⟩
  · intro t ht u hu heq
    rcases Finset.mem_filter.mp ht with ⟨htmem,htdvd,htcop⟩
    rcases Finset.mem_filter.mp hu with ⟨humem,hudvd,hucop⟩
    have hg : t.1=u.1 := by
      have h := congrArg (fun p : ℕ×ℕ => Nat.gcd p.1 p.2) heq
      simpa only [Nat.gcd_mul_left,htcop.gcd_eq_one,hucop.gcd_eq_one,mul_one] using h
    have htg : 0<t.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp htmem).1).1
    have htr : t.2.1=u.2.1 := by
      have h := congrArg Prod.fst heq
      rw [←hg] at h
      exact Nat.eq_of_mul_eq_mul_left htg h
    have hts : t.2.2=u.2.2 := by
      have h := congrArg Prod.snd heq
      rw [←hg] at h
      exact Nat.eq_of_mul_eq_mul_left htg h
    exact Prod.ext hg (Prod.ext htr hts)
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨hd,he⟩
    have hdpos : 0<p.1 := Nat.pos_of_mem_divisors hd
    have hepos : 0<p.2 := Nat.pos_of_mem_divisors he
    let g := Nat.gcd p.1 p.2
    let r := p.1/g
    let s := p.2/g
    have hgpos : 0<g := Nat.gcd_pos_of_pos_left p.2 hdpos
    have hgr : g*r=p.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2)
    have hgs : g*s=p.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2)
    have hrpos : 0<r := Nat.div_pos (Nat.le_of_dvd hdpos (Nat.gcd_dvd_left p.1 p.2)) hgpos
    have hspos : 0<s := Nat.div_pos (Nat.le_of_dvd hepos (Nat.gcd_dvd_right p.1 p.2)) hgpos
    have hcop : Nat.Coprime r s := Nat.coprime_div_gcd_div_gcd hgpos
    have hlcm : Nat.lcm p.1 p.2=g*r*s := by
      apply Nat.eq_of_mul_eq_mul_left hgpos
      calc
        g*Nat.lcm p.1 p.2=p.1*p.2 := Nat.gcd_mul_lcm p.1 p.2
        _=(g*r)*(g*s) := by rw [hgr,hgs]
        _=g*(g*r*s) := by ring
    have htdiv : g*r*s ∣ m := by
      rw [←hlcm]
      exact Nat.lcm_dvd (Nat.dvd_of_mem_divisors hd) (Nat.dvd_of_mem_divisors he)
    have hgdiv : g ∣ m := (Nat.gcd_dvd_left p.1 p.2).trans (Nat.dvd_of_mem_divisors hd)
    have hrdiv : r ∣ m := by
      have h : r ∣ p.1 := by rw [←hgr];exact dvd_mul_left r g
      exact h.trans (Nat.dvd_of_mem_divisors hd)
    have hsdiv : s ∣ m := by
      have h : s ∣ p.2 := by rw [←hgs];exact dvd_mul_left s g
      exact h.trans (Nat.dvd_of_mem_divisors he)
    refine ⟨(g,(r,s)),Finset.mem_filter.mpr ⟨?_,htdiv,hcop⟩,?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hgpos,Nat.le_of_dvd hm hgdiv⟩,
        Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hrpos,Nat.le_of_dvd hm hrdiv⟩,
          Finset.mem_Icc.mpr ⟨hspos,Nat.le_of_dvd hm hsdiv⟩⟩⟩
    · exact Prod.ext hgr hgs
  · intro t ht
    rfl

lemma moebius_common_factor_product (g r s : ℕ) :
    ((moebius (g*r) : ℤ) : ℝ)*((moebius (g*s) : ℤ) : ℝ)=
      if Nat.Coprime g (r*s) then ((moebius g : ℤ) : ℝ)^2*
        ((moebius r : ℤ) : ℝ)*((moebius s : ℤ) : ℝ) else 0 := by
  by_cases hc : Nat.Coprime g (r*s)
  · rw [if_pos hc]
    have hgr : Nat.Coprime g r := hc.of_dvd_right (dvd_mul_right r s)
    have hgs : Nat.Coprime g s := hc.of_dvd_right (dvd_mul_left s r)
    have h1 := isMultiplicative_moebius.map_mul_of_coprime hgr
    have h2 := isMultiplicative_moebius.map_mul_of_coprime hgs
    rw [h1,h2]
    push_cast
    ring
  · rw [if_neg hc]
    have hnot : ¬Nat.Coprime g r ∨ ¬Nat.Coprime g s := by
      by_contra h
      push_neg at h
      exact hc (h.1.mul_right h.2)
    rcases hnot with hgr|hgs
    · have hs : ¬Squarefree (g*r) := fun h => hgr (Nat.coprime_of_squarefree_mul h)
      rw [moebius_eq_zero_of_not_squarefree hs]
      norm_num
    · have hs : ¬Squarefree (g*s) := fun h => hgs (Nat.coprime_of_squarefree_mul h)
      rw [moebius_eq_zero_of_not_squarefree hs]
      norm_num

theorem moebius_large_divisor_square_gcd_reindex (U m : ℕ) (hm : 0<m) :
    (∑ d ∈ m.divisors,if U<d then ((moebius d : ℤ) : ℝ) else 0)^2=
      ∑ t ∈ ((Finset.Icc 1 m)×ˢ((Finset.Icc 1 m)×ˢ(Finset.Icc 1 m))).filter
        (fun t : ℕ×(ℕ×ℕ) => t.1*t.2.1*t.2.2 ∣ m ∧ Nat.Coprime t.2.1 t.2.2),
        if U<t.1*t.2.1 ∧ U<t.1*t.2.2 ∧ Nat.Coprime t.1 (t.2.1*t.2.2) then
          ((moebius t.1 : ℤ) : ℝ)^2*((moebius t.2.1 : ℤ) : ℝ)*((moebius t.2.2 : ℤ) : ℝ) else 0 := by
  rw [pow_two,Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [divisor_pair_gcd_reindex m hm]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hr : U<t.1*t.2.1 <;> by_cases hs : U<t.1*t.2.2 <;>
    by_cases hc : Nat.Coprime t.1 (t.2.1*t.2.2)
  all_goals simp [hr,hs,hc,moebius_common_factor_product]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma interval_multiples_sum (A B k : ℕ) (hk : 0<k) (F : ℕ → ℝ) :
    (∑ m ∈ Finset.Ioc A B,if k ∣ m then F m else 0)=
      ∑ l ∈ Finset.Icc 1 B,if A<k*l ∧ k*l≤B then F (k*l) else 0 := by
  rw [←Finset.sum_filter,←Finset.sum_filter]
  refine Finset.sum_bij (fun m _ => m/k) ?_ ?_ ?_ ?_
  · intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmI,hdvd⟩
    have hmpos : 0<m := by have h := (Finset.mem_Ioc.mp hmI).1;omega
    have he : k*(m/k)=m := Nat.mul_div_cancel' hdvd
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hmpos hdvd) hk,
      (Nat.div_le_self m k).trans (Finset.mem_Ioc.mp hmI).2⟩,by simpa only [he] using Finset.mem_Ioc.mp hmI⟩
  · intro m hm n hn heq
    have hmdiv := (Finset.mem_filter.mp hm).2
    have hndiv := (Finset.mem_filter.mp hn).2
    calc m=k*(m/k) := (Nat.mul_div_cancel' hmdiv).symm
         _=k*(n/k) := by rw [heq]
         _=n := Nat.mul_div_cancel' hndiv
  · intro l hl
    rcases Finset.mem_filter.mp hl with ⟨hlI,hlo,hhi⟩
    refine ⟨k*l,Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hlo,hhi⟩,dvd_mul_right k l⟩,?_⟩
    exact Nat.mul_div_right l hk
  · intro m hm
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hm).2]

lemma divisor_gcd_triple_cap_eq (m B : ℕ) (hm : 0<m) (hmB : m≤B) :
    ((Finset.Icc 1 m)×ˢ((Finset.Icc 1 m)×ˢ(Finset.Icc 1 m))).filter
        (fun t : ℕ×(ℕ×ℕ) => t.1*t.2.1*t.2.2 ∣ m ∧ Nat.Coprime t.2.1 t.2.2)=
    ((Finset.Icc 1 B)×ˢ((Finset.Icc 1 B)×ˢ(Finset.Icc 1 B))).filter
        (fun t : ℕ×(ℕ×ℕ) => t.1*t.2.1*t.2.2 ∣ m ∧ Nat.Coprime t.2.1 t.2.2) := by
  ext t
  simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hg,hgm⟩,⟨⟨hr,hrm⟩,⟨hs,hsm⟩⟩⟩,hdvd,hcop⟩
    exact ⟨⟨⟨hg,hgm.trans hmB⟩,⟨⟨hr,hrm.trans hmB⟩,⟨hs,hsm.trans hmB⟩⟩⟩,hdvd,hcop⟩
  · rintro ⟨⟨⟨hg,hgB⟩,⟨⟨hr,hrB⟩,⟨hs,hsB⟩⟩⟩,hdvd,hcop⟩
    have hgdiv : t.1 ∣ m := (dvd_mul_of_dvd_left (dvd_mul_right t.1 t.2.1) t.2.2).trans hdvd
    have hrdiv : t.2.1 ∣ m := (dvd_mul_of_dvd_left (dvd_mul_left t.2.1 t.1) t.2.2).trans hdvd
    have hsdiv : t.2.2 ∣ m := (dvd_mul_left t.2.2 (t.1*t.2.1)).trans hdvd
    exact ⟨⟨⟨hg,Nat.le_of_dvd hm hgdiv⟩,⟨⟨hr,Nat.le_of_dvd hm hrdiv⟩,⟨hs,Nat.le_of_dvd hm hsdiv⟩⟩⟩,hdvd,hcop⟩

theorem interval_divisor_pair_gcd_reindex (A B : ℕ) (F : ℕ → ℕ → ℕ → ℝ) :
    (∑ m ∈ Finset.Ioc A B,∑ d ∈ m.divisors,∑ e ∈ m.divisors,F m d e)=
      ∑ t ∈ ((Finset.Icc 1 B)×ˢ((Finset.Icc 1 B)×ˢ(Finset.Icc 1 B))),
        if Nat.Coprime t.2.1 t.2.2 then
          ∑ l ∈ Finset.Icc 1 B,if A<t.1*t.2.1*t.2.2*l ∧ t.1*t.2.1*t.2.2*l≤B then
            F (t.1*t.2.1*t.2.2*l) (t.1*t.2.1) (t.1*t.2.2) else 0 else 0 := by
  have hp (m : ℕ) (hm : m∈Finset.Ioc A B) :
      (∑ d ∈ m.divisors,∑ e ∈ m.divisors,F m d e)=
        ∑ t ∈ ((Finset.Icc 1 B)×ˢ((Finset.Icc 1 B)×ˢ(Finset.Icc 1 B))),
          if t.1*t.2.1*t.2.2 ∣ m ∧ Nat.Coprime t.2.1 t.2.2 then F m (t.1*t.2.1) (t.1*t.2.2) else 0 := by
    have hmpos : 0<m := by have h := (Finset.mem_Ioc.mp hm).1;omega
    rw [divisor_pair_gcd_reindex m hmpos,divisor_gcd_triple_cap_eq m B hmpos (Finset.mem_Ioc.mp hm).2,Finset.sum_filter]
  rw [Finset.sum_congr rfl hp,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hmem := Finset.mem_product.mp ht
  have hg := (Finset.mem_Icc.mp hmem.1).1
  have hr := (Finset.mem_Icc.mp (Finset.mem_product.mp hmem.2).1).1
  have hs := (Finset.mem_Icc.mp (Finset.mem_product.mp hmem.2).2).1
  by_cases hc : Nat.Coprime t.2.1 t.2.2
  · rw [if_pos hc]
    have hpoint (m : ℕ) :
        (if t.1*t.2.1*t.2.2 ∣ m ∧ Nat.Coprime t.2.1 t.2.2 then F m (t.1*t.2.1) (t.1*t.2.2) else 0)=
        (if t.1*t.2.1*t.2.2 ∣ m then F m (t.1*t.2.1) (t.1*t.2.2) else 0) := by
      by_cases hd : t.1*t.2.1*t.2.2 ∣ m
      · rw [if_pos ⟨hd,hc⟩,if_pos hd]
      · rw [if_neg (fun h => hd h.1),if_neg hd]
    simp_rw [hpoint]
    exact interval_multiples_sum A B _ (Nat.mul_pos (Nat.mul_pos hg hr) hs) (fun m => F m (t.1*t.2.1) (t.1*t.2.2))
  · simp [hc]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma actual_vaughan_mobius_coefficient_large_divisors (U m : ℕ) :
    (arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m=
      ∑ d ∈ m.divisors,if U<d then ((moebius d : ℤ) : ℝ) else 0 := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_congr rfl
  intro d hd
  change ((moebius d : ℤ) : ℝ)-(if d≤U then ((moebius d : ℤ) : ℝ) else 0)=_
  by_cases h : d≤U
  · simp [h,show ¬U<d by omega]
  · simp [h,show U<d by omega]

theorem actual_vaughan_mobius_gcd_square (U m : ℕ) (hm : 0<m) :
    ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2=
      ∑ t ∈ ((Finset.Icc 1 m)×ˢ((Finset.Icc 1 m)×ˢ(Finset.Icc 1 m))).filter
        (fun t : ℕ×(ℕ×ℕ) => t.1*t.2.1*t.2.2 ∣ m ∧ Nat.Coprime t.2.1 t.2.2),
        if U<t.1*t.2.1 ∧ U<t.1*t.2.2 ∧ Nat.Coprime t.1 (t.2.1*t.2.2) then
          ((moebius t.1 : ℤ) : ℝ)^2*((moebius t.2.1 : ℤ) : ℝ)*((moebius t.2.2 : ℤ) : ℝ) else 0 := by
  rw [actual_vaughan_mobius_coefficient_large_divisors]
  exact moebius_large_divisor_square_gcd_reindex U m hm

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem actual_vaughan_mobius_interval_gcd_energy (U A B v : ℕ) :
    (∑ m ∈ Finset.Ioc A B,if Nat.Coprime m v then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)=
      ∑ t ∈ ((Finset.Icc 1 B)×ˢ((Finset.Icc 1 B)×ˢ(Finset.Icc 1 B))),
        if Nat.Coprime t.2.1 t.2.2 then
          ∑ s ∈ Finset.Icc 1 B,
            if A<t.1*t.2.1*t.2.2*s ∧ t.1*t.2.1*t.2.2*s≤B ∧
                Nat.Coprime (t.1*t.2.1*t.2.2*s) v ∧ U<t.1*t.2.1 ∧ U<t.1*t.2.2 ∧
                Nat.Coprime t.1 (t.2.1*t.2.2) then
              ((moebius t.1 : ℤ) : ℝ)^2*((moebius t.2.1 : ℤ) : ℝ)*((moebius t.2.2 : ℤ) : ℝ) else 0 else 0 := by
  let F : ℕ → ℕ → ℕ → ℝ := fun m d e => if Nat.Coprime m v then
      (if U<d then ((moebius d : ℤ) : ℝ) else 0)*(if U<e then ((moebius e : ℤ) : ℝ) else 0) else 0
  have hp (m : ℕ) :
      (if Nat.Coprime m v then
        ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)=
        ∑ d ∈ m.divisors,∑ e ∈ m.divisors,F m d e := by
    by_cases hc : Nat.Coprime m v
    · rw [if_pos hc,actual_vaughan_mobius_coefficient_large_divisors,pow_two,Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      exact (if_pos hc).symm
    · simp only [if_neg hc]
      symm
      apply Finset.sum_eq_zero
      intro d hd
      apply Finset.sum_eq_zero
      intro e he
      exact if_neg hc
  rw [Finset.sum_congr rfl (fun m hm => hp m),interval_divisor_pair_gcd_reindex A B F]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hcop : Nat.Coprime t.2.1 t.2.2
  · rw [if_pos hcop,if_pos hcop]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hb : A<t.1*t.2.1*t.2.2*s ∧ t.1*t.2.1*t.2.2*s≤B
    · rw [if_pos hb]
      dsimp [F]
      by_cases hv : Nat.Coprime (t.1*t.2.1*t.2.2*s) v <;>
        by_cases hr : U<t.1*t.2.1 <;> by_cases ht' : U<t.1*t.2.2 <;>
        by_cases hg : Nat.Coprime t.1 (t.2.1*t.2.2)
      all_goals simp [hb,hv,hr,ht',hg,moebius_common_factor_product]
      all_goals split_ifs <;> aesop
    · rw [if_neg hb]
      have hnot : ¬(A<t.1*t.2.1*t.2.2*s ∧ t.1*t.2.1*t.2.2*s≤B ∧
          Nat.Coprime (t.1*t.2.1*t.2.2*s) v ∧ U<t.1*t.2.1 ∧ U<t.1*t.2.2 ∧
          Nat.Coprime t.1 (t.2.1*t.2.2)) := fun h => hb ⟨h.1,h.2.1⟩
      rw [if_neg hnot]
  · rw [if_neg hcop,if_neg hcop]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma four_finite_sum_rotate (S : Finset ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ g ∈ S,∑ r ∈ S,∑ t ∈ S,∑ s ∈ S,F g r t s)=
      ∑ s ∈ S,∑ r ∈ S,∑ t ∈ S,∑ g ∈ S,F g r t s := by
  calc
    _=∑ r ∈ S,∑ g ∈ S,∑ t ∈ S,∑ s ∈ S,F g r t s := Finset.sum_comm
    _=∑ r ∈ S,∑ t ∈ S,∑ g ∈ S,∑ s ∈ S,F g r t s := by
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_comm
    _=∑ r ∈ S,∑ t ∈ S,∑ s ∈ S,∑ g ∈ S,F g r t s := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro t ht
      exact Finset.sum_comm
    _=∑ r ∈ S,∑ s ∈ S,∑ t ∈ S,∑ g ∈ S,F g r t s := by
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_comm
    _=_ := Finset.sum_comm

lemma finite_sum_product_cutoff (B k : ℕ) (hk : 0<k) (F : ℕ → ℝ) :
    (∑ g ∈ Finset.Icc 1 B,if g*k≤B then F g else 0)=∑ g ∈ Finset.Icc 1 (B/k),F g := by
  rw [←Finset.sum_filter]
  have hi : (Finset.Icc 1 B).filter (fun g => g*k≤B)=Finset.Icc 1 (B/k) := by
    ext g
    simp only [Finset.mem_filter,Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hg,hgB⟩,hprod⟩
      exact ⟨hg,(Nat.le_div_iff_mul_le hk).mpr hprod⟩
    · rintro ⟨hg,hgdiv⟩
      exact ⟨⟨hg,hgdiv.trans (Nat.div_le_self B k)⟩,(Nat.le_div_iff_mul_le hk).mp hgdiv⟩
  rw [hi]

lemma finite_sum_interval_product_cutoff (A B k : ℕ) (hk : 0<k) (P : ℕ → Prop) (F : ℕ → ℝ) :
    (∑ g ∈ Finset.Icc 1 B,if A<g*k ∧ g*k≤B ∧ P g then F g else 0)=
      ∑ g ∈ Finset.Icc 1 (B/k),if A<g*k ∧ P g then F g else 0 := by
  have he (g : ℕ) :
      (if A<g*k ∧ g*k≤B ∧ P g then F g else 0)=
      if g*k≤B then (if A<g*k ∧ P g then F g else 0) else 0 := by
    by_cases hb : g*k≤B <;> simp [hb]
  rw [Finset.sum_congr rfl (fun g hg => he g),finite_sum_product_cutoff B k hk]

lemma vaughan_coprime_factor_rearrange (g r t s v : ℕ) :
    (Nat.Coprime (g*r*t*s) v ∧ Nat.Coprime g (r*t)) ↔
      (Nat.Coprime (r*t*s) v ∧ Nat.Coprime g (r*t*v)) := by
  simp only [Nat.coprime_mul_iff_left,Nat.coprime_mul_iff_right]
  tauto

theorem actual_vaughan_squarefree_interval_reduction (U A B v : ℕ) :
    (∑ m ∈ Finset.Ioc A B,if Nat.Coprime m v then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)=
      ∑ s ∈ Finset.Icc 1 B,∑ r ∈ Finset.Icc 1 B,∑ t ∈ Finset.Icc 1 B,
        if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
          ((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
            (∑ g ∈ Finset.Icc 1 (B/(r*t*s)),
              if A<g*r*t*s ∧ U<g*r ∧ U<g*t ∧ Nat.Coprime g (r*t*v) then ((moebius g : ℤ) : ℝ)^2 else 0) else 0 := by
  let F : ℕ → ℕ → ℕ → ℕ → ℝ := fun g r t s => if Nat.Coprime r t then
    (if A<g*r*t*s ∧ g*r*t*s≤B ∧ Nat.Coprime (g*r*t*s) v ∧ U<g*r ∧ U<g*t ∧ Nat.Coprime g (r*t) then
      ((moebius g : ℤ) : ℝ)^2*((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ) else 0) else 0
  have hquad :
      (∑ m ∈ Finset.Ioc A B,if Nat.Coprime m v then
        ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)=
        ∑ g ∈ Finset.Icc 1 B,∑ r ∈ Finset.Icc 1 B,∑ t ∈ Finset.Icc 1 B,∑ s ∈ Finset.Icc 1 B,F g r t s := by
    rw [actual_vaughan_mobius_interval_gcd_energy,Finset.sum_product]
    apply Finset.sum_congr rfl
    intro g hg
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hc : Nat.Coprime r t
    · rw [if_pos hc]
      apply Finset.sum_congr rfl
      intro s hs
      exact (if_pos hc).symm
    · rw [if_neg hc]
      symm
      apply Finset.sum_eq_zero
      intro s hs
      exact if_neg hc
  rw [hquad,four_finite_sum_rotate]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro t ht
  have hspos := (Finset.mem_Icc.mp hs).1
  have hrpos := (Finset.mem_Icc.mp hr).1
  have htpos := (Finset.mem_Icc.mp ht).1
  have hk : 0<r*t*s := Nat.mul_pos (Nat.mul_pos hrpos htpos) hspos
  by_cases hc : Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v
  · rw [if_pos hc]
    have hsum : (∑ g ∈ Finset.Icc 1 B,F g r t s)=
        ((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
          (∑ g ∈ Finset.Icc 1 B,if A<g*r*t*s ∧ g*r*t*s≤B ∧ U<g*r ∧ U<g*t ∧ Nat.Coprime g (r*t*v) then
            ((moebius g : ℤ) : ℝ)^2 else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g hg
      dsimp [F]
      rw [if_pos hc.1]
      have hiff : (A<g*r*t*s ∧ g*r*t*s≤B ∧ Nat.Coprime (g*r*t*s) v ∧ U<g*r ∧ U<g*t ∧ Nat.Coprime g (r*t)) ↔
          (A<g*r*t*s ∧ g*r*t*s≤B ∧ U<g*r ∧ U<g*t ∧ Nat.Coprime g (r*t*v)) := by
        have he := vaughan_coprime_factor_rearrange g r t s v
        tauto
      by_cases hgood : A<g*r*t*s ∧ g*r*t*s≤B ∧ U<g*r ∧ U<g*t ∧ Nat.Coprime g (r*t*v)
      · rw [if_pos (hiff.mpr hgood),if_pos hgood]
        ring
      · rw [if_neg (fun h => hgood (hiff.mp h)),if_neg hgood,mul_zero]
    rw [hsum]
    congr 1
    simpa only [mul_assoc] using finite_sum_interval_product_cutoff A B (r*t*s) hk
      (fun g => U<g*r ∧ U<g*t ∧ Nat.Coprime g (r*t*v)) (fun g => ((moebius g : ℤ) : ℝ)^2)
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro g hg
    dsimp [F]
    by_cases hrt : Nat.Coprime r t
    · rw [if_pos hrt]
      have hnot : ¬(A<g*r*t*s ∧ g*r*t*s≤B ∧ Nat.Coprime (g*r*t*s) v ∧ U<g*r ∧ U<g*t ∧ Nat.Coprime g (r*t)) := by
        intro h
        have hcop := (vaughan_coprime_factor_rearrange g r t s v).mp ⟨h.2.2.1,h.2.2.2.2.2⟩
        exact hc ⟨hrt,hcop.1⟩
      rw [if_neg hnot]
    · rw [if_neg hrt]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 3200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma vaughan_large_divisor_product_support (U B g r t s : ℕ)
    (hg : 1≤g) (hr : 1≤r) (ht : 1≤t) (hs : 1≤s)
    (hprod : g*r*t*s≤B) (hUr : U<g*r) (hUt : U<g*t) :
    s≤B/(U+1) ∧ r≤B/((U+1)*s) ∧ t≤B/((U+1)*s) := by
  have hrprod : r*((U+1)*s)≤B := by
    calc
      _=(r*s)*(U+1) := by ring
      _≤(r*s)*(g*t) := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hUt)
      _=g*r*t*s := by ring
      _≤B := hprod
  have htprod : t*((U+1)*s)≤B := by
    calc
      _=(t*s)*(U+1) := by ring
      _≤(t*s)*(g*r) := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hUr)
      _=g*r*t*s := by ring
      _≤B := hprod
  have hsprod : s*(U+1)≤B := by
    calc
      _=1*((U+1)*s) := by ring
      _≤r*((U+1)*s) := Nat.mul_le_mul_right _ hr
      _≤B := hrprod
  exact ⟨(Nat.le_div_iff_mul_le (Nat.succ_pos U)).mpr hsprod,
    (Nat.le_div_iff_mul_le (Nat.mul_pos (Nat.succ_pos U) hs)).mpr hrprod,
    (Nat.le_div_iff_mul_le (Nat.mul_pos (Nat.succ_pos U) hs)).mpr htprod⟩

theorem actual_vaughan_squarefree_small_interval_reduction (U A B v : ℕ) :
    (∑ m ∈ Finset.Ioc A B,if Nat.Coprime m v then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)=
      ∑ s ∈ Finset.Icc 1 (B/(U+1)),
        ∑ r ∈ Finset.Icc 1 (B/((U+1)*s)),∑ t ∈ Finset.Icc 1 (B/((U+1)*s)),
          if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
            ((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
              (∑ g ∈ Finset.Icc 1 (B/(r*t*s)),
                if A<g*r*t*s ∧ U<g*r ∧ U<g*t ∧ Nat.Coprime g (r*t*v) then ((moebius g : ℤ) : ℝ)^2 else 0) else 0 := by
  let F : ℕ → ℕ → ℕ → ℝ := fun s r t =>
    if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
      ((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
        (∑ g ∈ Finset.Icc 1 (B/(r*t*s)),
          if A<g*r*t*s ∧ U<g*r ∧ U<g*t ∧ Nat.Coprime g (r*t*v) then ((moebius g : ℤ) : ℝ)^2 else 0) else 0
  have hzero (s r t : ℕ) (hs : 1≤s) (hr : 1≤r) (ht : 1≤t)
      (hout : ¬(s≤B/(U+1) ∧ r≤B/((U+1)*s) ∧ t≤B/((U+1)*s))) : F s r t=0 := by
    dsimp [F]
    by_cases hc : Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v
    · rw [if_pos hc]
      have hinner : (∑ g ∈ Finset.Icc 1 (B/(r*t*s)),
          if A<g*r*t*s ∧ U<g*r ∧ U<g*t ∧ Nat.Coprime g (r*t*v) then ((moebius g : ℤ) : ℝ)^2 else 0)=0 := by
        apply Finset.sum_eq_zero
        intro g hg
        by_cases hgood : A<g*r*t*s ∧ U<g*r ∧ U<g*t ∧ Nat.Coprime g (r*t*v)
        · have hk : 0<r*t*s := Nat.mul_pos (Nat.mul_pos hr ht) hs
          have hprod : g*r*t*s≤B := by
            simpa only [mul_assoc] using (Nat.le_div_iff_mul_le hk).mp (Finset.mem_Icc.mp hg).2
          exact False.elim (hout (vaughan_large_divisor_product_support U B g r t s (Finset.mem_Icc.mp hg).1 hr ht hs hprod hgood.2.1 hgood.2.2.1))
        · exact if_neg hgood
      rw [hinner,mul_zero]
    · rw [if_neg hc]
  rw [actual_vaughan_squarefree_interval_reduction]
  change (∑ s ∈ Finset.Icc 1 B,∑ r ∈ Finset.Icc 1 B,∑ t ∈ Finset.Icc 1 B,F s r t)=
    ∑ s ∈ Finset.Icc 1 (B/(U+1)),∑ r ∈ Finset.Icc 1 (B/((U+1)*s)),∑ t ∈ Finset.Icc 1 (B/((U+1)*s)),F s r t
  have hcapS : (∑ s ∈ Finset.Icc 1 B,∑ r ∈ Finset.Icc 1 B,∑ t ∈ Finset.Icc 1 B,F s r t)=
      ∑ s ∈ Finset.Icc 1 (B/(U+1)),∑ r ∈ Finset.Icc 1 B,∑ t ∈ Finset.Icc 1 B,F s r t := by
    symm
    apply Finset.sum_subset
    · intro s hs
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hs).1,(Finset.mem_Icc.mp hs).2.trans (Nat.div_le_self B _)⟩
    · intro s hs hnot
      apply Finset.sum_eq_zero
      intro r hr
      apply Finset.sum_eq_zero
      intro t ht
      apply hzero s r t (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp ht).1
      intro hc
      exact hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hs).1,hc.1⟩)
  rw [hcapS]
  apply Finset.sum_congr rfl
  intro s hs
  have hcapR : (∑ r ∈ Finset.Icc 1 B,∑ t ∈ Finset.Icc 1 B,F s r t)=
      ∑ r ∈ Finset.Icc 1 (B/((U+1)*s)),∑ t ∈ Finset.Icc 1 B,F s r t := by
    symm
    apply Finset.sum_subset
    · intro r hr
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,(Finset.mem_Icc.mp hr).2.trans (Nat.div_le_self B _)⟩
    · intro r hr hnot
      apply Finset.sum_eq_zero
      intro t ht
      apply hzero s r t (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp ht).1
      intro hc
      exact hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,hc.2.1⟩)
  rw [hcapR]
  apply Finset.sum_congr rfl
  intro r hr
  symm
  apply Finset.sum_subset
  · intro t ht
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ht).1,(Finset.mem_Icc.mp ht).2.trans (Nat.div_le_self B _)⟩
  · intro t ht hnot
    apply hzero s r t (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp ht).1
    intro hc
    exact hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ht).1,hc.2.2⟩)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma finite_sum_positive_lower_cutoff (L H : ℕ) (F : ℕ → ℝ) :
    (∑ g ∈ Finset.Icc 1 H,if L<g then F g else 0)=∑ g ∈ Finset.Ioc L H,F g := by
  rw [←Finset.sum_filter]
  have hi : (Finset.Icc 1 H).filter (fun g => L<g)=Finset.Ioc L H := by
    ext g
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  rw [hi]

lemma vaughan_squarefree_inner_interval (U A B v r t s : ℕ) (hr : 1≤r) (ht : 1≤t) (hs : 1≤s) :
    (∑ g ∈ Finset.Icc 1 (B/(r*t*s)),
      if A<g*r*t*s ∧ U<g*r ∧ U<g*t ∧ Nat.Coprime g (r*t*v) then ((moebius g : ℤ) : ℝ)^2 else 0)=
    ∑ g ∈ Finset.Ioc (max (A/(r*t*s)) (max (U/r) (U/t))) (B/(r*t*s)),
      if Nat.Coprime g (r*t*v) then ((moebius g : ℤ) : ℝ)^2 else 0 := by
  have hk : 0<r*t*s := Nat.mul_pos (Nat.mul_pos hr ht) hs
  have hiff (g : ℕ) : (A<g*r*t*s ∧ U<g*r ∧ U<g*t ∧ Nat.Coprime g (r*t*v)) ↔
      (max (A/(r*t*s)) (max (U/r) (U/t))<g ∧ Nat.Coprime g (r*t*v)) := by
    rw [max_lt_iff,max_lt_iff,Nat.div_lt_iff_lt_mul hk,Nat.div_lt_iff_lt_mul hr,Nat.div_lt_iff_lt_mul ht]
    simp only [mul_assoc]
    tauto
  have he (g : ℕ) :
      (if A<g*r*t*s ∧ U<g*r ∧ U<g*t ∧ Nat.Coprime g (r*t*v) then ((moebius g : ℤ) : ℝ)^2 else 0)=
      if max (A/(r*t*s)) (max (U/r) (U/t))<g then
        (if Nat.Coprime g (r*t*v) then ((moebius g : ℤ) : ℝ)^2 else 0) else 0 := by
    by_cases hL : max (A/(r*t*s)) (max (U/r) (U/t))<g
    · rw [if_pos hL]
      by_cases hc : Nat.Coprime g (r*t*v)
      · rw [if_pos hc,if_pos ((hiff g).mpr ⟨hL,hc⟩)]
      · rw [if_neg hc,if_neg (fun h => hc ((hiff g).mp h).2)]
    · rw [if_neg hL,if_neg (fun h => hL ((hiff g).mp h).1)]
  rw [Finset.sum_congr rfl (fun g hg => he g),finite_sum_positive_lower_cutoff]

theorem actual_vaughan_squarefree_count_reduction (U A B v : ℕ) :
    (∑ m ∈ Finset.Ioc A B,if Nat.Coprime m v then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)=
      ∑ s ∈ Finset.Icc 1 (B/(U+1)),
        ∑ r ∈ Finset.Icc 1 (B/((U+1)*s)),∑ t ∈ Finset.Icc 1 (B/((U+1)*s)),
          if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
            ((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
              (∑ g ∈ Finset.Ioc (max (A/(r*t*s)) (max (U/r) (U/t))) (B/(r*t*s)),
                if Nat.Coprime g (r*t*v) then ((moebius g : ℤ) : ℝ)^2 else 0) else 0 := by
  rw [actual_vaughan_squarefree_small_interval_reduction]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro t ht
  rw [vaughan_squarefree_inner_interval U A B v r t s (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp hs).1]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2300000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

noncomputable def reciprocalSquareArithmetic : ArithmeticFunction ℝ :=
  ⟨fun n => 1/(n : ℝ)^2,by norm_num⟩

noncomputable def reciprocalFourthArithmetic : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul reciprocalSquareArithmetic reciprocalSquareArithmetic

noncomputable def squarefreeReciprocalSquareArithmetic : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul (ArithmeticFunction.pmul (moebius : ArithmeticFunction ℝ) (moebius : ArithmeticFunction ℝ)) reciprocalSquareArithmetic

lemma reciprocalSquareArithmetic_multiplicative : reciprocalSquareArithmetic.IsMultiplicative := by
  refine ⟨by norm_num [reciprocalSquareArithmetic],?_⟩
  intro m n hmn
  simp only [reciprocalSquareArithmetic,ArithmeticFunction.coe_mk,Nat.cast_mul,mul_pow,one_div,mul_inv_rev]
  ring

lemma reciprocalFourthArithmetic_multiplicative : reciprocalFourthArithmetic.IsMultiplicative :=
  reciprocalSquareArithmetic_multiplicative.pmul reciprocalSquareArithmetic_multiplicative

lemma squarefreeReciprocalSquareArithmetic_multiplicative : squarefreeReciprocalSquareArithmetic.IsMultiplicative :=
  (isMultiplicative_moebius.intCast.pmul isMultiplicative_moebius.intCast).pmul reciprocalSquareArithmetic_multiplicative

lemma reciprocalFourthArithmetic_value (n : ℕ) : reciprocalFourthArithmetic n=1/(n : ℝ)^4 := by
  change (1/(n : ℝ)^2)*(1/(n : ℝ)^2)=1/(n : ℝ)^4
  ring

lemma squarefreeReciprocalSquareArithmetic_value (n : ℕ) :
    squarefreeReciprocalSquareArithmetic n=((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 := by
  change (((moebius n : ℤ) : ℝ)*((moebius n : ℤ) : ℝ))*(1/(n : ℝ)^2)=((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2
  ring

lemma reciprocalSquareArithmetic_norm_summable : Summable (fun n : ℕ => ‖reciprocalSquareArithmetic n‖) := by
  have he (n : ℕ) : ‖reciprocalSquareArithmetic n‖=1/(n : ℝ)^2 := by
    change ‖1/(n : ℝ)^2‖=1/(n : ℝ)^2
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  simpa only [he] using hasSum_zeta_two.summable

lemma reciprocalFourthArithmetic_norm_summable : Summable (fun n : ℕ => ‖reciprocalFourthArithmetic n‖) := by
  simpa [reciprocalFourthArithmetic_value,Real.norm_eq_abs] using hasSum_zeta_four.summable

lemma squarefreeReciprocalSquareArithmetic_norm_summable : Summable (fun n : ℕ => ‖squarefreeReciprocalSquareArithmetic n‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hasSum_zeta_two.summable
  intro n
  rw [squarefreeReciprocalSquareArithmetic_value,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hmu : ((moebius n : ℤ) : ℝ)^2≤1 := by
    rcases moebius_eq_or n with h|h|h <;> rw [h] <;> norm_num
  exact div_le_div_of_nonneg_right hmu (sq_nonneg _)

lemma reciprocalSquareArithmetic_prime_power (p k : ℕ) :
    reciprocalSquareArithmetic (p^k)=(1/(p : ℝ)^2)^k := by
  simp only [reciprocalSquareArithmetic,ArithmeticFunction.coe_mk,Nat.cast_pow,one_div,inv_pow,←pow_mul,mul_comm]

lemma reciprocalFourthArithmetic_prime_power (p k : ℕ) :
    reciprocalFourthArithmetic (p^k)=(1/(p : ℝ)^4)^k := by
  simp only [reciprocalFourthArithmetic_value,Nat.cast_pow,one_div,inv_pow,←pow_mul,mul_comm]

lemma squarefreeReciprocalSquareArithmetic_prime_power_tsum (p : ℕ) (hp : Nat.Prime p) :
    (∑' k : ℕ,squarefreeReciprocalSquareArithmetic (p^k))=1+1/(p : ℝ)^2 := by
  have hz (k : ℕ) (hk : k∉Finset.range 2) : squarefreeReciprocalSquareArithmetic (p^k)=0 := by
    have hk2 : 2≤k := by simp only [Finset.mem_range] at hk;omega
    rw [squarefreeReciprocalSquareArithmetic_value,moebius_apply_prime_pow hp (by omega),if_neg (by omega)]
    norm_num
  rw [tsum_eq_sum hz]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    squarefreeReciprocalSquareArithmetic_value,moebius_apply_one,moebius_apply_prime hp]
  norm_num

lemma reciprocal_power_local_lt_one (p k : ℕ) (hp : Nat.Prime p) (hk : 1≤k) :
    |1/(p : ℝ)^k|<1 := by
  have hp2 : (2 : ℝ)≤p := by exact_mod_cast hp.two_le
  have hpow : (1 : ℝ)<(p : ℝ)^k := one_lt_pow₀ (by linarith) (by omega)
  rw [abs_of_nonneg (by positivity)]
  exact (div_lt_one (by positivity)).mpr hpow

theorem squarefree_reciprocal_square_series :
    (∑' n : ℕ,((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2)=15/Real.pi^2 := by
  have hf := squarefreeReciprocalSquareArithmetic_multiplicative.eulerProduct_hasProd squarefreeReciprocalSquareArithmetic_norm_summable
  have hg := reciprocalFourthArithmetic_multiplicative.eulerProduct_hasProd reciprocalFourthArithmetic_norm_summable
  have hh := reciprocalSquareArithmetic_multiplicative.eulerProduct_hasProd reciprocalSquareArithmetic_norm_summable
  have hloc (p : Nat.Primes) :
      (∑' k : ℕ,squarefreeReciprocalSquareArithmetic ((p : ℕ)^k))*(∑' k : ℕ,reciprocalFourthArithmetic ((p : ℕ)^k)) =
        ∑' k : ℕ,reciprocalSquareArithmetic ((p : ℕ)^k) := by
    rw [squarefreeReciprocalSquareArithmetic_prime_power_tsum p p.property]
    simp_rw [reciprocalFourthArithmetic_prime_power,reciprocalSquareArithmetic_prime_power]
    rw [(hasSum_geometric_of_abs_lt_one (reciprocal_power_local_lt_one p 4 p.property (by norm_num))).tsum_eq,
      (hasSum_geometric_of_abs_lt_one (reciprocal_power_local_lt_one p 2 p.property (by norm_num))).tsum_eq]
    have hp2 : (2 : ℝ)≤(p : ℕ) := by exact_mod_cast p.property.two_le
    have hp0 : ((p : ℕ) : ℝ)≠0 := by linarith
    have hden2 : 1-1/((p : ℕ) : ℝ)^2≠0 := by
      have ht := reciprocal_power_local_lt_one p 2 p.property (by norm_num)
      rw [abs_of_nonneg (by positivity)] at ht
      linarith
    have hden4 : 1-1/((p : ℕ) : ℝ)^4≠0 := by
      have ht := reciprocal_power_local_lt_one p 4 p.property (by norm_num)
      rw [abs_of_nonneg (by positivity)] at ht
      linarith
    rw [←div_eq_mul_inv]
    apply (div_eq_iff hden4).mpr
    rw [mul_comm,←div_eq_mul_inv]
    apply (eq_div_iff hden2).mpr
    field_simp [hp0] <;> ring
  have hfg := hf.mul hg
  have he : (∑' n : ℕ,squarefreeReciprocalSquareArithmetic n)*(∑' n : ℕ,reciprocalFourthArithmetic n) =
      ∑' n : ℕ,reciprocalSquareArithmetic n := by
    have hfg' : HasProd (fun p : Nat.Primes => ∑' k : ℕ,reciprocalSquareArithmetic ((p : ℕ)^k))
        ((∑' n : ℕ,squarefreeReciprocalSquareArithmetic n)*(∑' n : ℕ,reciprocalFourthArithmetic n)) := by
      simpa only [hloc] using hfg
    exact hfg'.unique hh
  simp_rw [squarefreeReciprocalSquareArithmetic_value,reciprocalFourthArithmetic_value] at he
  change (∑' n : ℕ,((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2)*(∑' n : ℕ,1/(n : ℝ)^4) = ∑' n : ℕ,1/(n : ℝ)^2 at he
  rw [hasSum_zeta_four.tsum_eq,hasSum_zeta_two.tsum_eq] at he
  have hpi : Real.pi≠0 := Real.pi_ne_zero
  have h : (∑' n : ℕ,((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2)=(Real.pi^2/6)/(Real.pi^4/90) :=
    (eq_div_iff (by positivity)).mpr he
  rw [h]
  field_simp [hpi] <;> ring

theorem squarefree_reciprocal_square_series_le_152 :
    (∑' n : ℕ,((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2)≤(38/25 : ℝ) := by
  rw [squarefree_reciprocal_square_series]
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<Real.pi^2)).mpr
  nlinarith [Real.pi_gt_d4,Real.pi_pos]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma principal_character_nat_value (q n : ℕ) :
    (1 : DirichletCharacter ℂ q) n = if Nat.Coprime n q then 1 else 0 := by
  by_cases hc : Nat.Coprime n q
  · rw [if_pos hc]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hc)
  · rw [if_neg hc]
    exact MulChar.map_nonunit _ (fun h => hc ((ZMod.isUnit_iff_coprime n q).mp h))

lemma principal_LSeries_at_two (q : ℕ) (hq : q ≠ 0) :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) 2 =
      ((Real.pi : ℂ)^2/6)*∏ p ∈ q.primeFactors,(1-1/(p : ℂ)^2) := by
  letI : NeZero q := ⟨hq⟩
  have h := DirichletCharacter.LSeries_changeLevel (Nat.one_dvd q)
    (1 : DirichletCharacter ℂ 1) (s:=2) (by norm_num)
  rw [DirichletCharacter.changeLevel_one,DirichletCharacter.LSeries_modOne_eq,
    LSeries_one_eq_riemannZeta (by norm_num),riemannZeta_two] at h
  rw [h]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [principal_character_nat_value]
  try simp only [Nat.coprime_one_right,if_true,one_mul]
  rw [Complex.cpow_neg]
  norm_num [Complex.cpow_natCast]

lemma principal_moebius_LSeries_at_two (q : ℕ) :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (moebius n : ℂ)) 2 =
      ((∑' n : ℕ,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) : ℂ) := by
  rw [LSeries]
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · subst n
    simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn,principal_character_nat_value]
    norm_num [Complex.cpow_natCast]
    split_ifs <;> push_cast <;> ring

theorem squarefree_coprime_density_series (q : ℕ) (hq : q ≠ 0) :
    (∑' n : ℕ,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) =
      (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹ := by
  have h := DirichletCharacter.LSeries.mul_mu_eq_one (1 : DirichletCharacter ℂ q) (s:=2) (by norm_num)
  change LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) 2 *
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (moebius n : ℂ)) 2 = 1 at h
  rw [principal_LSeries_at_two q hq,principal_moebius_LSeries_at_two] at h
  have hr : ((Real.pi^2/6)*(∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)))*
      (∑' n : ℕ,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) = 1 := by
    apply Complex.ofReal_injective
    push_cast
    simpa only [apply_ite,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_intCast,Complex.ofReal_natCast,Complex.ofReal_zero] using h
  have hp0 : (∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hsq : (1 : ℝ)<(p : ℝ)^2 := by nlinarith
    have hinv : 1/(p : ℝ)^2 < 1 := (div_lt_one (by positivity)).mpr hsq
    linarith
  rw [Finset.prod_inv_distrib]
  have hpi : Real.pi^2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  have hx : (∑' n : ℕ,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) =
      1/((Real.pi^2/6)*(∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2))) := by
    apply (eq_div_iff (mul_ne_zero (div_ne_zero hpi (by norm_num)) hp0)).mpr
    simpa only [mul_comm] using hr
  rw [hx]
  field_simp [hpi,hp0]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma shifted_reciprocal_square_sum_le (D K : ℕ) (hD : 1≤D) :
    (∑ n ∈ Finset.range K,1/((n+D+1 : ℕ) : ℝ)^2) ≤ 1/(D : ℝ) := by
  have hpoint (n : ℕ) : 1/((n+D+1 : ℕ) : ℝ)^2 ≤
      1/((n+D : ℕ) : ℝ)-1/((n+D+1 : ℕ) : ℝ) := by
    have hpos : (0 : ℝ)<((n+D : ℕ) : ℝ) := by exact_mod_cast (show 0<n+D by omega)
    push_cast
    field_simp
    nlinarith
  calc
    _ ≤ ∑ n ∈ Finset.range K,(1/((n+D : ℕ) : ℝ)-1/((n+D+1 : ℕ) : ℝ)) := Finset.sum_le_sum (fun n hn => hpoint n)
    _ = 1/(D : ℝ)-1/((K+D : ℕ) : ℝ) := by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,add_assoc,add_comm,add_left_comm] using Finset.sum_range_sub' (fun n : ℕ => 1/((n+D : ℕ) : ℝ)) K
    _ ≤ _ := sub_le_self _ (by positivity)

lemma shifted_reciprocal_square_tsum_le (D : ℕ) (hD : 1≤D) :
    (∑' n : ℕ,1/((n+D+1 : ℕ) : ℝ)^2) ≤ 1/(D : ℝ) :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) (fun K => shifted_reciprocal_square_sum_le D K hD)

lemma coprime_moebius_reciprocal_square_norm_le (q n : ℕ) :
    ‖(if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0)‖ ≤ 1/(n : ℝ)^2 := by
  by_cases hc : Nat.Coprime n q
  · rw [if_pos hc,Real.norm_eq_abs,abs_div]
    rw [show |(n : ℝ)^2| = (n : ℝ)^2 from abs_of_nonneg (sq_nonneg _)]
    exact div_le_div_of_nonneg_right (by exact_mod_cast abs_moebius_le_one (n:=n)) (sq_nonneg _)
  · rw [if_neg hc,norm_zero]
    positivity

lemma coprime_moebius_reciprocal_square_summable (q : ℕ) :
    Summable (fun n : ℕ => if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) := by
  exact Summable.of_norm_bounded hasSum_zeta_two.summable (fun n => coprime_moebius_reciprocal_square_norm_le q n)

lemma reciprocal_square_tsum_le_two : (∑' n : ℕ,1/(n : ℝ)^2) ≤ 2 := by
  have h := hasSum_zeta_two.summable.sum_add_tsum_nat_add 2
  norm_num [Finset.sum_range_succ] at h
  have ht := shifted_reciprocal_square_tsum_le 1 (by norm_num)
  norm_num [add_assoc] at ht
  simp only [one_div]
  linarith

lemma coprime_moebius_density_norm_le_two (q : ℕ) (hq : q ≠ 0) :
    |(6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹| ≤ 2 := by
  rw [←squarefree_coprime_density_series q hq]
  have hf := coprime_moebius_reciprocal_square_summable q
  calc
    _ ≤ ∑' n : ℕ,‖if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n : ℕ,1/(n : ℝ)^2 := hf.norm.tsum_le_tsum
      (fun n => coprime_moebius_reciprocal_square_norm_le q n) hasSum_zeta_two.summable
    _ ≤ _ := reciprocal_square_tsum_le_two

theorem coprime_moebius_density_tail_error (q D : ℕ) (hq : q ≠ 0) (hD : 1≤D) :
    |(6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹-
      (∑ n ∈ Finset.Icc 1 D,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0)| ≤ 1/(D : ℝ) := by
  let f : ℕ → ℝ := fun n => if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0
  have hf : Summable f := coprime_moebius_reciprocal_square_summable q
  have hs : (∑ n ∈ Finset.range (D+1),f n) = ∑ n ∈ Finset.Icc 1 D,f n := by
    rw [Finset.range_eq_Ico]
    have he : Finset.Ico 0 (D+1) = insert 0 (Finset.Icc 1 D) := by ext n;simp;omega
    rw [he,Finset.sum_insert (by simp)]
    simp [f]
  rw [←squarefree_coprime_density_series q hq]
  change |(∑' n : ℕ,f n)-(∑ n ∈ Finset.Icc 1 D,f n)| ≤ _
  have he := hf.sum_add_tsum_nat_add (D+1)
  rw [hs] at he
  have herr : (∑' n : ℕ,f n)-(∑ n ∈ Finset.Icc 1 D,f n) = ∑' n : ℕ,f (n+(D+1)) := by linarith
  rw [herr]
  have htail : Summable (fun n : ℕ => f (n+(D+1))) := hf.comp_injective (fun n m h => by omega)
  have hnorm : Summable (fun n : ℕ => 1/((n+D+1 : ℕ) : ℝ)^2) :=
    hasSum_zeta_two.summable.comp_injective (fun n m h => by omega)
  calc
    _ ≤ ∑' n : ℕ,‖f (n+(D+1))‖ := by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm htail.norm
    _ ≤ ∑' n : ℕ,1/((n+D+1 : ℕ) : ℝ)^2 :=
      htail.norm.tsum_le_tsum (fun n => by simpa [f,Nat.add_assoc] using coprime_moebius_reciprocal_square_norm_le q (n+(D+1))) hnorm
    _ ≤ _ := shifted_reciprocal_square_tsum_le D hD

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real Set
open scoped BigOperators Classical

namespace Helfgott

lemma moebius_real_square_nonneg (n : ℕ) : 0 ≤ ((moebius n : ℤ) : ℝ)^2 := sq_nonneg _

lemma moebius_real_square_le_one (n : ℕ) : ((moebius n : ℤ) : ℝ)^2 ≤ 1 := by
  rcases moebius_eq_or n with h|h|h <;> rw [h] <;> norm_num

lemma moebius_real_square_eq_zero_four_dvd (n : ℕ) (hn : 4 ∣ n) :
    ((moebius n : ℤ) : ℝ)^2=0 := by
  have hs : ¬Squarefree n := by
    intro h
    have hunit : IsUnit (2 : ℕ) := h 2 (by simpa using hn)
    norm_num at hunit
  rw [moebius_eq_zero_of_not_squarefree hs]
  norm_num

lemma squarefree_count_le_three_quarters (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,((moebius n : ℤ) : ℝ)^2) ≤ 3/4*(N : ℝ)+1 := by
  have hp (n : ℕ) : ((moebius n : ℤ) : ℝ)^2 ≤ if 4 ∣ n then (0 : ℝ) else 1 := by
    by_cases hn : 4 ∣ n
    · simp only [if_pos hn,moebius_real_square_eq_zero_four_dvd n hn,le_refl]
    · simpa only [if_neg hn] using moebius_real_square_le_one n
  have hi : (∑ n ∈ Finset.Icc 1 N,if 4 ∣ n then (0 : ℝ) else 1) =
      (N : ℝ)-((N/4 : ℕ) : ℝ) := by
    have hcard : (Finset.Icc 1 N).filter (fun n => 4 ∣ n) =
        (Finset.range (N+1)).filter (fun n => n ≠ 0 ∧ 4 ∣ n) := by
      ext n
      simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_range]
      omega
    have he := Nat.card_multiples' N 4
    rw [←hcard] at he
    have ht := Finset.card_filter_add_card_filter_not (s:=Finset.Icc 1 N) (p:=fun n => 4 ∣ n)
    rw [he,Nat.card_Icc] at ht
    simp only [Finset.sum_ite,Finset.sum_const_zero,zero_add,Finset.sum_const, nsmul_eq_mul,mul_one]
    have h := congrArg (fun m : ℕ => (m : ℝ)) ht
    norm_num at h
    linarith
  have hrem := Nat.mod_lt N (by norm_num : (0 : ℕ)<4)
  have hdiv := Nat.mod_add_div N 4
  have h : (N : ℝ) = ((N%4 : ℕ) : ℝ)+4*((N/4 : ℕ) : ℝ) := by exact_mod_cast hdiv.symm
  have hr : (((N%4 : ℕ) : ℝ)) ≤ 4 := by exact_mod_cast (Nat.le_of_lt hrem)
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,if 4 ∣ n then (0 : ℝ) else 1 := Finset.sum_le_sum (fun n hn => hp n)
    _ = (N : ℝ)-((N/4 : ℕ) : ℝ) := hi
    _ ≤ _ := by linarith

lemma shifted_reciprocal_square_tsum_lower (K : ℕ) :
    1/((K+1 : ℕ) : ℝ) ≤ ∑' n : ℕ,1/((n+K+1 : ℕ) : ℝ)^2 := by
  have anti : AntitoneOn (fun t : ℝ => t^(-2 : ℝ)) (Set.Ici ((K+1 : ℕ) : ℝ)) := by
    intro a ha b hb hab
    have hpos : (0 : ℝ)<((K+1 : ℕ) : ℝ) := by positivity
    exact Real.rpow_le_rpow_of_nonpos (hpos.trans_le ha) hab (by norm_num)
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-2 : ℝ)) := by
    simpa using (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))
  have ht := anti.integral_le_tsum_comp_add (K+1) hs (fun t ht => Real.rpow_nonneg ((by positivity : (0 : ℝ)≤((K+1 : ℕ) : ℝ)).trans ht.le) _)
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by positivity : (0 : ℝ)<((K+1 : ℕ) : ℝ))] at ht
  norm_num [Real.rpow_neg,Real.rpow_two,Real.rpow_neg_one,one_div,Nat.add_assoc] at ht ⊢
  exact ht

lemma squarefree_reciprocal_tail_summable (N : ℕ) :
    Summable (fun n : ℕ => if N<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0) := by
  apply Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) ?_ hasSum_zeta_two.summable
  intro n
  split_ifs
  · exact div_le_div_of_nonneg_right (moebius_real_square_le_one n) (sq_nonneg _)
  · positivity

lemma reciprocal_square_tail_as_shift (N : ℕ) :
    (∑' n : ℕ,if N<n then 1/(n : ℝ)^2 else 0)=∑' n : ℕ,1/((n+N+1 : ℕ) : ℝ)^2 := by
  let f : ℕ → ℝ := fun n => if N<n then 1/(n : ℝ)^2 else 0
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le (fun n => by dsimp [f];split_ifs <;> positivity) ?_ hasSum_zeta_two.summable
    intro n
    dsimp [f]
    split_ifs <;> first | exact le_rfl | positivity
  have he := hf.sum_add_tsum_nat_add (N+1)
  have hz : ∑ n ∈ Finset.range (N+1),f n=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnn : n≤N := by have h := Finset.mem_range.mp hn;omega
    exact if_neg (by omega)
  rw [hz,zero_add] at he
  rw [←he]
  apply tsum_congr
  intro n
  simp only [f,if_pos (by omega : N<n+(N+1)),Nat.add_assoc]

theorem squarefree_reciprocal_tail_upper (N : ℕ) (hN : 1≤N) :
    (∑' n : ℕ,if N<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0) ≤
      1/(N : ℝ)-1/(16*((N/4+1 : ℕ) : ℝ)) := by
  let r : ℕ → ℝ := fun n => if N<n then (1-((moebius n : ℤ) : ℝ)^2)/(n : ℝ)^2 else 0
  have hn (n : ℕ) : 0≤r n := by dsimp [r];split_ifs <;> positivity [sub_nonneg.mpr (moebius_real_square_le_one n)]
  have hr : Summable r := by
    apply Summable.of_nonneg_of_le hn ?_ hasSum_zeta_two.summable
    intro n
    dsimp [r]
    split_ifs
    · exact div_le_div_of_nonneg_right (by nlinarith [moebius_real_square_nonneg n]) (sq_nonneg _)
    · positivity
  let sparseMap : ℕ → ℕ := fun k => 4*(k+N/4+1)
  have hi : Function.Injective sparseMap := by intro k l h;dsimp [sparseMap] at h;omega
  have hpoint (k : ℕ) : r (sparseMap k)=(1/16 : ℝ)*(1/((k+N/4+1 : ℕ) : ℝ)^2) := by
    have hd : 4 ∣ sparseMap k := by dsimp [sparseMap];exact dvd_mul_right _ _
    have hb : N<sparseMap k := by
      dsimp [sparseMap]
      have hm := Nat.mod_lt N (by norm_num : (0 : ℕ)<4)
      have he := Nat.mod_add_div N 4
      omega
    dsimp [r]
    rw [if_pos hb,moebius_real_square_eq_zero_four_dvd (sparseMap k) hd]
    simp only [sparseMap,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    simp only [mul_pow,one_div,mul_inv_rev]
    norm_num
    ring
  have hl := tsum_comp_le_tsum_of_inj hr hn hi
  simp only [Function.comp_def,hpoint,tsum_mul_left] at hl
  have ht := shifted_reciprocal_square_tsum_lower (N/4)
  have hlow : 1/(16*((N/4+1 : ℕ) : ℝ)) ≤ ∑' n : ℕ,r n := by
    have h := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ)≤1/16)
    calc _ = (1/16 : ℝ)*(1/((N/4+1 : ℕ) : ℝ)) := by ring
         _ ≤ _ := h.trans hl
  have hf := squarefree_reciprocal_tail_summable N
  have hadd := hf.tsum_add hr
  have he : (∑' n : ℕ,if N<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0)+(∑' n : ℕ,r n)=
      ∑' n : ℕ,1/((n+N+1 : ℕ) : ℝ)^2 := by
    rw [←reciprocal_square_tail_as_shift N,←hadd]
    apply tsum_congr
    intro n
    dsimp [r]
    split_ifs <;> ring
  have hup := shifted_reciprocal_square_tsum_le N hN
  linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 100000
open Finset Nat ArithmeticFunction
open scoped BigOperators

namespace Helfgott

def smoothSquarefreeCountRat (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc 1 N,if Squarefree n then (1 : ℚ) else 0

def smoothSquarefreePartialRat (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc 1 N,if Squarefree n then 1/(n : ℚ)^2 else 0

lemma squarefree_smooth_finite_certificate :
    ∀ N ∈ Finset.range 16,
      0≤(38/25 : ℚ)-smoothSquarefreePartialRat N ∧
      smoothSquarefreeCountRat N+(1/2 : ℚ)*(N : ℚ)^2*((38/25 : ℚ)-smoothSquarefreePartialRat N)≤(127/100 : ℚ)*N ∧
      smoothSquarefreeCountRat N+(1/2 : ℚ)*(N+1 : ℚ)^2*((38/25 : ℚ)-smoothSquarefreePartialRat N)≤(127/100 : ℚ)*(N+1) := by
  decide +kernel

lemma moebius_real_square_indicator (n : ℕ) :
    ((moebius n : ℤ) : ℝ)^2=if Squarefree n then (1 : ℝ) else 0 := by
  by_cases hn : Squarefree n
  · rw [if_pos hn]
    exact_mod_cast moebius_sq_eq_one_of_squarefree hn
  · rw [if_neg hn,moebius_eq_zero_of_not_squarefree hn]
    norm_num

lemma smoothSquarefreeCountRat_cast (N : ℕ) :
    (smoothSquarefreeCountRat N : ℝ)=∑ n ∈ Finset.Icc 1 N,((moebius n : ℤ) : ℝ)^2 := by
  unfold smoothSquarefreeCountRat
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  rw [moebius_real_square_indicator]
  split_ifs <;> norm_num

lemma smoothSquarefreePartialRat_cast (N : ℕ) :
    (smoothSquarefreePartialRat N : ℝ)=∑ n ∈ Finset.Icc 1 N,((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 := by
  unfold smoothSquarefreePartialRat
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  rw [moebius_real_square_indicator]
  split_ifs <;> norm_num

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma squarefree_reciprocal_tail_sub (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2)+
    (∑' n : ℕ,if N<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0) =
    ∑' n : ℕ,((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 := by
  let f : ℕ → ℝ := fun n => ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) ?_ hasSum_zeta_two.summable
    intro n
    exact div_le_div_of_nonneg_right (moebius_real_square_le_one n) (sq_nonneg _)
  have he := hf.sum_add_tsum_nat_add (N+1)
  have hs : (∑ n ∈ Finset.range (N+1),f n)=∑ n ∈ Finset.Icc 1 N,f n := by
    rw [Finset.range_eq_Ico]
    have hi : Finset.Ico 0 (N+1)=insert 0 (Finset.Icc 1 N) := by ext n;simp;omega
    rw [hi,Finset.sum_insert (by simp)]
    simp [f]
  rw [hs] at he
  have ht : (∑' n : ℕ,if N<n then f n else 0)=∑' n : ℕ,f (n+(N+1)) := by
    have hfi := squarefree_reciprocal_tail_summable N
    have het := hfi.sum_add_tsum_nat_add (N+1)
    have hz : (∑ n ∈ Finset.range (N+1),if N<n then f n else 0)=0 := by
      apply Finset.sum_eq_zero
      intro n hn
      exact if_neg (by have h := Finset.mem_range.mp hn;omega)
    rw [hz,zero_add] at het
    rw [←het]
    apply tsum_congr
    intro n
    rw [if_pos (by omega : N<n+(N+1))]
  change (∑ n ∈ Finset.Icc 1 N,f n)+(∑' n : ℕ,if N<n then f n else 0)=∑' n : ℕ,f n
  rw [ht]
  exact he

lemma squarefree_smooth_small (x : ℝ) (N : ℕ) (hN : N<16)
    (hlo : (N : ℝ)≤x) (hhi : x≤(N : ℝ)+1) :
    (∑ n ∈ Finset.Icc 1 N,((moebius n : ℤ) : ℝ)^2)+
    (x^2/2)*(∑' n : ℕ,if N<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0)≤(127/100 : ℝ)*x := by
  rcases squarefree_smooth_finite_certificate N (Finset.mem_range.mpr hN) with ⟨hc,ha,hb⟩
  let a : ℝ := smoothSquarefreeCountRat N
  let c : ℝ := (38/25 : ℝ)-smoothSquarefreePartialRat N
  have hc' : 0≤c := by
    have h := (Rat.cast_le (K:=ℝ)).mpr hc
    push_cast at h
    simpa [c] using h
  have ha' : a+(1/2 : ℝ)*(N : ℝ)^2*c≤(127/100 : ℝ)*N := by
    have h := (Rat.cast_le (K:=ℝ)).mpr ha
    push_cast at h
    simpa [a,c] using h
  have hb' : a+(1/2 : ℝ)*((N : ℝ)+1)^2*c≤(127/100 : ℝ)*((N : ℝ)+1) := by
    have h := (Rat.cast_le (K:=ℝ)).mpr hb
    push_cast at h
    simpa [a,c] using h
  have hqa : a+(1/2 : ℝ)*(N : ℝ)^2*c-(127/100 : ℝ)*N≤0 := by linarith
  have hqb : a+(1/2 : ℝ)*((N : ℝ)+1)^2*c-(127/100 : ℝ)*((N : ℝ)+1)≤0 := by linarith
  have hleft := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤(N : ℝ)+1-x) hqa
  have hright := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤x-(N : ℝ)) hqb
  have hquad : 0≤c*(x-(N : ℝ))*((N : ℝ)+1-x) := mul_nonneg (mul_nonneg hc' (by linarith)) (by linarith)
  have hpoly : a+(x^2/2)*c≤(127/100 : ℝ)*x := by nlinarith
  have htail := squarefree_reciprocal_tail_sub N
  have htotal := squarefree_reciprocal_square_series_le_152
  have hle : (∑' n : ℕ,if N<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0)≤c := by
    dsimp [c]
    rw [smoothSquarefreePartialRat_cast]
    linarith
  rw [←smoothSquarefreeCountRat_cast]
  have hm : (x^2/2)*(∑' n : ℕ,if N<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0)≤(x^2/2)*c :=
    mul_le_mul_of_nonneg_left hle (by positivity)
  exact (add_le_add_right hm a).trans (by simpa only [add_comm] using hpoly)

lemma squarefree_smooth_large (x : ℝ) (N : ℕ) (hx : 16≤x)
    (hlo : (N : ℝ)≤x) (hhi : x≤(N : ℝ)+1) :
    (∑ n ∈ Finset.Icc 1 N,((moebius n : ℤ) : ℝ)^2)+
    (x^2/2)*(∑' n : ℕ,if N<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0)≤(127/100 : ℝ)*x := by
  have hN : 1≤N := by
    by_contra h
    have he : N=0 := by omega
    norm_num [he] at hhi
    linarith
  have hNp : (0 : ℝ)<N := by exact_mod_cast hN
  have hx1 : 0<x-1 := by linarith
  have hx4 : 0<x+4 := by linarith
  have hdiv : 4*((N/4 : ℕ) : ℝ)≤(N : ℝ) := by exact_mod_cast (Nat.mul_div_le N 4)
  have hden : 16*((N/4+1 : ℕ) : ℝ)≤4*(x+4) := by push_cast;linarith
  have hupper := one_div_le_one_div_of_le hx1 (by linarith : x-1≤(N : ℝ))
  have hlower := one_div_le_one_div_of_le (by positivity : (0 : ℝ)<16*((N/4+1 : ℕ) : ℝ)) hden
  have ht : (∑' n : ℕ,if N<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0)≤1/(x-1)-1/(4*(x+4)) := by
    have h := squarefree_reciprocal_tail_upper N hN
    linarith
  have hc : (∑ n ∈ Finset.Icc 1 N,((moebius n : ℤ) : ℝ)^2)≤3/4*x+1 := by
    have h := squarefree_count_le_three_quarters N
    linarith
  have hid : (3/4 : ℝ)*x+1+(x^2/2)*(1/(x-1)-1/(4*(x+4)))=
      (9/8 : ℝ)*x+2+1/(2*(x-1))-2/(x+4) := by
    field_simp [hx1.ne',hx4.ne']
    ring
  have hsmall : 1/(2*(x-1))≤(1/30 : ℝ) := one_div_le_one_div_of_le (by norm_num) (by linarith)
  calc
    _ ≤ (3/4 : ℝ)*x+1+(x^2/2)*(1/(x-1)-1/(4*(x+4))) := add_le_add hc (mul_le_mul_of_nonneg_left ht (by positivity))
    _ = (9/8 : ℝ)*x+2+1/(2*(x-1))-2/(x+4) := hid
    _ ≤ (9/8 : ℝ)*x+2+1/30 := by
      have hp : 0≤2/(x+4) := by positivity
      linarith
    _ ≤ _ := by linarith

theorem squarefree_smoothed_count_le_127 (x : ℝ) (hx : 0≤x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,((moebius n : ℤ) : ℝ)^2)+
    (x^2/2)*(∑' n : ℕ,if ⌊x⌋₊<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0)≤(127/100 : ℝ)*x := by
  have hlo := Nat.floor_le hx
  have hhi := (Nat.lt_floor_add_one x).le
  by_cases h : 16≤x
  · exact squarefree_smooth_large x ⌊x⌋₊ h hlo hhi
  · have hN : ⌊x⌋₊<16 := by
      by_contra hN
      have hc : (16 : ℝ)≤⌊x⌋₊ := by exact_mod_cast (Nat.le_of_not_gt hN)
      linarith
    exact squarefree_smooth_small x ⌊x⌋₊ hN hlo hhi

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma floorRoot_two_eq_one_iff_squarefree (n : ℕ) (hn : n ≠ 0) :
    Nat.floorRoot 2 n = 1 ↔ Squarefree n := by
  constructor
  · intro hroot
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hdvd
    have h : p ∣ Nat.floorRoot 2 n := Nat.pow_dvd_iff_dvd_floorRoot.mp (by simpa [pow_two] using hdvd)
    rw [hroot] at h
    exact hp.ne_one (Nat.dvd_one.mp h)
  · intro hsf
    have h := hsf (Nat.floorRoot 2 n) (by simpa [pow_two] using Nat.floorRoot_pow_dvd (n:=2) (a:=n))
    exact Nat.isUnit_iff.mp h

lemma moebius_divisor_sum (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors,moebius d) = if n=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply,hn] using h

theorem moebius_square_divisor_expansion (n : ℕ) (hn : n ≠ 0) :
    (moebius n)^2 = ∑ d ∈ n.divisors,if d^2 ∣ n then moebius d else 0 := by
  have hroot0 : Nat.floorRoot 2 n ≠ 0 := Nat.floorRoot_ne_zero.mpr ⟨by norm_num,hn⟩
  have he : n.divisors.filter (fun d => d^2 ∣ n) = (Nat.floorRoot 2 n).divisors := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd,hn0⟩,hsq⟩
      exact ⟨Nat.pow_dvd_iff_dvd_floorRoot.mp hsq,hroot0⟩
    · rintro ⟨hd,hr0⟩
      have hsq := Nat.pow_dvd_iff_dvd_floorRoot.mpr hd
      exact ⟨⟨dvd_trans (dvd_pow_self d (by norm_num : 2 ≠ 0)) hsq,hn⟩,hsq⟩
  rw [←Finset.sum_filter,he,moebius_divisor_sum _ hroot0,moebius_sq]
  simp only [floorRoot_two_eq_one_iff_squarefree n hn]

lemma coprime_moebius_divisor_expansion (q n : ℕ) (hq : q ≠ 0) :
    (∑ e ∈ q.divisors,if e ∣ n then moebius e else 0) =
      if Nat.Coprime n q then 1 else 0 := by
  have he : q.divisors.filter (fun e => e ∣ n) = (Nat.gcd n q).divisors := by
    ext e
    simp only [Finset.mem_filter,Nat.mem_divisors]
    have hg : Nat.gcd n q ≠ 0 := Nat.gcd_ne_zero_right hq
    constructor
    · rintro ⟨⟨heq,hq0⟩,hen⟩
      exact ⟨Nat.dvd_gcd hen heq,hg⟩
    · rintro ⟨heg,hg0⟩
      exact ⟨⟨dvd_trans heg (Nat.gcd_dvd_right n q),hq⟩,dvd_trans heg (Nat.gcd_dvd_left n q)⟩
  rw [←Finset.sum_filter,he,moebius_divisor_sum _ (Nat.gcd_ne_zero_right hq)]

theorem squarefree_coprime_pointwise_expansion (q n : ℕ) (hq : q ≠ 0) (hn : n ≠ 0) :
    (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0)*
      (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) := by
  have hcop : (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) =
      if Nat.Coprime n q then 1 else 0 := by
    exact_mod_cast coprime_moebius_divisor_expansion q n hq
  rw [hcop]
  by_cases h : Nat.Coprime n q
  · simp only [if_pos h,mul_one]
    have he : (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0) =
        ∑ d ∈ n.divisors,if d^2 ∣ n then ((moebius d : ℤ) : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdc : Nat.Coprime d q := h.of_dvd_left (Nat.dvd_of_mem_divisors hd)
      by_cases hs : d^2 ∣ n <;> simp [hs,hdc]
    rw [he]
    exact_mod_cast moebius_square_divisor_expansion n hn
  · simp [h]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma squarefree_square_divisor_sum_cap (q n N : ℕ) (hn : 0<n) (hnN : n≤N) :
    (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0) =
      ∑ d ∈ Finset.Icc 1 N.sqrt,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0 := by
  rw [←Finset.sum_filter,←Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter,Nat.mem_divisors,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd,hn0⟩,hsq,hcop⟩
    have hdpos : 0<d := Nat.pos_of_dvd_of_pos hd hn
    have hdN : d≤N.sqrt := Nat.le_sqrt.mpr (by simpa [pow_two] using (Nat.le_of_dvd hn hsq).trans hnN)
    exact ⟨⟨hdpos,hdN⟩,hsq,hcop⟩
  · rintro ⟨⟨hdpos,hdN⟩,hsq,hcop⟩
    exact ⟨⟨dvd_trans (dvd_pow_self d (by norm_num : 2 ≠ 0)) hsq,hn.ne'⟩,hsq,hcop⟩

theorem squarefree_coprime_count_exact (q N : ℕ) (hq : q ≠ 0) :
    (∑ n ∈ Finset.Icc 1 N,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      ∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ)) else 0 := by
  have hp (n : ℕ) (hn : n∈Finset.Icc 1 N) :
      (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
        ∑ d ∈ Finset.Icc 1 N.sqrt,∑ e ∈ q.divisors,
          if d^2 ∣ n ∧ Nat.Coprime d q ∧ e ∣ n then
            ((moebius d : ℤ) : ℝ)*((moebius e : ℤ) : ℝ) else 0 := by
    rw [squarefree_coprime_pointwise_expansion q n hq (by have := (Finset.mem_Icc.mp hn).1;omega),
      squarefree_square_divisor_sum_cap q n N (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hs : d^2 ∣ n <;> by_cases hc : Nat.Coprime d q <;> by_cases he : e ∣ n <;>
      simp [hs,hc,he]
  rw [Finset.sum_congr rfl hp,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  by_cases hc : Nat.Coprime d q
  · rw [if_pos hc]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hde : Nat.Coprime (d^2) e := (hc.pow_left 2).of_dvd_right (Nat.dvd_of_mem_divisors he)
    have hdvd (n : ℕ) : (d^2 ∣ n ∧ Nat.Coprime d q ∧ e ∣ n) ↔ d^2*e ∣ n := by
      constructor
      · rintro ⟨hsq,hc,he⟩
        rw [←hde.lcm_eq_mul]
        exact Nat.lcm_dvd hsq he
      · intro h
        rw [←hde.lcm_eq_mul] at h
        exact ⟨(Nat.lcm_dvd_iff.mp h).1,hc,(Nat.lcm_dvd_iff.mp h).2⟩
    simp_rw [hdvd]
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,smul_eq_mul]
    have hi : (Finset.Icc 1 N).filter (fun n => d^2*e ∣ n) =
        (Finset.Ioc 0 N).filter (fun n => d^2*e ∣ n) := by congr 1
    rw [hi,Nat.Ioc_filter_dvd_card_eq_div]
    ring
  · simp [hc]

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
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma moebius_reciprocal_divisor_sum_totient (q : ℕ) (hq : q ≠ 0) :
    (∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)/(e : ℝ)) = (q.totient : ℝ)/(q : ℝ) := by
  have hinv := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp
    (show ∀ (n : ℕ),n>0 → ∑ i ∈ n.divisors,(i.totient : ℝ) = (n : ℝ) from
      fun n hn => by exact_mod_cast Nat.sum_totient n) q (Nat.pos_of_ne_zero hq)
  rw [Nat.sum_divisorsAntidiagonal (f:=fun x y => ((moebius x : ℤ) : ℝ)*(y : ℝ))] at hinv
  apply (eq_div_iff (show (q : ℝ) ≠ 0 by exact_mod_cast hq)).mpr
  rw [Finset.sum_mul]
  calc
    _ = ∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((q/e : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro e he
      have he0 : e ≠ 0 := (Nat.pos_of_mem_divisors he).ne'
      rw [Nat.cast_div (Nat.dvd_of_mem_divisors he) (by exact_mod_cast he0)]
      ring
    _ = _ := hinv

theorem squarefree_coprime_count_truncated_error (q N : ℕ) (hq : q ≠ 0) :
    |(∑ n ∈ Finset.Icc 1 N,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      (N : ℝ)*((q.totient : ℝ)/(q : ℝ))*
        (∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0)| ≤
      (N.sqrt : ℝ)*(∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)|) := by
  rw [squarefree_coprime_count_exact q N hq]
  have herr : (∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ)) else 0)-
      (N : ℝ)*((q.totient : ℝ)/(q : ℝ))*
        (∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0) =
      ∑ d ∈ Finset.Icc 1 N.sqrt,∑ e ∈ q.divisors,
        if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)*((moebius e : ℤ) : ℝ)*
          (((N/(d^2*e) : ℕ) : ℝ)-(N : ℝ)/((d : ℝ)^2*(e : ℝ))) else 0 := by
    rw [←moebius_reciprocal_divisor_sum_totient q hq,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hc : Nat.Coprime d q
    · simp only [if_pos hc,Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e he
      ring
    · simp [hc]
  rw [herr]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 N.sqrt,|∑ e ∈ q.divisors,
        if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)*((moebius e : ℤ) : ℝ)*
          (((N/(d^2*e) : ℕ) : ℝ)-(N : ℝ)/((d : ℝ)^2*(e : ℝ))) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N.sqrt,∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)| := by
      apply Finset.sum_le_sum
      intro d hd
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro e he
      by_cases hc : Nat.Coprime d q
      · rw [if_pos hc,abs_mul,abs_mul]
        have hdpos := (Finset.mem_Icc.mp hd).1
        have hepos := Nat.pos_of_mem_divisors he
        have herr1 : |((N/(d^2*e) : ℕ) : ℝ)-(N : ℝ)/((d : ℝ)^2*(e : ℝ))| ≤ 1 := by
          simpa only [Nat.cast_mul,Nat.cast_pow] using nat_div_cast_error_le_one N (d^2*e) (Nat.mul_pos (pow_pos hdpos 2) hepos)
        have hmu : |((moebius d : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n:=d)
        calc
          _ ≤ (1*|((moebius e : ℤ) : ℝ)|)*1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right hmu (abs_nonneg _)) herr1 (abs_nonneg _) (by positivity)
          _ = _ := by ring
      · simp [hc]
    _ = _ := by simp [Finset.sum_const,Nat.card_Icc,smul_eq_mul]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem squarefree_coprime_rational_floor_error (q N e : ℕ) (hq : q ≠ 0) (he : 1≤e) :
    |(∑ d ∈ Finset.Icc 1 (N/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-
      ((N : ℝ)/(e : ℝ))*((6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹)| ≤
      3*Real.sqrt ((N : ℝ)/(e : ℝ)) := by
  let X : ℝ := (N : ℝ)/(e : ℝ)
  let D : ℕ := (N/e).sqrt
  let C : ℝ := (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹
  have hX : 0≤X := by dsimp [X];positivity
  have heR : (0 : ℝ)<e := by exact_mod_cast he
  have hfloorlo : ((N/e : ℕ) : ℝ) ≤ X := Nat.cast_div_le
  have hfloorhi : X ≤ ((N/e : ℕ) : ℝ)+1 := by
    have h := nat_div_cast_error_le_one N e he
    rw [abs_of_nonpos (sub_nonpos.mpr hfloorlo)] at h
    linarith
  have hDlo : (D : ℝ)^2≤X := (show (D : ℝ)^2 ≤ ((N/e : ℕ) : ℝ) by exact_mod_cast Nat.sqrt_le' (N/e)).trans hfloorlo
  have hDhi : X≤((D : ℝ)+1)^2 := by
    have h : ((N/e : ℕ) : ℝ)+1 ≤ ((D : ℝ)+1)^2 := by
      have hn := Nat.lt_succ_sqrt' (N/e)
      have hn' : N/e+1 ≤ (D+1)^2 := by simpa [D,Nat.succ_eq_add_one] using hn
      exact_mod_cast hn'
    exact hfloorhi.trans h
  have hsqrtlo : (D : ℝ) ≤ Real.sqrt X := by
    have hs := Real.sqrt_sq (show 0≤(D : ℝ) by positivity)
    simpa only [hs] using Real.sqrt_le_sqrt hDlo
  have hsqrthi : Real.sqrt X≤(D : ℝ)+1 := by
    simpa only [Real.sqrt_sq (show 0≤(D : ℝ)+1 by positivity)] using Real.sqrt_le_sqrt hDhi
  have hC : |C|≤2 := coprime_moebius_density_norm_le_two q hq
  change |(∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-X*C|≤3*Real.sqrt X
  by_cases hD0 : D=0
  · rw [hD0]
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0:ℕ)<1),Finset.sum_empty,zero_sub,abs_neg,abs_mul,abs_of_nonneg hX]
    have hroot1 : Real.sqrt X≤1 := by simpa only [hD0,Nat.cast_zero,zero_add] using hsqrthi
    have hXroot : X≤Real.sqrt X := by nlinarith [Real.sq_sqrt hX,Real.sqrt_nonneg X]
    have hbound : X*|C|≤X*2 := mul_le_mul_of_nonneg_left hC hX
    nlinarith [Real.sqrt_nonneg X]
  · have hD : 1≤D := Nat.pos_of_ne_zero hD0
    have hDR : (0 : ℝ)<D := by exact_mod_cast hD
    have herr : |(∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-
        X*(∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0)|≤(D : ℝ) := by
      rw [Finset.mul_sum,←Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc
        _ ≤ ∑ d ∈ Finset.Icc 1 D,(1 : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          by_cases hc : Nat.Coprime d q
          · rw [if_pos hc,if_pos hc]
            have hdR : (d : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hd).1)
            have hr : ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ)-X*(((moebius d : ℤ) : ℝ)/(d : ℝ)^2) =
                ((moebius d : ℤ) : ℝ)*(((N/(d^2*e) : ℕ) : ℝ)-(N : ℝ)/((d^2*e : ℕ) : ℝ)) := by
              dsimp only [X]
              push_cast
              field_simp <;> ring
            rw [hr,abs_mul]
            have hmu : |((moebius d : ℤ) : ℝ)|≤1 := by exact_mod_cast abs_moebius_le_one (n:=d)
            exact mul_le_one₀ hmu (abs_nonneg _) (nat_div_cast_error_le_one N _ (Nat.mul_pos (pow_pos (Finset.mem_Icc.mp hd).1 2) he))
          · simp [if_neg hc]
        _ = _ := by simp [Nat.card_Icc]
    have htail := coprime_moebius_density_tail_error q D hq hD
    change |C-(∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0)|≤1/(D : ℝ) at htail
    have hbound : |(∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-X*C|≤(D : ℝ)+X/(D : ℝ) := by
      have heq (S : ℝ) : (∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-X*C =
          ((∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-X*S)+X*(S-C) := by ring
      rw [heq (∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0)]
      refine (abs_add_le _ _).trans (add_le_add herr ?_)
      rw [abs_mul,abs_of_nonneg hX,abs_sub_comm]
      simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left htail hX
    refine hbound.trans ?_
    have hrootD : Real.sqrt X≤2*(D : ℝ) := by
      have h1 : (1 : ℝ)≤D := by exact_mod_cast hD
      linarith
    have hxdiv : X/(D : ℝ)≤2*Real.sqrt X := (div_le_iff₀ hDR).mpr (by nlinarith [Real.sq_sqrt hX,Real.sqrt_nonneg X])
    linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma squarefree_coprime_count_reordered (q N : ℕ) (hq : q ≠ 0) :
    (∑ n ∈ Finset.Icc 1 N,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      ∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*
        (∑ d ∈ Finset.Icc 1 (N/e).sqrt,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0) := by
  rw [squarefree_coprime_count_exact q N hq]
  have hdist : (∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ)) else 0) =
      ∑ d ∈ Finset.Icc 1 N.sqrt,∑ e ∈ q.divisors,
        ((moebius e : ℤ) : ℝ)*(if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hc : Nat.Coprime d q
    · rw [if_pos hc,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [if_pos hc]
      ring
    · simp [if_neg hc]
  rw [hdist,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [←Finset.mul_sum]
  congr 1
  symm
  apply Finset.sum_subset
  · intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans (Nat.sqrt_le_sqrt (Nat.div_le_self N e))⟩
  · intro d hd hnot
    have hdlarge : (N/e).sqrt<d := by
      have hd1 := (Finset.mem_Icc.mp hd).1
      have hnot' : ¬(1≤d ∧ d≤(N/e).sqrt) := by simpa only [Finset.mem_Icc] using hnot
      omega
    have hd2 : N/e<d^2 := Nat.sqrt_lt'.mp hdlarge
    have hdiv : N/(d^2*e)=(N/e)/d^2 := by rw [Nat.div_div_eq_div_mul,Nat.mul_comm]
    rw [hdiv,Nat.div_eq_of_lt hd2]
    simp

lemma squarefree_coprime_density_normalization (q : ℕ) (hq : q ≠ 0) :
    ((q.totient : ℝ)/(q : ℝ))*((6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹) =
      (6/Real.pi^2)*∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1) := by
  have htot : (q.totient : ℝ)=(q : ℝ)*∏ p ∈ q.primeFactors,(1-(p : ℝ)⁻¹) := by
    have h := congrArg (fun r : ℚ => (r : ℝ)) (Nat.totient_eq_mul_prod_factors q)
    push_cast at h
    exact h
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  rw [htot,mul_div_cancel_left₀ _ hqR]
  have hprod : (∏ p ∈ q.primeFactors,(1-(p : ℝ)⁻¹))*(∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹) =
      ∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1) := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 : (2 : ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ)-1 ≠ 0 := by linarith
    have hpp : (p : ℝ)+1 ≠ 0 := by linarith
    have hden : 1-1/(p : ℝ)^2 ≠ 0 := by
      have hsq : (1 : ℝ)<(p : ℝ)^2 := by nlinarith
      have hi : 1/(p : ℝ)^2<1 := (div_lt_one (by positivity)).mpr hsq
      linarith
    rw [←div_eq_mul_inv]
    apply (div_eq_iff hden).mpr
    field_simp [hp0,hpp] <;> ring
  calc
    _ = (6/Real.pi^2)*((∏ p ∈ q.primeFactors,(1-(p : ℝ)⁻¹))*(∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹)) := by ring
    _ = _ := by rw [hprod]

theorem squarefree_coprime_count_square_root_error (q N : ℕ) (hq : q ≠ 0) :
    |(∑ n ∈ Finset.Icc 1 N,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      (N : ℝ)*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))| ≤
      3*Real.sqrt (N : ℝ)*(∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)|/Real.sqrt (e : ℝ)) := by
  let C : ℝ := (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹
  have hmain : (N : ℝ)*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1)) =
      ∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((N : ℝ)/(e : ℝ))*C := by
    have h := squarefree_coprime_density_normalization q hq
    change ((q.totient : ℝ)/(q : ℝ))*C = _ at h
    rw [mul_assoc,←h,←moebius_reciprocal_divisor_sum_totient q hq,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    ring
  rw [squarefree_coprime_count_reordered q N hq,hmain,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)*
        (∑ d ∈ Finset.Icc 1 (N/e).sqrt,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-((moebius e : ℤ) : ℝ)*((N : ℝ)/(e : ℝ))*C| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)| * (3*Real.sqrt ((N : ℝ)/(e : ℝ))) := by
      apply Finset.sum_le_sum
      intro e he
      have hepos := Nat.pos_of_mem_divisors he
      have herr := squarefree_coprime_rational_floor_error q N e hq hepos
      change |(∑ d ∈ Finset.Icc 1 (N/e).sqrt,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-((N : ℝ)/(e : ℝ))*C| ≤ _ at herr
      rw [mul_assoc,←mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_left herr (abs_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [Real.sqrt_div (by positivity)]
      ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2300000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma moebius_real_abs_eq_square (n : ℕ) : |((moebius n : ℤ) : ℝ)|=((moebius n : ℤ) : ℝ)^2 := by
  rcases moebius_eq_or n with h|h|h <;> rw [h] <;> norm_num

lemma nat_div_interval_cast_error_le_one (A B k : ℕ) (hk : 0<k) :
    |((B/k : ℕ) : ℝ)-((A/k : ℕ) : ℝ)-((B : ℝ)-(A : ℝ))/(k : ℝ)|≤1 := by
  have ha := nat_div_cast_error_le_one A k hk
  have hb := nat_div_cast_error_le_one B k hk
  have hal : ((A/k : ℕ) : ℝ)≤(A : ℝ)/(k : ℝ) := Nat.cast_div_le
  have hbl : ((B/k : ℕ) : ℝ)≤(B : ℝ)/(k : ℝ) := Nat.cast_div_le
  rw [abs_of_nonpos (sub_nonpos.mpr hal)] at ha
  rw [abs_of_nonpos (sub_nonpos.mpr hbl)] at hb
  rw [sub_div,abs_le]
  constructor <;> linarith

lemma coprime_moebius_density_tail_squarefree (q D : ℕ) (hq : q≠0) :
    |(6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹-
      (∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0)|≤
      ∑' n : ℕ,if D<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0 := by
  let f : ℕ → ℝ := fun n => if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0
  let g : ℕ → ℝ := fun n => ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2
  have hf : Summable f := coprime_moebius_reciprocal_square_summable q
  have hg : Summable g := by
    apply Summable.of_nonneg_of_le (fun n => by dsimp [g];positivity) ?_ hasSum_zeta_two.summable
    intro n
    exact div_le_div_of_nonneg_right (moebius_real_square_le_one n) (sq_nonneg _)
  have hs : (∑ d ∈ Finset.range (D+1),f d) = ∑ d ∈ Finset.Icc 1 D,f d := by
    rw [Finset.range_eq_Ico]
    have hi : Finset.Ico 0 (D+1)=insert 0 (Finset.Icc 1 D) := by ext n;simp;omega
    rw [hi,Finset.sum_insert (by simp)]
    simp [f]
  have he := hf.sum_add_tsum_nat_add (D+1)
  rw [hs] at he
  rw [←squarefree_coprime_density_series q hq]
  change |(∑' n : ℕ,f n)-(∑ d ∈ Finset.Icc 1 D,f d)|≤_
  have hid : (∑' n : ℕ,f n)-(∑ d ∈ Finset.Icc 1 D,f d)=∑' n : ℕ,f (n+(D+1)) := by linarith
  rw [hid]
  have hft : Summable (fun n : ℕ => f (n+(D+1))) := hf.comp_injective (fun n m h => by omega)
  have hgt : Summable (fun n : ℕ => g (n+(D+1))) := hg.comp_injective (fun n m h => by omega)
  have hpoint (n : ℕ) : ‖f n‖≤g n := by
    dsimp [f,g]
    by_cases hc : Nat.Coprime n q
    · rw [if_pos hc,abs_div,show |(n : ℝ)^2|=(n : ℝ)^2 from abs_of_nonneg (sq_nonneg _),moebius_real_abs_eq_square]
    · rw [if_neg hc,abs_zero]
      positivity
  have hbound : |∑' n : ℕ,f (n+(D+1))|≤∑' n : ℕ,g (n+(D+1)) :=
    (show |∑' n : ℕ,f (n+(D+1))|≤∑' n : ℕ,‖f (n+(D+1))‖ by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hft.norm).trans
      (hft.norm.tsum_le_tsum (fun n => hpoint (n+(D+1))) hgt)
  have hgf := hg.sum_add_tsum_nat_add (D+1)
  have hgs : (∑ d ∈ Finset.range (D+1),g d)=∑ d ∈ Finset.Icc 1 D,g d := by
    rw [Finset.range_eq_Ico]
    have hi : Finset.Ico 0 (D+1)=insert 0 (Finset.Icc 1 D) := by ext n;simp;omega
    rw [hi,Finset.sum_insert (by simp)]
    simp [g]
  rw [hgs] at hgf
  have hge := squarefree_reciprocal_tail_sub D
  change (∑ d ∈ Finset.Icc 1 D,g d)+(∑' n : ℕ,if D<n then g n else 0)=∑' n : ℕ,g n at hge
  have htail : (∑' n : ℕ,g (n+(D+1)))=∑' n : ℕ,if D<n then g n else 0 := by linarith
  rw [htail] at hbound
  exact hbound

lemma floor_sqrt_rational_nat (B e : ℕ) (he : 1≤e) :
    ⌊Real.sqrt ((B : ℝ)/(e : ℝ))⌋₊=(B/e).sqrt := by
  let D := (B/e).sqrt
  have heR : (0 : ℝ)<e := by exact_mod_cast he
  have hlo : ((B/e : ℕ) : ℝ)≤(B : ℝ)/(e : ℝ) := Nat.cast_div_le
  have hmod : ((B%e : ℕ) : ℝ)<(e : ℝ) := by exact_mod_cast Nat.mod_lt B (by omega : 0<e)
  have hid : (e : ℝ)*((B/e : ℕ) : ℝ)+((B%e : ℕ) : ℝ)=(B : ℝ) := by exact_mod_cast Nat.div_add_mod B e
  have hhi : (B : ℝ)/(e : ℝ)<((B/e : ℕ) : ℝ)+1 := (div_lt_iff₀ heR).mpr (by nlinarith)
  have hDlo : (D : ℝ)^2≤(B : ℝ)/(e : ℝ) :=
    (show (D : ℝ)^2≤((B/e : ℕ) : ℝ) by exact_mod_cast Nat.sqrt_le' (B/e)).trans hlo
  have hDhi : (B : ℝ)/(e : ℝ)<((D : ℝ)+1)^2 := by
    have h : ((B/e : ℕ) : ℝ)+1≤((D : ℝ)+1)^2 := by
      exact_mod_cast Nat.lt_succ_sqrt' (B/e)
    exact hhi.trans_le h
  apply (Nat.floor_eq_iff (Real.sqrt_nonneg _)).mpr
  constructor
  · simpa only [Real.sqrt_sq (by positivity : (0 : ℝ)≤D)] using Real.sqrt_le_sqrt hDlo
  · simpa only [Real.sqrt_sq (by positivity : (0 : ℝ)≤(D : ℝ)+1)] using Real.sqrt_lt_sqrt (by positivity) hDhi

theorem squarefree_coprime_rational_interval_floor_error (q A B e : ℕ)
    (hq : q≠0) (he : 1≤e) (hAB : A≤B) (hhalf : B≤2*A) :
    |(∑ d ∈ Finset.Icc 1 (B/e).sqrt,if Nat.Coprime d q then
      ((moebius d : ℤ) : ℝ)*(((B/(d^2*e) : ℕ) : ℝ)-((A/(d^2*e) : ℕ) : ℝ)) else 0)-
      (((B : ℝ)-(A : ℝ))/(e : ℝ))*((6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹)|≤
      (127/100 : ℝ)*Real.sqrt ((B : ℝ)/(e : ℝ)) := by
  let X : ℝ := (B : ℝ)/(e : ℝ)
  let Y : ℝ := ((B : ℝ)-(A : ℝ))/(e : ℝ)
  let D : ℕ := (B/e).sqrt
  let C : ℝ := (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹
  let P : ℝ := ∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0
  let S : ℝ := ∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
      ((moebius d : ℤ) : ℝ)*(((B/(d^2*e) : ℕ) : ℝ)-((A/(d^2*e) : ℕ) : ℝ)) else 0
  let T : ℝ := ∑' n : ℕ,if D<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0
  have hY : 0≤Y := by
    dsimp [Y]
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hAB)) (by positivity)
  have hYX : Y≤X/2 := by
    have h : (B : ℝ)≤2*(A : ℝ) := by exact_mod_cast hhalf
    have heR : (0 : ℝ)<e := by exact_mod_cast he
    dsimp [Y,X]
    apply (div_le_iff₀ heR).mpr
    field_simp
    linarith
  have hT : 0≤T := by
    dsimp [T]
    apply tsum_nonneg
    intro n
    split_ifs <;> positivity
  have herr : |S-Y*P|≤∑ d ∈ Finset.Icc 1 D,((moebius d : ℤ) : ℝ)^2 := by
    dsimp [S,P]
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro d hd
    by_cases hc : Nat.Coprime d q
    · rw [if_pos hc,if_pos hc]
      have hdR : (d : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hd).1)
      have hid : ((moebius d : ℤ) : ℝ)*(((B/(d^2*e) : ℕ) : ℝ)-((A/(d^2*e) : ℕ) : ℝ))-Y*(((moebius d : ℤ) : ℝ)/(d : ℝ)^2)=
          ((moebius d : ℤ) : ℝ)*(((B/(d^2*e) : ℕ) : ℝ)-((A/(d^2*e) : ℕ) : ℝ)-((B : ℝ)-(A : ℝ))/((d^2*e : ℕ) : ℝ)) := by
        dsimp [Y]
        push_cast
        field_simp <;> ring
      rw [hid,abs_mul,moebius_real_abs_eq_square]
      exact mul_le_of_le_one_right (sq_nonneg _) (nat_div_interval_cast_error_le_one A B _ (Nat.mul_pos (pow_pos (Finset.mem_Icc.mp hd).1 2) he))
    · simp only [if_neg hc,mul_zero,sub_zero,abs_zero]
      positivity
  have htail : |P-C|≤T := by
    simpa only [abs_sub_comm] using coprime_moebius_density_tail_squarefree q D hq
  have hbound : |S-Y*C|≤(∑ d ∈ Finset.Icc 1 D,((moebius d : ℤ) : ℝ)^2)+(X/2)*T := by
    have hid : S-Y*C=(S-Y*P)+Y*(P-C) := by ring
    rw [hid]
    refine (abs_add_le _ _).trans (add_le_add herr ?_)
    rw [abs_mul,abs_of_nonneg hY]
    exact (mul_le_mul_of_nonneg_left htail hY).trans (mul_le_mul_of_nonneg_right hYX hT)
  have hsm := squarefree_smoothed_count_le_127 (Real.sqrt X) (Real.sqrt_nonneg X)
  have hfloor : ⌊Real.sqrt X⌋₊=D := floor_sqrt_rational_nat B e he
  rw [hfloor,Real.sq_sqrt (by dsimp [X];positivity)] at hsm
  change |S-Y*C|≤_
  exact hbound.trans hsm

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2500000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma real_floor_interval_error_le_one (A B k : ℝ) (hA : 0≤A) (hB : 0≤B) (hk : 0<k) :
    |(⌊B/k⌋₊ : ℝ)-(⌊A/k⌋₊ : ℝ)-(B-A)/k|≤1 := by
  have hal := Nat.floor_le (div_nonneg hA hk.le)
  have hbl := Nat.floor_le (div_nonneg hB hk.le)
  have hau := Nat.lt_floor_add_one (A/k)
  have hbu := Nat.lt_floor_add_one (B/k)
  rw [sub_div,abs_le]
  constructor <;> linarith

lemma floor_sqrt_nonnegative_real (X : ℝ) (hX : 0≤X) :
    ⌊Real.sqrt X⌋₊=Nat.sqrt ⌊X⌋₊ := by
  let D := Nat.sqrt ⌊X⌋₊
  have hlo : (⌊X⌋₊ : ℝ)≤X := Nat.floor_le hX
  have hhi : X<(⌊X⌋₊ : ℝ)+1 := Nat.lt_floor_add_one X
  have hDlo : (D : ℝ)^2≤X :=
    (show (D : ℝ)^2≤(⌊X⌋₊ : ℝ) by exact_mod_cast Nat.sqrt_le' ⌊X⌋₊).trans hlo
  have hDhi : X<((D : ℝ)+1)^2 := by
    have h : (⌊X⌋₊ : ℝ)+1≤((D : ℝ)+1)^2 := by exact_mod_cast Nat.lt_succ_sqrt' ⌊X⌋₊
    exact hhi.trans_le h
  apply (Nat.floor_eq_iff (Real.sqrt_nonneg _)).mpr
  constructor
  · simpa only [Real.sqrt_sq (by positivity : (0 : ℝ)≤D)] using Real.sqrt_le_sqrt hDlo
  · simpa only [Real.sqrt_sq (by positivity : (0 : ℝ)≤(D : ℝ)+1)] using Real.sqrt_lt_sqrt hX hDhi

lemma floor_sqrt_real_quotient (B : ℝ) (e : ℕ) (hB : 0≤B) (he : 1≤e) :
    ⌊Real.sqrt (B/(e : ℝ))⌋₊=(⌊B⌋₊/e).sqrt := by
  rw [floor_sqrt_nonnegative_real (B/(e : ℝ)) (div_nonneg hB (by positivity)),Nat.floor_div_natCast]

theorem squarefree_coprime_real_rational_interval_floor_error (q e : ℕ) (A B : ℝ)
    (hq : q≠0) (he : 1≤e) (hA : 0≤A) (hAB : A≤B) (hhalf : B≤2*A) :
    |(∑ d ∈ Finset.Icc 1 (⌊B⌋₊/e).sqrt,if Nat.Coprime d q then
      ((moebius d : ℤ) : ℝ)*(((⌊B⌋₊/(d^2*e) : ℕ) : ℝ)-((⌊A⌋₊/(d^2*e) : ℕ) : ℝ)) else 0)-
      ((B-A)/(e : ℝ))*((6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹)|≤
      (127/100 : ℝ)*Real.sqrt (B/(e : ℝ)) := by
  have hB : 0≤B := hA.trans hAB
  let X : ℝ := B/(e : ℝ)
  let Y : ℝ := (B-A)/(e : ℝ)
  let D : ℕ := (⌊B⌋₊/e).sqrt
  let C : ℝ := (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹
  let P : ℝ := ∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0
  let S : ℝ := ∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
      ((moebius d : ℤ) : ℝ)*(((⌊B⌋₊/(d^2*e) : ℕ) : ℝ)-((⌊A⌋₊/(d^2*e) : ℕ) : ℝ)) else 0
  let T : ℝ := ∑' n : ℕ,if D<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0
  have hY : 0≤Y := by
    dsimp [Y]
    exact div_nonneg (sub_nonneg.mpr (hAB)) (by positivity)
  have hYX : Y≤X/2 := by
    have h : B≤2*A := hhalf
    have heR : (0 : ℝ)<e := by exact_mod_cast he
    dsimp [Y,X]
    apply (div_le_iff₀ heR).mpr
    field_simp
    linarith
  have hT : 0≤T := by
    dsimp [T]
    apply tsum_nonneg
    intro n
    split_ifs <;> positivity
  have herr : |S-Y*P|≤∑ d ∈ Finset.Icc 1 D,((moebius d : ℤ) : ℝ)^2 := by
    dsimp [S,P]
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro d hd
    by_cases hc : Nat.Coprime d q
    · rw [if_pos hc,if_pos hc]
      have hdR : (d : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hd).1)
      have hid : ((moebius d : ℤ) : ℝ)*(((⌊B⌋₊/(d^2*e) : ℕ) : ℝ)-((⌊A⌋₊/(d^2*e) : ℕ) : ℝ))-Y*(((moebius d : ℤ) : ℝ)/(d : ℝ)^2)=
          ((moebius d : ℤ) : ℝ)*(((⌊B⌋₊/(d^2*e) : ℕ) : ℝ)-((⌊A⌋₊/(d^2*e) : ℕ) : ℝ)-(B-A)/((d^2*e : ℕ) : ℝ)) := by
        dsimp [Y]
        push_cast
        field_simp <;> ring
      rw [hid,abs_mul,moebius_real_abs_eq_square]
      have hkpos : (0 : ℝ)<((d^2*e : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos (pow_pos (Finset.mem_Icc.mp hd).1 2) he
      have hfloor := real_floor_interval_error_le_one A B ((d^2*e : ℕ) : ℝ) hA hB hkpos
      rw [Nat.floor_div_natCast,Nat.floor_div_natCast] at hfloor
      exact mul_le_of_le_one_right (sq_nonneg _) hfloor
    · simp only [if_neg hc,mul_zero,sub_zero,abs_zero]
      positivity
  have htail : |P-C|≤T := by
    simpa only [abs_sub_comm] using coprime_moebius_density_tail_squarefree q D hq
  have hbound : |S-Y*C|≤(∑ d ∈ Finset.Icc 1 D,((moebius d : ℤ) : ℝ)^2)+(X/2)*T := by
    have hid : S-Y*C=(S-Y*P)+Y*(P-C) := by ring
    rw [hid]
    refine (abs_add_le _ _).trans (add_le_add herr ?_)
    rw [abs_mul,abs_of_nonneg hY]
    exact (mul_le_mul_of_nonneg_left htail hY).trans (mul_le_mul_of_nonneg_right hYX hT)
  have hsm := squarefree_smoothed_count_le_127 (Real.sqrt X) (Real.sqrt_nonneg X)
  have hfloor : ⌊Real.sqrt X⌋₊=D := floor_sqrt_real_quotient B e hB he
  rw [hfloor,Real.sq_sqrt (div_nonneg hB (by positivity))] at hsm
  change |S-Y*C|≤_
  exact hbound.trans hsm

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2300000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma squarefree_coprime_count_reordered_cap (q A B : ℕ) (hq : q≠0) (hAB : A≤B) :
    (∑ n ∈ Finset.Icc 1 A,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)=
      ∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*
        (∑ d ∈ Finset.Icc 1 (B/e).sqrt,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((A/(d^2*e) : ℕ) : ℝ) else 0) := by
  rw [squarefree_coprime_count_reordered q A hq]
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  apply Finset.sum_subset
  · intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans (Nat.sqrt_le_sqrt (Nat.div_le_div_right hAB))⟩
  · intro d hd hnot
    have hdlarge : (A/e).sqrt<d := by
      have hd1 := (Finset.mem_Icc.mp hd).1
      have hnot' : ¬(1≤d ∧ d≤(A/e).sqrt) := by simpa only [Finset.mem_Icc] using hnot
      omega
    have hd2 : A/e<d^2 := Nat.sqrt_lt'.mp hdlarge
    have hdiv : A/(d^2*e)=(A/e)/d^2 := by rw [Nat.div_div_eq_div_mul,Nat.mul_comm]
    rw [hdiv,Nat.div_eq_of_lt hd2]
    simp

theorem squarefree_coprime_short_interval_error (q A B : ℕ) (hq : q≠0)
    (hAB : A≤B) (hhalf : B≤2*A) :
    |(∑ n ∈ Finset.Ioc A B,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      ((B : ℝ)-(A : ℝ))*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))|≤
      (127/100 : ℝ)*Real.sqrt (B : ℝ)*(∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)|/Real.sqrt (e : ℝ)) := by
  let C : ℝ := (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹
  have hs : (∑ n ∈ Finset.Ioc A B,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)=
      (∑ n ∈ Finset.Icc 1 B,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      (∑ n ∈ Finset.Icc 1 A,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) := by
    have hsub : Finset.Icc 1 A⊆Finset.Icc 1 B := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans hAB⟩
    have hi : Finset.Icc 1 B \ Finset.Icc 1 A=Finset.Ioc A B := by ext n;simp;omega
    rw [←Finset.sum_sdiff hsub,hi]
    ring
  have hmain : ((B : ℝ)-(A : ℝ))*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))=
      ∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*(((B : ℝ)-(A : ℝ))/(e : ℝ))*C := by
    have h := squarefree_coprime_density_normalization q hq
    change ((q.totient : ℝ)/(q : ℝ))*C=_ at h
    rw [mul_assoc,←h,←moebius_reciprocal_divisor_sum_totient q hq,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    ring
  rw [hs,squarefree_coprime_count_reordered q B hq,squarefree_coprime_count_reordered_cap q A B hq hAB,
    ←Finset.sum_sub_distrib,hmain,←Finset.sum_sub_distrib]
  have hterm (e : ℕ) :
      ((moebius e : ℤ) : ℝ)*(∑ d ∈ Finset.Icc 1 (B/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((B/(d^2*e) : ℕ) : ℝ) else 0)-
      ((moebius e : ℤ) : ℝ)*(∑ d ∈ Finset.Icc 1 (B/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((A/(d^2*e) : ℕ) : ℝ) else 0)-
      ((moebius e : ℤ) : ℝ)*(((B : ℝ)-(A : ℝ))/(e : ℝ))*C=
      ((moebius e : ℤ) : ℝ)*((∑ d ∈ Finset.Icc 1 (B/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(((B/(d^2*e) : ℕ) : ℝ)-((A/(d^2*e) : ℕ) : ℝ)) else 0)-
        (((B : ℝ)-(A : ℝ))/(e : ℝ))*C) := by
    have hdifference : (∑ d ∈ Finset.Icc 1 (B/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((B/(d^2*e) : ℕ) : ℝ) else 0)-
        (∑ d ∈ Finset.Icc 1 (B/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((A/(d^2*e) : ℕ) : ℝ) else 0)=
        ∑ d ∈ Finset.Icc 1 (B/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(((B/(d^2*e) : ℕ) : ℝ)-((A/(d^2*e) : ℕ) : ℝ)) else 0 := by
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> ring
    rw [←mul_sub,hdifference]
    ring
  simp_rw [hterm]
  calc
    _ ≤ ∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)*((∑ d ∈ Finset.Icc 1 (B/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(((B/(d^2*e) : ℕ) : ℝ)-((A/(d^2*e) : ℕ) : ℝ)) else 0)-
        (((B : ℝ)-(A : ℝ))/(e : ℝ))*C)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)| *((127/100 : ℝ)*Real.sqrt ((B : ℝ)/(e : ℝ))) := by
      apply Finset.sum_le_sum
      intro e he
      have herr := squarefree_coprime_rational_interval_floor_error q A B e hq (Nat.pos_of_mem_divisors he) hAB hhalf
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left herr (abs_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [Real.sqrt_div (by positivity)]
      ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2300000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

noncomputable def reciprocalSqrtArithmetic : ArithmeticFunction ℝ :=
  ⟨fun n => 1/Real.sqrt (n : ℝ),by norm_num⟩

noncomputable def squarefreeReciprocalSqrtArithmetic : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul (ArithmeticFunction.pmul (moebius : ArithmeticFunction ℝ) (moebius : ArithmeticFunction ℝ)) reciprocalSqrtArithmetic

lemma reciprocalSqrtArithmetic_multiplicative : reciprocalSqrtArithmetic.IsMultiplicative := by
  refine ⟨by norm_num [reciprocalSqrtArithmetic],?_⟩
  intro m n hmn
  simp only [reciprocalSqrtArithmetic,ArithmeticFunction.coe_mk,Nat.cast_mul,
    Real.sqrt_mul (by positivity : (0 : ℝ)≤m),one_div,mul_inv_rev]
  ring

lemma squarefreeReciprocalSqrtArithmetic_multiplicative : squarefreeReciprocalSqrtArithmetic.IsMultiplicative :=
  (isMultiplicative_moebius.intCast.pmul isMultiplicative_moebius.intCast).pmul reciprocalSqrtArithmetic_multiplicative

lemma squarefreeReciprocalSqrtArithmetic_value (n : ℕ) :
    squarefreeReciprocalSqrtArithmetic n=|((moebius n : ℤ) : ℝ)|/Real.sqrt (n : ℝ) := by
  change (((moebius n : ℤ) : ℝ)*((moebius n : ℤ) : ℝ))*(1/Real.sqrt (n : ℝ))=_
  rw [moebius_real_abs_eq_square]
  ring

lemma squarefreeReciprocalSqrtArithmetic_prime_power_sum (p k : ℕ) (hp : Nat.Prime p) (hk : 1≤k) :
    (∑ d ∈ (p^k).divisors,squarefreeReciprocalSqrtArithmetic d)=1+1/Real.sqrt (p : ℝ) := by
  rw [Nat.sum_divisors_prime_pow hp]
  have hs : (∑ j ∈ Finset.range (k+1),squarefreeReciprocalSqrtArithmetic (p^j))=
      ∑ j ∈ Finset.range 2,squarefreeReciprocalSqrtArithmetic (p^j) := by
    symm
    apply Finset.sum_subset
    · exact Finset.range_mono (by omega)
    · intro j hj hnot
      have hj2 : 2≤j := by simp only [Finset.mem_range] at hnot;omega
      rw [squarefreeReciprocalSqrtArithmetic_value,moebius_apply_prime_pow hp (by omega),if_neg (by omega)]
      norm_num
  rw [hs]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    squarefreeReciprocalSqrtArithmetic_value,moebius_apply_one,moebius_apply_prime hp]
  norm_num

theorem moebius_half_weighted_divisor_euler_product (q : ℕ) (hq : q≠0) :
    (∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)|/Real.sqrt (e : ℝ))=
      ∏ p ∈ q.primeFactors,(1+1/Real.sqrt (p : ℝ)) := by
  let f := squarefreeReciprocalSqrtArithmetic
  have hf : f.IsMultiplicative := squarefreeReciprocalSqrtArithmetic_multiplicative
  have hg := hf.mul (isMultiplicative_zeta.natCast (R:=ℝ))
  have he := hg.multiplicative_factorization (f*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) hq
  rw [ArithmeticFunction.coe_mul_zeta_apply] at he
  simp only [Finsupp.prod] at he
  change (∑ e ∈ q.divisors,f e)=∏ p ∈ q.factorization.support,(f*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) (p^q.factorization p) at he
  change (∑ e ∈ q.divisors,squarefreeReciprocalSqrtArithmetic e)=_ at he
  rw [←Finset.sum_congr rfl (fun e he => squarefreeReciprocalSqrtArithmetic_value e)]
  rw [he]
  apply Finset.prod_congr q.support_factorization
  intro p hp
  have hp' : p∈q.primeFactors := by simpa only [q.support_factorization] using hp
  have hprime := Nat.prime_of_mem_primeFactors hp'
  have hk : 1≤q.factorization p := by
    have hne : q.factorization p≠0 := Finsupp.mem_support_iff.mp hp
    omega
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  exact squarefreeReciprocalSqrtArithmetic_prime_power_sum p (q.factorization p) hprime hk

theorem squarefree_coprime_short_interval_euler_error (q A B : ℕ) (hq : q≠0)
    (hAB : A≤B) (hhalf : B≤2*A) :
    |(∑ n ∈ Finset.Ioc A B,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      ((B : ℝ)-(A : ℝ))*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))|≤
      (127/100 : ℝ)*Real.sqrt (B : ℝ)*(∏ p ∈ q.primeFactors,(1+1/Real.sqrt (p : ℝ))) := by
  rw [←moebius_half_weighted_divisor_euler_product q hq]
  exact squarefree_coprime_short_interval_error q A B hq hAB hhalf

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem squarefree_coprime_real_short_interval_error (q : ℕ) (A B : ℝ) (hq : q≠0)
    (hA : 0≤A) (hAB : A≤B) (hhalf : B≤2*A) :
    |(∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      (B-A)*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))|≤
      (127/100 : ℝ)*Real.sqrt B*(∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)|/Real.sqrt (e : ℝ)) := by
  have hB : 0≤B := hA.trans hAB
  let C : ℝ := (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹
  have hs : (∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)=
      (∑ n ∈ Finset.Icc 1 ⌊B⌋₊,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      (∑ n ∈ Finset.Icc 1 ⌊A⌋₊,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) := by
    have hsub : Finset.Icc 1 ⌊A⌋₊⊆Finset.Icc 1 ⌊B⌋₊ := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans (Nat.floor_mono hAB)⟩
    have hi : Finset.Icc 1 ⌊B⌋₊ \ Finset.Icc 1 ⌊A⌋₊=Finset.Ioc ⌊A⌋₊ ⌊B⌋₊ := by ext n;simp;omega
    rw [←Finset.sum_sdiff hsub,hi]
    ring
  have hmain : (B-A)*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))=
      ∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((B-A)/(e : ℝ))*C := by
    have h := squarefree_coprime_density_normalization q hq
    change ((q.totient : ℝ)/(q : ℝ))*C=_ at h
    rw [mul_assoc,←h,←moebius_reciprocal_divisor_sum_totient q hq,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    ring
  rw [hs,squarefree_coprime_count_reordered q ⌊B⌋₊ hq,squarefree_coprime_count_reordered_cap q ⌊A⌋₊ ⌊B⌋₊ hq (Nat.floor_mono hAB),
    ←Finset.sum_sub_distrib,hmain,←Finset.sum_sub_distrib]
  have hterm (e : ℕ) :
      ((moebius e : ℤ) : ℝ)*(∑ d ∈ Finset.Icc 1 (⌊B⌋₊/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((⌊B⌋₊/(d^2*e) : ℕ) : ℝ) else 0)-
      ((moebius e : ℤ) : ℝ)*(∑ d ∈ Finset.Icc 1 (⌊B⌋₊/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((⌊A⌋₊/(d^2*e) : ℕ) : ℝ) else 0)-
      ((moebius e : ℤ) : ℝ)*((B-A)/(e : ℝ))*C=
      ((moebius e : ℤ) : ℝ)*((∑ d ∈ Finset.Icc 1 (⌊B⌋₊/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(((⌊B⌋₊/(d^2*e) : ℕ) : ℝ)-((⌊A⌋₊/(d^2*e) : ℕ) : ℝ)) else 0)-
        ((B-A)/(e : ℝ))*C) := by
    have hdifference : (∑ d ∈ Finset.Icc 1 (⌊B⌋₊/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((⌊B⌋₊/(d^2*e) : ℕ) : ℝ) else 0)-
        (∑ d ∈ Finset.Icc 1 (⌊B⌋₊/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((⌊A⌋₊/(d^2*e) : ℕ) : ℝ) else 0)=
        ∑ d ∈ Finset.Icc 1 (⌊B⌋₊/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(((⌊B⌋₊/(d^2*e) : ℕ) : ℝ)-((⌊A⌋₊/(d^2*e) : ℕ) : ℝ)) else 0 := by
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> ring
    rw [←mul_sub,hdifference]
    ring
  simp_rw [hterm]
  calc
    _ ≤ ∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)*((∑ d ∈ Finset.Icc 1 (⌊B⌋₊/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(((⌊B⌋₊/(d^2*e) : ℕ) : ℝ)-((⌊A⌋₊/(d^2*e) : ℕ) : ℝ)) else 0)-
        ((B-A)/(e : ℝ))*C)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)| *((127/100 : ℝ)*Real.sqrt (B/(e : ℝ))) := by
      apply Finset.sum_le_sum
      intro e he
      have herr := squarefree_coprime_real_rational_interval_floor_error q e A B hq (Nat.pos_of_mem_divisors he) hA hAB hhalf
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left herr (abs_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [Real.sqrt_div hB]
      ring


theorem squarefree_coprime_real_short_interval_euler_error (q : ℕ) (A B : ℝ) (hq : q≠0)
    (hA : 0≤A) (hAB : A≤B) (hhalf : B≤2*A) :
    |(∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      (B-A)*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))|≤
      (127/100 : ℝ)*Real.sqrt B*(∏ p ∈ q.primeFactors,(1+1/Real.sqrt (p : ℝ))) := by
  rw [←moebius_half_weighted_divisor_euler_product q hq]
  exact squarefree_coprime_real_short_interval_error q A B hq hA hAB hhalf

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma floor_max_nonnegative_real (a b : ℝ) : ⌊max a b⌋₊=max ⌊a⌋₊ ⌊b⌋₊ := by
  by_cases h : a≤b
  · rw [max_eq_right h,max_eq_right (Nat.floor_mono h)]
  · rw [max_eq_left (le_of_not_ge h),max_eq_left (Nat.floor_mono (le_of_not_ge h))]

lemma vaughan_squarefree_real_cutoffs (U A B r t s : ℕ)
    (hr : 1≤r) (ht : 1≤t) (hs : 1≤s) (hAB : A≤B) (hhalf : B≤2*A)
    (hrcap : r≤B/((U+1)*s)) (htcap : t≤B/((U+1)*s)) :
    let a : ℝ := max ((A : ℝ)/(r*t*s : ℕ)) (max ((U : ℝ)/r) ((U : ℝ)/t))
    let b : ℝ := (B : ℝ)/(r*t*s : ℕ)
    0≤a ∧ a≤b ∧ b≤2*a ∧
      ⌊a⌋₊=max (A/(r*t*s)) (max (U/r) (U/t)) ∧ ⌊b⌋₊=B/(r*t*s) := by
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have htR : (0:ℝ)<t := by exact_mod_cast ht
  have hsR : (0:ℝ)<s := by exact_mod_cast hs
  have hk : (0:ℝ)<(r*t*s : ℕ) := by positivity
  have hd : 0<(U+1)*s := Nat.mul_pos (Nat.succ_pos U) hs
  have hrProd : r*((U+1)*s)≤B := (Nat.le_div_iff_mul_le hd).mp hrcap
  have htProd : t*((U+1)*s)≤B := (Nat.le_div_iff_mul_le hd).mp htcap
  have hUrs : U*r*s≤B := by
    calc
      _≤(U+1)*r*s := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ U))
      _=r*((U+1)*s) := by ring
      _≤B := hrProd
  have hUts : U*t*s≤B := by
    calc
      _≤(U+1)*t*s := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ U))
      _=t*((U+1)*s) := by ring
      _≤B := htProd
  have hUr : (U : ℝ)/r≤(B : ℝ)/(r*t*s : ℕ) := by
    apply (div_le_div_iff₀ hrR hk).mpr
    have hp : (U : ℝ)*t*s≤B := by exact_mod_cast hUts
    push_cast
    nlinarith
  have hUt : (U : ℝ)/t≤(B : ℝ)/(r*t*s : ℕ) := by
    apply (div_le_div_iff₀ htR hk).mpr
    have hp : (U : ℝ)*r*s≤B := by exact_mod_cast hUrs
    push_cast
    nlinarith
  have hAleB : (A : ℝ)/(r*t*s : ℕ)≤(B : ℝ)/(r*t*s : ℕ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hAB) hk.le
  have hh : (B : ℝ)/(r*t*s : ℕ)≤2*((A : ℝ)/(r*t*s : ℕ)) := by
    rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hhalf) hk.le
  dsimp only
  refine ⟨le_max_of_le_left (by positivity),max_le hAleB (max_le hUr hUt),
    hh.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)),?_,?_⟩
  · rw [floor_max_nonnegative_real,floor_max_nonnegative_real,Nat.floor_div_natCast,
      Nat.floor_div_natCast,Nat.floor_div_natCast]
    simp
  · rw [Nat.floor_div_natCast]
    simp

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma vaughan_squarefree_inner_density_error (U A B v r t s : ℕ)
    (hv : 1≤v) (hr : 1≤r) (ht : 1≤t) (hs : 1≤s) (hAB : A≤B) (hhalf : B≤2*A)
    (hrcap : r≤B/((U+1)*s)) (htcap : t≤B/((U+1)*s)) :
    |(∑ g∈Finset.Ioc (max (A/(r*t*s)) (max (U/r) (U/t))) (B/(r*t*s)),
        if Nat.Coprime g (r*t*v) then ((moebius g : ℤ) : ℝ)^2 else 0)-
      ((B : ℝ)/(r*t*s : ℕ)-max ((A : ℝ)/(r*t*s : ℕ)) (max ((U : ℝ)/r) ((U : ℝ)/t)))*
        (6/Real.pi^2)*(∏ p∈(r*t*v).primeFactors,(p : ℝ)/((p : ℝ)+1))|≤
      (127/100:ℝ)*Real.sqrt ((B : ℝ)/(r*t*s : ℕ))*
        (∏ p∈(r*t*v).primeFactors,(1+1/Real.sqrt (p : ℝ))) := by
  obtain ⟨ha,hab,hh,hfa,hfb⟩ := vaughan_squarefree_real_cutoffs U A B r t s hr ht hs hAB hhalf hrcap htcap
  have hq : r*t*v≠0 := Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos hr ht) hv)
  have h := squarefree_coprime_real_short_interval_euler_error (r*t*v)
    (max ((A : ℝ)/(r*t*s : ℕ)) (max ((U : ℝ)/r) ((U : ℝ)/t)))
    ((B : ℝ)/(r*t*s : ℕ)) hq ha hab hh
  rw [hfa,hfb] at h
  exact h

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma abs_triple_sum_le (S : Finset ℕ) (T : ℕ→Finset ℕ) (F : ℕ→ℕ→ℕ→ℝ) :
    |∑ s∈S,∑ r∈T s,∑ t∈T s,F s r t|≤∑ s∈S,∑ r∈T s,∑ t∈T s,|F s r t| := by
  calc
    _≤∑ s∈S,|∑ r∈T s,∑ t∈T s,F s r t| := abs_sum_le_sum_abs _ _
    _≤∑ s∈S,∑ r∈T s,|∑ t∈T s,F s r t| := by
      exact Finset.sum_le_sum (fun s hs => abs_sum_le_sum_abs _ _)
    _≤_ := by
      exact Finset.sum_le_sum (fun s hs => Finset.sum_le_sum (fun r hr => abs_sum_le_sum_abs _ _))

theorem actual_vaughan_mobius_interval_density_error (U A B v : ℕ)
    (hv : 1≤v) (hAB : A≤B) (hhalf : B≤2*A) :
    let rho : ℕ→ℝ := fun q => (6/Real.pi^2)*∏ p∈q.primeFactors,(p : ℝ)/((p : ℝ)+1)
    let omega : ℕ→ℝ := fun q => ∏ p∈q.primeFactors,(1+1/Real.sqrt (p : ℝ))
    let L : ℕ→ℕ→ℕ→ℝ := fun s r t => max ((A : ℝ)/(r*t*s : ℕ)) (max ((U : ℝ)/r) ((U : ℝ)/t))
    |(∑ m∈Finset.Ioc A B,if Nat.Coprime m v then
        ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)-
      (∑ s∈Finset.Icc 1 (B/(U+1)),∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
        if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
          ((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
            (((B : ℝ)/(r*t*s : ℕ)-L s r t)*rho (r*t*v)) else 0)|≤
      ∑ s∈Finset.Icc 1 (B/(U+1)),∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
        if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
          |((moebius r : ℤ) : ℝ)| *|((moebius t : ℤ) : ℝ)| *(127/100:ℝ)*
            Real.sqrt ((B : ℝ)/(r*t*s : ℕ))*omega (r*t*v) else 0 := by
  dsimp only
  rw [actual_vaughan_squarefree_count_reduction]
  simp_rw [←Finset.sum_sub_distrib]
  apply (abs_triple_sum_le _ _ _).trans
  apply Finset.sum_le_sum
  intro s hs
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro t ht
  by_cases hc : Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v
  · rw [if_pos hc,if_pos hc,if_pos hc,←mul_sub,abs_mul,abs_mul]
    have h := vaughan_squarefree_inner_density_error U A B v r t s hv
      (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp hs).1 hAB hhalf
      (Finset.mem_Icc.mp hr).2 (Finset.mem_Icc.mp ht).2
    have h' := mul_le_mul_of_nonneg_left h
      (mul_nonneg (abs_nonneg (((moebius r : ℤ) : ℝ))) (abs_nonneg (((moebius t : ℤ) : ℝ))))
    convert h' using 1 <;> ring
  · rw [if_neg hc,if_neg hc,if_neg hc,sub_self,abs_zero]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Finset Nat Real
open scoped BigOperators Classical

namespace Helfgott

lemma reciprocal_sqrt_nat_step (n : ℕ) (hn : 1≤n) :
    1/Real.sqrt (n : ℝ)≤2*(Real.sqrt (n : ℝ)-Real.sqrt ((n-1 : ℕ) : ℝ)) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have ha : 0<Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hb : 0≤Real.sqrt ((n-1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hsqA := Real.sq_sqrt hnR.le
  have hsqB := Real.sq_sqrt (show 0≤((n-1 : ℕ) : ℝ) by positivity)
  have hcast : ((n-1 : ℕ) : ℝ)=(n : ℝ)-1 := by rw [Nat.cast_sub hn,Nat.cast_one]
  apply (div_le_iff₀ ha).mpr
  nlinarith [hcast,sq_nonneg (Real.sqrt (n : ℝ)-Real.sqrt ((n-1 : ℕ) : ℝ))]

theorem reciprocal_sqrt_sum_le (N : ℕ) :
    (∑ n∈Finset.Icc 1 N,1/Real.sqrt (n : ℝ))≤2*Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1≤N+1)]
    have h := reciprocal_sqrt_nat_step (N+1) (by omega)
    simp only [Nat.add_sub_cancel] at h
    calc
      _≤2*Real.sqrt (N : ℝ)+2*(Real.sqrt ((N+1 : ℕ) : ℝ)-Real.sqrt (N : ℝ)) := add_le_add ih h
      _=_ := by ring

lemma reciprocal_sqrt_odd_step (k : ℕ) :
    1/Real.sqrt ((2*k+1 : ℕ) : ℝ)≤
      Real.sqrt ((2*k+1 : ℕ) : ℝ)-Real.sqrt ((2*k-1 : ℕ) : ℝ) := by
  by_cases hk : k=0
  · subst k;simp
  have hk1 : 1≤k := by omega
  have hnR : (0:ℝ)<((2*k+1 : ℕ) : ℝ) := by positivity
  have ha := Real.sqrt_pos.mpr hnR
  have hsqA := Real.sq_sqrt hnR.le
  have hsqB := Real.sq_sqrt (show 0≤((2*k-1 : ℕ) : ℝ) by positivity)
  have hcastA : ((2*k+1 : ℕ) : ℝ)=2*(k : ℝ)+1 := by push_cast;ring
  have hcastB : ((2*k-1 : ℕ) : ℝ)=2*(k : ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤2*k)];push_cast;ring
  apply (div_le_iff₀ ha).mpr
  nlinarith [hcastA,hcastB,sq_nonneg (Real.sqrt ((2*k+1 : ℕ) : ℝ)-Real.sqrt ((2*k-1 : ℕ) : ℝ))]

theorem reciprocal_sqrt_odd_sum_le (K : ℕ) :
    (∑ k∈Finset.range K,1/Real.sqrt ((2*k+1 : ℕ) : ℝ))≤Real.sqrt ((2*K-1 : ℕ) : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    calc
      _≤Real.sqrt ((2*K-1 : ℕ) : ℝ)+
          (Real.sqrt ((2*K+1 : ℕ) : ℝ)-Real.sqrt ((2*K-1 : ℕ) : ℝ)) := add_le_add ih (reciprocal_sqrt_odd_step K)
      _=Real.sqrt ((2*K+1 : ℕ) : ℝ) := by ring
      _=_ := by congr 2 <;> omega

lemma reciprocal_sqrt_coprime_two_sum_le (N : ℕ) :
    (∑ n∈Finset.Icc 1 N,if Nat.Coprime n 2 then 1/Real.sqrt (n : ℝ) else 0)≤Real.sqrt (N : ℝ) := by
  have heq : (∑ n∈Finset.Icc 1 N,if Nat.Coprime n 2 then 1/Real.sqrt (n : ℝ) else 0)=
      ∑ k∈Finset.range ((N+1)/2),1/Real.sqrt ((2*k+1 : ℕ) : ℝ) := by
    rw [←Finset.sum_filter]
    apply Finset.sum_bij (fun n hn => n/2)
    · intro n hn
      obtain ⟨hnI,hcop⟩ := Finset.mem_filter.mp hn
      have hnodd := Nat.coprime_two_right.mp hcop
      obtain ⟨k,hk⟩ := hnodd
      have hnlo := (Finset.mem_Icc.mp hnI).1
      have hnhi := (Finset.mem_Icc.mp hnI).2
      apply Finset.mem_range.mpr
      omega
    · intro n hn m hm hnm
      have hnc := (Finset.mem_filter.mp hn).2
      have hmc := (Finset.mem_filter.mp hm).2
      obtain ⟨k,hk⟩ := Nat.coprime_two_right.mp hnc
      obtain ⟨l,hl⟩ := Nat.coprime_two_right.mp hmc
      omega
    · intro k hk
      refine ⟨2*k+1,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by
        have := Finset.mem_range.mp hk;omega⟩,Nat.coprime_two_right.mpr ⟨k,by omega⟩⟩,by omega⟩
    · intro n hn
      have hcop := (Finset.mem_filter.mp hn).2
      obtain ⟨k,hk⟩ := Nat.coprime_two_right.mp hcop
      have he : n=2*(n/2)+1 := by omega
      rw [←he]
  rw [heq]
  exact (reciprocal_sqrt_odd_sum_le ((N+1)/2)).trans
    (Real.sqrt_le_sqrt (by exact_mod_cast (show 2*((N+1)/2)-1≤N by omega)))

end Helfgott
end

section
set_option autoImplicit false
open Finset
open scoped BigOperators Classical
namespace Helfgott

theorem finite_positive_divisor_reindex (B : ℕ) (F : ℕ → ℕ → ℝ) :
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

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma half_weighted_prime_product_mul (m n : ℕ) (hc : Nat.Coprime m n) :
    (∏ p∈(m*n).primeFactors,(1+1/Real.sqrt (p : ℝ)))=
      (∏ p∈m.primeFactors,(1+1/Real.sqrt (p : ℝ)))*
      (∏ p∈n.primeFactors,(1+1/Real.sqrt (p : ℝ))) := by
  rw [hc.primeFactors_mul,Finset.prod_union hc.disjoint_primeFactors]

lemma finite_divisor_reciprocal_sqrt_bound (Y : ℕ) :
    (∑ r∈Finset.Icc 1 Y,(∑ d∈r.divisors,1/Real.sqrt (d : ℝ))/Real.sqrt (r : ℝ))≤
      2*Real.sqrt (Y : ℝ)*(∑ d∈Finset.Icc 1 Y,1/((d : ℝ)*Real.sqrt (d : ℝ))) := by
  have hfactor (r d : ℕ) (hr : 1≤r) (hd : d∈r.divisors) :
      (1/Real.sqrt (d : ℝ))/Real.sqrt (r : ℝ)=
        (1/(d : ℝ))*(1/Real.sqrt ((r/d : ℕ) : ℝ)) := by
    have hpos : 0<d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hr
    have he : r=d*(r/d) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1).symm
    have hdR : (0:ℝ)<d := by exact_mod_cast hpos
    conv_lhs => rw [he]
    rw [Nat.cast_mul,Real.sqrt_mul hdR.le]
    have hs := Real.sq_sqrt hdR.le
    field_simp [hdR.ne', (Real.sqrt_pos.mpr hdR).ne']
    rw [hs]
  have hsum : (∑ r∈Finset.Icc 1 Y,(∑ d∈r.divisors,1/Real.sqrt (d : ℝ))/Real.sqrt (r : ℝ))=
      ∑ d∈Finset.Icc 1 Y,(1/(d : ℝ))*(∑ a∈Finset.Icc 1 (Y/d),1/Real.sqrt (a : ℝ)) := by
    simp_rw [Finset.sum_div]
    rw [Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (fun d hd => hfactor r d (Finset.mem_Icc.mp hr).1 hd)),
      finite_positive_divisor_reindex Y (fun d a => (1/(d : ℝ))*(1/Real.sqrt (a : ℝ)))]
    simp_rw [Finset.mul_sum]
  rw [hsum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hd1 := (Finset.mem_Icc.mp hd).1
  have hdR : (0:ℝ)<d := by exact_mod_cast hd1
  have hfloor : ((Y/d : ℕ) : ℝ)≤(Y : ℝ)/(d : ℝ) := by
    exact_mod_cast Nat.cast_div_le
  have hsqrt : Real.sqrt ((Y/d : ℕ) : ℝ)≤Real.sqrt (Y : ℝ)/Real.sqrt (d : ℝ) := by
    rw [←Real.sqrt_div (by positivity : (0:ℝ)≤Y)]
    exact Real.sqrt_le_sqrt hfloor
  have hsum := reciprocal_sqrt_sum_le (Y/d)
  calc
    _≤(1/(d : ℝ))*(2*Real.sqrt ((Y/d : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _≤(1/(d : ℝ))*(2*(Real.sqrt (Y : ℝ)/Real.sqrt (d : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) (by positivity)
    _=_ := by simp only [div_eq_mul_inv,mul_inv_rev];ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma finite_odd_divisor_reciprocal_sqrt_bound (Y : ℕ) :
    (∑ r∈Finset.Icc 1 Y,if Nat.Coprime r 2 then (∑ d∈r.divisors,1/Real.sqrt (d : ℝ))/Real.sqrt (r : ℝ) else 0)≤
      Real.sqrt (Y : ℝ)*(∑ d∈Finset.Icc 1 Y,if Nat.Coprime d 2 then 1/((d : ℝ)*Real.sqrt (d : ℝ)) else 0) := by
  have hfactor (r d : ℕ) (hr : 1≤r) (hd : d∈r.divisors) :
      (1/Real.sqrt (d : ℝ))/Real.sqrt (r : ℝ)=
        (1/(d : ℝ))*(1/Real.sqrt ((r/d : ℕ) : ℝ)) := by
    have hpos : 0<d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hr
    have he : r=d*(r/d) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1).symm
    have hdR : (0:ℝ)<d := by exact_mod_cast hpos
    conv_lhs => rw [he]
    rw [Nat.cast_mul,Real.sqrt_mul hdR.le]
    have hs := Real.sq_sqrt hdR.le
    field_simp [hdR.ne', (Real.sqrt_pos.mpr hdR).ne']
    rw [hs]
  have hsum : (∑ r∈Finset.Icc 1 Y,if Nat.Coprime r 2 then
      (∑ d∈r.divisors,1/Real.sqrt (d : ℝ))/Real.sqrt (r : ℝ) else 0)=
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d 2 then (1/(d : ℝ))*
        (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a 2 then 1/Real.sqrt (a : ℝ) else 0) else 0 := by
    have hfirst (r : ℕ) (hr : r∈Finset.Icc 1 Y) :
        (if Nat.Coprime r 2 then (∑ d∈r.divisors,1/Real.sqrt (d : ℝ))/Real.sqrt (r : ℝ) else 0)=
        ∑ d∈r.divisors,if Nat.Coprime d 2 ∧ Nat.Coprime (r/d) 2 then
          (1/(d : ℝ))*(1/Real.sqrt ((r/d : ℕ) : ℝ)) else 0 := by
      have he (d : ℕ) (hd : d∈r.divisors) :
          (Nat.Coprime d 2 ∧ Nat.Coprime (r/d) 2) ↔ Nat.Coprime r 2 := by
        rw [←Nat.coprime_mul_iff_left,Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
      by_cases hc : Nat.Coprime r 2
      · rw [if_pos hc,Finset.sum_div]
        apply Finset.sum_congr rfl
        intro d hd
        rw [if_pos ((he d hd).mpr hc)]
        exact hfactor r d (Finset.mem_Icc.mp hr).1 hd
      · rw [if_neg hc]
        symm
        exact Finset.sum_eq_zero (fun d hd => if_neg (fun h => hc ((he d hd).mp h)))
    rw [Finset.sum_congr rfl hfirst,
      finite_positive_divisor_reindex Y (fun d a => if Nat.Coprime d 2 ∧ Nat.Coprime a 2 then
        (1/(d : ℝ))*(1/Real.sqrt (a : ℝ)) else 0)]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hc : Nat.Coprime d 2
    · rw [if_pos hc,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hca : Nat.Coprime a 2
      · rw [if_pos ⟨hc,hca⟩,if_pos hca]
      · rw [if_neg (fun h => hca h.2),if_neg hca,mul_zero]
    · rw [if_neg hc]
      exact Finset.sum_eq_zero (fun a ha => if_neg (fun h => hc h.1))
  rw [hsum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  by_cases hc : Nat.Coprime d 2
  · rw [if_pos hc,if_pos hc]
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hdR : (0:ℝ)<d := by exact_mod_cast hd1
    have hfloor : ((Y/d : ℕ) : ℝ)≤(Y : ℝ)/(d : ℝ) := by exact_mod_cast Nat.cast_div_le
    have hsqrt : Real.sqrt ((Y/d : ℕ) : ℝ)≤Real.sqrt (Y : ℝ)/Real.sqrt (d : ℝ) := by
      rw [←Real.sqrt_div (by positivity : (0:ℝ)≤Y)]
      exact Real.sqrt_le_sqrt hfloor
    calc
      _≤(1/(d : ℝ))*Real.sqrt ((Y/d : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (reciprocal_sqrt_coprime_two_sum_le (Y/d)) (by positivity)
      _≤(1/(d : ℝ))*(Real.sqrt (Y : ℝ)/Real.sqrt (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _=_ := by simp only [div_eq_mul_inv,mul_inv_rev];ring
  · rw [if_neg hc,if_neg hc,mul_zero]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma half_weighted_prime_product_nonneg (r : ℕ) :
    0≤∏ p∈r.primeFactors,(1+1/Real.sqrt (p : ℝ)) := by
  exact Finset.prod_nonneg (fun p hp => by positivity)

lemma half_weighted_mobius_term_le_divisor_sum (r : ℕ) (hr : 1≤r) :
    |((moebius r : ℤ) : ℝ)| *(∏ p∈r.primeFactors,(1+1/Real.sqrt (p : ℝ)))/Real.sqrt (r : ℝ)≤
      (∑ d∈r.divisors,1/Real.sqrt (d : ℝ))/Real.sqrt (r : ℝ) := by
  have hmu : |((moebius r : ℤ) : ℝ)|≤1 := by exact_mod_cast abs_moebius_le_one (n:=r)
  have hprod : (∏ p∈r.primeFactors,(1+1/Real.sqrt (p : ℝ)))≤∑ d∈r.divisors,1/Real.sqrt (d : ℝ) := by
    rw [←moebius_half_weighted_divisor_euler_product r (by omega)]
    exact Finset.sum_le_sum (fun d hd => div_le_div_of_nonneg_right
      (show |((moebius d : ℤ) : ℝ)|≤1 by exact_mod_cast abs_moebius_le_one (n:=d)) (Real.sqrt_nonneg _))
  exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_right hmu
    (half_weighted_prime_product_nonneg r)).trans (by simpa only [one_mul] using hprod)) (Real.sqrt_nonneg _)

theorem half_weighted_mobius_sum_le_finite (Y : ℕ) :
    (∑ r∈Finset.Icc 1 Y,|((moebius r : ℤ) : ℝ)| *
      (∏ p∈r.primeFactors,(1+1/Real.sqrt (p : ℝ)))/Real.sqrt (r : ℝ))≤
      2*Real.sqrt (Y : ℝ)*(∑ d∈Finset.Icc 1 Y,1/((d : ℝ)*Real.sqrt (d : ℝ))) := by
  exact (Finset.sum_le_sum (fun r hr => half_weighted_mobius_term_le_divisor_sum r
    (Finset.mem_Icc.mp hr).1)).trans (finite_divisor_reciprocal_sqrt_bound Y)

lemma reciprocal_three_half_kernel (n : ℕ) :
    1/((n : ℝ)*Real.sqrt (n : ℝ))=(n : ℝ)^(-(3/2:ℝ)) := by
  by_cases hn : n=0
  · subst n;norm_num
  have hnR : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  symm
  rw [Real.rpow_neg hnR.le,show (3/2:ℝ)=1+1/2 by norm_num,
    Real.rpow_add hnR,Real.rpow_one,←Real.sqrt_eq_rpow]
  simp only [one_div]

lemma reciprocal_three_half_summable : Summable (fun n : ℕ => 1/((n : ℝ)*Real.sqrt (n : ℝ))) := by
  simp_rw [reciprocal_three_half_kernel]
  exact Real.summable_nat_rpow.mpr (by norm_num)

theorem half_weighted_mobius_sum_le_series (Y : ℕ) :
    (∑ r∈Finset.Icc 1 Y,|((moebius r : ℤ) : ℝ)| *
      (∏ p∈r.primeFactors,(1+1/Real.sqrt (p : ℝ)))/Real.sqrt (r : ℝ))≤
      2*Real.sqrt (Y : ℝ)*(∑' d : ℕ,1/((d : ℝ)*Real.sqrt (d : ℝ))) := by
  exact (half_weighted_mobius_sum_le_finite Y).trans
    (mul_le_mul_of_nonneg_left (reciprocal_three_half_summable.sum_le_tsum _ (fun d hd => by positivity)) (by positivity))

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma odd_reciprocal_three_half_summable :
    Summable (fun n : ℕ => if Nat.Coprime n 2 then 1/((n : ℝ)*Real.sqrt (n : ℝ)) else 0) := by
  apply Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) _ reciprocal_three_half_summable
  intro n
  split_ifs
  · exact le_rfl
  · positivity

lemma odd_reciprocal_three_half_nonneg :
    0 ≤ ∑' n : ℕ,if Nat.Coprime n 2 then 1/((n : ℝ)*Real.sqrt (n : ℝ)) else 0 := by
  exact tsum_nonneg (fun n => by split_ifs <;> positivity)

theorem odd_half_weighted_mobius_sum_le_series (Y : ℕ) :
    (∑ r∈Finset.Icc 1 Y,if Nat.Coprime r 2 then |((moebius r : ℤ) : ℝ)| *
      (∏ p∈r.primeFactors,(1+1/Real.sqrt (p : ℝ)))/Real.sqrt (r : ℝ) else 0) ≤
      Real.sqrt (Y : ℝ)*(∑' d : ℕ,if Nat.Coprime d 2 then 1/((d : ℝ)*Real.sqrt (d : ℝ)) else 0) := by
  have hfinite : (∑ r∈Finset.Icc 1 Y,if Nat.Coprime r 2 then |((moebius r : ℤ) : ℝ)| *
      (∏ p∈r.primeFactors,(1+1/Real.sqrt (p : ℝ)))/Real.sqrt (r : ℝ) else 0) ≤
      Real.sqrt (Y : ℝ)*(∑ d∈Finset.Icc 1 Y,if Nat.Coprime d 2 then 1/((d : ℝ)*Real.sqrt (d : ℝ)) else 0) := by
    apply (le_trans ?_ (finite_odd_divisor_reciprocal_sqrt_bound Y))
    apply Finset.sum_le_sum
    intro r hr
    by_cases hc : Nat.Coprime r 2
    · rw [if_pos hc,if_pos hc]
      exact half_weighted_mobius_term_le_divisor_sum r (Finset.mem_Icc.mp hr).1
    · rw [if_neg hc,if_neg hc]
  exact hfinite.trans (mul_le_mul_of_nonneg_left
    (odd_reciprocal_three_half_summable.sum_le_tsum _ (fun d hd => by split_ifs <;> positivity)) (Real.sqrt_nonneg _))

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma sqrt_ratio_three_factor (B r t s : ℕ) :
    Real.sqrt ((B : ℝ)/(r*t*s : ℕ))=
      Real.sqrt ((B : ℝ)/(s : ℝ))/(Real.sqrt (r : ℝ ) * Real.sqrt (t : ℝ)) := by
  rw [Real.sqrt_div (by positivity : (0:ℝ) ≤ B),Real.sqrt_div (by positivity : (0:ℝ) ≤ B)]
  simp only [Nat.cast_mul,Real.sqrt_mul (by positivity : (0:ℝ) ≤ (r : ℝ ) * (t : ℝ)),
    Real.sqrt_mul (by positivity : (0:ℝ) ≤ r),div_eq_mul_inv,mul_inv_rev]
  ring

lemma vaughan_density_error_block_factor (B v s Y : ℕ) (hv : 1 ≤ v) (hs : 1 ≤ s) :
    (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
        |((moebius r : ℤ) : ℝ)| * |((moebius t : ℤ) : ℝ)| * (127/100:ℝ ) * 
          Real.sqrt ((B : ℝ)/(r*t*s : ℕ) ) * 
          (∏ p∈(r*t*v).primeFactors,(1+1/Real.sqrt (p : ℝ))) else 0) ≤ 
      (127/100:ℝ ) * Real.sqrt ((B : ℝ)/(s : ℝ) ) * 
        (∏ p∈v.primeFactors,(1+1/Real.sqrt (p : ℝ)) ) * 
        (∑ r∈Finset.Icc 1 Y,|((moebius r : ℤ) : ℝ)| *
          (∏ p∈r.primeFactors,(1+1/Real.sqrt (p : ℝ)))/Real.sqrt (r : ℝ))^2 := by
  let F : ℕ→ℝ := fun r => |((moebius r : ℤ) : ℝ)| *
    (∏ p∈r.primeFactors,(1+1/Real.sqrt (p : ℝ)))/Real.sqrt (r : ℝ)
  let C : ℝ := (127/100:ℝ ) * Real.sqrt ((B : ℝ)/(s : ℝ) ) * 
    (∏ p∈v.primeFactors,(1+1/Real.sqrt (p : ℝ)))
  have hF (r : ℕ) : 0 ≤ F r := by
    dsimp [F]
    exact div_nonneg (mul_nonneg (abs_nonneg _) (half_weighted_prime_product_nonneg r)) (Real.sqrt_nonneg _)
  have hC : 0 ≤ C := by dsimp [C];exact mul_nonneg (by positivity) (half_weighted_prime_product_nonneg v)
  have hterm (r t : ℕ) :
      (if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
        |((moebius r : ℤ) : ℝ)| * |((moebius t : ℤ) : ℝ)| * (127/100:ℝ ) * 
          Real.sqrt ((B : ℝ)/(r*t*s : ℕ) ) * 
          (∏ p∈(r*t*v).primeFactors,(1+1/Real.sqrt (p : ℝ))) else 0) ≤ C*F r*F t := by
    by_cases hc : Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v
    · rw [if_pos hc]
      have hrtv : Nat.Coprime (r*t) v := hc.2.of_dvd_left (dvd_mul_right (r*t) s)
      rw [half_weighted_prime_product_mul (r*t) v hrtv,half_weighted_prime_product_mul r t hc.1,
        sqrt_ratio_three_factor]
      dsimp [C,F]
      simp only [div_eq_mul_inv,mul_inv_rev]
      exact le_of_eq (by ring)
    · rw [if_neg hc]
      exact mul_nonneg (mul_nonneg hC (hF r)) (hF t)
  calc
    _ ≤ ∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,C*F r*F t :=
      Finset.sum_le_sum (fun r hr => Finset.sum_le_sum (fun t ht => hterm r t))
    _=C*(∑ r∈Finset.Icc 1 Y,F r)^2 := by
      simp_rw [←Finset.mul_sum]
      rw [←Finset.sum_mul,←Finset.mul_sum]
      ring
    _=_ := rfl

lemma vaughan_density_error_block_series (B v s Y : ℕ) (hv : 1 ≤ v) (hs : 1 ≤ s) :
    (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
        |((moebius r : ℤ) : ℝ)| * |((moebius t : ℤ) : ℝ)| * (127/100:ℝ ) * 
          Real.sqrt ((B : ℝ)/(r*t*s : ℕ) ) * 
          (∏ p∈(r*t*v).primeFactors,(1+1/Real.sqrt (p : ℝ))) else 0) ≤ 
      (127/25:ℝ ) * Real.sqrt ((B : ℝ)/(s : ℝ) ) * 
        (∏ p∈v.primeFactors,(1+1/Real.sqrt (p : ℝ)) ) * (Y : ℝ ) * 
        (∑' d : ℕ,1/((d : ℝ ) * Real.sqrt (d : ℝ)))^2 := by
  have h := half_weighted_mobius_sum_le_series Y
  have hlo : 0 ≤ ∑ r∈Finset.Icc 1 Y,|((moebius r : ℤ) : ℝ)| *
      (∏ p∈r.primeFactors,(1+1/Real.sqrt (p : ℝ)))/Real.sqrt (r : ℝ) := by
    apply Finset.sum_nonneg
    intro r hr
    exact div_nonneg (mul_nonneg (abs_nonneg _) (half_weighted_prime_product_nonneg r)) (Real.sqrt_nonneg _)
  have hsq := sq_le_sq₀ hlo (by positivity : 0 ≤ 2*Real.sqrt (Y : ℝ ) * (∑' d : ℕ,1/((d : ℝ ) * Real.sqrt (d : ℝ)))) |>.mpr h
  have hC : 0 ≤ (127/100:ℝ ) * Real.sqrt ((B : ℝ)/(s : ℝ) ) * 
      (∏ p∈v.primeFactors,(1+1/Real.sqrt (p : ℝ))) :=
    mul_nonneg (by positivity) (half_weighted_prime_product_nonneg v)
  calc
    _ ≤ _ := vaughan_density_error_block_factor B v s Y hv hs
    _ ≤ ((127/100:ℝ ) * Real.sqrt ((B : ℝ)/(s : ℝ) ) * 
      (∏ p∈v.primeFactors,(1+1/Real.sqrt (p : ℝ))) ) * 
      (2*Real.sqrt (Y : ℝ ) * (∑' d : ℕ,1/((d : ℝ ) * Real.sqrt (d : ℝ))))^2 := mul_le_mul_of_nonneg_left hsq hC
    _=_ := by rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity : (0:ℝ) ≤ Y)];ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma vaughan_odd_density_error_block_factor (B s Y : ℕ) (hs : 1 ≤ s) (hsOdd : Nat.Coprime s 2) :
    (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) 2 then
        |((moebius r : ℤ) : ℝ)| * |((moebius t : ℤ) : ℝ)| * (127/100:ℝ ) * 
          Real.sqrt ((B : ℝ)/(r*t*s : ℕ) ) * 
          (∏ p∈(r*t*2).primeFactors,(1+1/Real.sqrt (p : ℝ))) else 0) ≤ 
      (127/100:ℝ ) * Real.sqrt ((B : ℝ)/(s : ℝ) ) * 
        (∏ p∈(2 : ℕ).primeFactors,(1+1/Real.sqrt (p : ℝ)) ) * 
        (∑ r∈Finset.Icc 1 Y,if Nat.Coprime r 2 then |((moebius r : ℤ) : ℝ)| *
          (∏ p∈r.primeFactors,(1+1/Real.sqrt (p : ℝ)))/Real.sqrt (r : ℝ) else 0)^2 := by
  let F : ℕ→ℝ := fun r => if Nat.Coprime r 2 then |((moebius r : ℤ) : ℝ)| *
    (∏ p∈r.primeFactors,(1+1/Real.sqrt (p : ℝ)))/Real.sqrt (r : ℝ) else 0
  let C : ℝ := (127/100:ℝ ) * Real.sqrt ((B : ℝ)/(s : ℝ) ) * 
    (∏ p∈(2 : ℕ).primeFactors,(1+1/Real.sqrt (p : ℝ)))
  have hF (r : ℕ) : 0 ≤ F r := by
    dsimp [F]
    split_ifs
    · exact div_nonneg (mul_nonneg (abs_nonneg _) (half_weighted_prime_product_nonneg r)) (Real.sqrt_nonneg _)
    · exact le_rfl
  have hC : 0 ≤ C := by dsimp [C];exact mul_nonneg (by positivity) (half_weighted_prime_product_nonneg 2)
  have hterm (r t : ℕ) :
      (if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) 2 then
        |((moebius r : ℤ) : ℝ)| * |((moebius t : ℤ) : ℝ)| * (127/100:ℝ ) * 
          Real.sqrt ((B : ℝ)/(r*t*s : ℕ) ) * 
          (∏ p∈(r*t*2).primeFactors,(1+1/Real.sqrt (p : ℝ))) else 0) ≤ C*F r*F t := by
    by_cases hc : Nat.Coprime r t ∧ Nat.Coprime (r*t*s) 2
    · rw [if_pos hc]
      have hrtv : Nat.Coprime (r*t) 2 := hc.2.of_dvd_left (dvd_mul_right (r*t) s)
      rw [half_weighted_prime_product_mul (r*t) 2 hrtv,half_weighted_prime_product_mul r t hc.1,
        sqrt_ratio_three_factor]
      have hrOdd : Nat.Coprime r 2 := hrtv.of_dvd_left (dvd_mul_right r t)
      have htOdd : Nat.Coprime t 2 := hrtv.of_dvd_left (dvd_mul_left t r)
      dsimp only [C,F]
      rw [if_pos hrOdd,if_pos htOdd]
      simp only [div_eq_mul_inv,mul_inv_rev]
      exact le_of_eq (by ring)
    · rw [if_neg hc]
      exact mul_nonneg (mul_nonneg hC (hF r)) (hF t)
  calc
    _ ≤ ∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,C*F r*F t :=
      Finset.sum_le_sum (fun r hr => Finset.sum_le_sum (fun t ht => hterm r t))
    _=C*(∑ r∈Finset.Icc 1 Y,F r)^2 := by
      simp_rw [←Finset.mul_sum]
      rw [←Finset.sum_mul,←Finset.mul_sum]
      ring
    _=_ := rfl

lemma vaughan_odd_density_error_block_series (B s Y : ℕ) (hs : 1 ≤ s) (hsOdd : Nat.Coprime s 2) :
    (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) 2 then
        |((moebius r : ℤ) : ℝ)| * |((moebius t : ℤ) : ℝ)| * (127/100:ℝ)*
          Real.sqrt ((B : ℝ)/(r*t*s : ℕ))*
          (∏ p∈(r*t*2).primeFactors,(1+1/Real.sqrt (p : ℝ))) else 0) ≤
      (127/100:ℝ)*Real.sqrt ((B : ℝ)/(s : ℝ))*
        (∏ p∈(2 : ℕ).primeFactors,(1+1/Real.sqrt (p : ℝ)))*(Y : ℝ)*
        (∑' d : ℕ,if Nat.Coprime d 2 then 1/((d : ℝ)*Real.sqrt (d : ℝ)) else 0)^2 := by
  have h := odd_half_weighted_mobius_sum_le_series Y
  have hlo : 0 ≤ ∑ r∈Finset.Icc 1 Y,if Nat.Coprime r 2 then |((moebius r : ℤ) : ℝ)| *
      (∏ p∈r.primeFactors,(1+1/Real.sqrt (p : ℝ)))/Real.sqrt (r : ℝ) else 0 := by
    apply Finset.sum_nonneg
    intro r hr
    split_ifs
    · exact div_nonneg (mul_nonneg (abs_nonneg _) (half_weighted_prime_product_nonneg r)) (Real.sqrt_nonneg _)
    · exact le_rfl
  have hhi : 0 ≤ Real.sqrt (Y : ℝ)*(∑' d : ℕ,if Nat.Coprime d 2 then 1/((d : ℝ)*Real.sqrt (d : ℝ)) else 0) :=
    mul_nonneg (Real.sqrt_nonneg _) odd_reciprocal_three_half_nonneg
  have hsq := (sq_le_sq₀ hlo hhi).mpr h
  have hC : 0 ≤ (127/100:ℝ)*Real.sqrt ((B : ℝ)/(s : ℝ))*
      (∏ p∈(2 : ℕ).primeFactors,(1+1/Real.sqrt (p : ℝ))) :=
    mul_nonneg (by positivity) (half_weighted_prime_product_nonneg 2)
  calc
    _ ≤ _ := vaughan_odd_density_error_block_factor B s Y hs hsOdd
    _ ≤ ((127/100:ℝ)*Real.sqrt ((B : ℝ)/(s : ℝ))*
      (∏ p∈(2 : ℕ).primeFactors,(1+1/Real.sqrt (p : ℝ))))*
      (Real.sqrt (Y : ℝ)*(∑' d : ℕ,if Nat.Coprime d 2 then 1/((d : ℝ)*Real.sqrt (d : ℝ)) else 0))^2 := mul_le_mul_of_nonneg_left hsq hC
    _=_ := by rw [mul_pow,Real.sq_sqrt (by positivity : (0:ℝ) ≤ Y)];ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma vaughan_odd_density_cofactor_sum_bound (U B : ℕ) :
    (∑ s∈Finset.Icc 1 (B/(U+1)),if Nat.Coprime s 2 then
      ((B/((U+1)*s) : ℕ) : ℝ)*Real.sqrt ((B : ℝ)/(s : ℝ)) else 0) ≤
      ((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ))*
        (∑' s : ℕ,if Nat.Coprime s 2 then 1/((s : ℝ)*Real.sqrt (s : ℝ)) else 0) := by
  have ht (s : ℕ) (hs : s∈Finset.Icc 1 (B/(U+1))) :
      ((B/((U+1)*s) : ℕ) : ℝ)*Real.sqrt ((B : ℝ)/(s : ℝ)) ≤
        ((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ))*(1/((s : ℝ)*Real.sqrt (s : ℝ))) := by
    have hs1 := (Finset.mem_Icc.mp hs).1
    have hdiv : ((B/((U+1)*s) : ℕ) : ℝ)≤(B : ℝ)/((U+1)*s : ℕ) := Nat.cast_div_le
    calc
      _ ≤ ((B : ℝ)/((U+1)*s : ℕ))*Real.sqrt ((B : ℝ)/(s : ℝ)) :=
        mul_le_mul_of_nonneg_right hdiv (Real.sqrt_nonneg _)
      _=_ := by
        rw [Real.sqrt_div (by positivity : (0:ℝ)≤B),Nat.cast_mul]
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
  have hC : 0≤(B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ) := by positivity
  calc
    _ ≤ ∑ s∈Finset.Icc 1 (B/(U+1)),
        ((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ))*
          (if Nat.Coprime s 2 then 1/((s : ℝ)*Real.sqrt (s : ℝ)) else 0) := by
      apply Finset.sum_le_sum
      intro s hs
      by_cases hc : Nat.Coprime s 2
      · rw [if_pos hc,if_pos hc]
        exact ht s hs
      · rw [if_neg hc,if_neg hc,mul_zero]
    _=((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ))*
        (∑ s∈Finset.Icc 1 (B/(U+1)),if Nat.Coprime s 2 then 1/((s : ℝ)*Real.sqrt (s : ℝ)) else 0) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (odd_reciprocal_three_half_summable.sum_le_tsum _ (fun s hs => by split_ifs <;> positivity)) hC

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem actual_vaughan_odd_mobius_interval_density_uniform_error (U A B : ℕ)
     (hAB : A ≤ B) (hhalf : B ≤ 2*A) :
    let rho : ℕ→ℝ := fun q => (6/Real.pi^2)*∏ p∈q.primeFactors,(p : ℝ)/((p : ℝ)+1)
    let omega : ℕ→ℝ := fun q => ∏ p∈q.primeFactors,(1+1/Real.sqrt (p : ℝ))
    let L : ℕ→ℕ→ℕ→ℝ := fun s r t => max ((A : ℝ)/(r*t*s : ℕ)) (max ((U : ℝ)/r) ((U : ℝ)/t))
    |(∑ m∈Finset.Ioc A B,if Nat.Coprime m 2 then
        ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)-
      (∑ s∈Finset.Icc 1 (B/(U+1)),∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
        if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) 2 then
          ((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
            (((B : ℝ)/(r*t*s : ℕ)-L s r t)*rho (r*t*2)) else 0)| ≤
      (127/100:ℝ)*omega 2*(∑' d : ℕ,if Nat.Coprime d 2 then 1/((d : ℝ)*Real.sqrt (d : ℝ)) else 0)^3*
        ((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := by
  dsimp only
  let Z : ℝ := ∑' d : ℕ,if Nat.Coprime d 2 then 1/((d : ℝ)*Real.sqrt (d : ℝ)) else 0
  let W : ℝ := ∏ p∈(2 : ℕ).primeFactors,(1+1/Real.sqrt (p : ℝ))
  let C : ℝ := (127/100:ℝ)*W*Z^2
  have hC : 0 ≤ C := by
    dsimp [C,W]
    exact mul_nonneg (mul_nonneg (by norm_num) (half_weighted_prime_product_nonneg 2)) (sq_nonneg _)
  apply (actual_vaughan_mobius_interval_density_error U A B 2 (by norm_num) hAB hhalf).trans
  have hblock (s : ℕ) (hs : s∈Finset.Icc 1 (B/(U+1))) :
      (∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
        if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) 2 then
          |((moebius r : ℤ) : ℝ)| * |((moebius t : ℤ) : ℝ)| * (127/100:ℝ)*
            Real.sqrt ((B : ℝ)/(r*t*s : ℕ))*
            (∏ p∈(r*t*2).primeFactors,(1+1/Real.sqrt (p : ℝ))) else 0) ≤
      C*(if Nat.Coprime s 2 then ((B/((U+1)*s) : ℕ) : ℝ)*Real.sqrt ((B : ℝ)/(s : ℝ)) else 0) := by
    by_cases hodd : Nat.Coprime s 2
    · rw [if_pos hodd]
      have h := vaughan_odd_density_error_block_series B s (B/((U+1)*s)) (Finset.mem_Icc.mp hs).1 hodd
      dsimp [C,W,Z]
      convert h using 1 <;> ring
    · rw [if_neg hodd,mul_zero]
      have hz : (∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
        if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) 2 then
          |((moebius r : ℤ) : ℝ)| * |((moebius t : ℤ) : ℝ)| * (127/100:ℝ)*
            Real.sqrt ((B : ℝ)/(r*t*s : ℕ))*
            (∏ p∈(r*t*2).primeFactors,(1+1/Real.sqrt (p : ℝ))) else 0)=0 := by
        apply Finset.sum_eq_zero
        intro r hr
        apply Finset.sum_eq_zero
        intro t ht
        exact if_neg (fun h => hodd (h.2.of_dvd_left (dvd_mul_left s (r*t))))
      rw [hz]
  calc
    _ ≤ ∑ s∈Finset.Icc 1 (B/(U+1)),
        C*(if Nat.Coprime s 2 then ((B/((U+1)*s) : ℕ) : ℝ)*Real.sqrt ((B : ℝ)/(s : ℝ)) else 0) := Finset.sum_le_sum hblock
    _=C*(∑ s∈Finset.Icc 1 (B/(U+1)),if Nat.Coprime s 2 then ((B/((U+1)*s) : ℕ) : ℝ)*Real.sqrt ((B : ℝ)/(s : ℝ)) else 0) := (Finset.mul_sum _ _ _).symm
    _ ≤ C*(((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ))*Z) := mul_le_mul_of_nonneg_left (vaughan_odd_density_cofactor_sum_bound U B) hC
    _=_ := by dsimp [C,W,Z];ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat Real MeasureTheory
open scoped BigOperators Classical
namespace Helfgott

lemma reciprocal_three_half_tail_thirtyone :
    (∑' n : ℕ,1/(((n+32 : ℕ) : ℝ)*Real.sqrt ((n+32 : ℕ) : ℝ))) ≤ 2*(31:ℝ)^(-(1/2:ℝ)) := by
  have ha : AntitoneOn (fun x : ℝ => x^(-(3/2:ℝ))) (Set.Ici (31:ℝ)) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos (by change (31:ℝ) ≤ a at ha;linarith) hab (by norm_num)
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3/2:ℝ)) < -1) (by norm_num : (0:ℝ)<31)
  have ht := ha.tsum_comp_add_le_integral 31 hi (fun x hx => Real.rpow_nonneg
    (by change (31:ℝ)<x at hx;linarith) _)
  norm_num only [Nat.cast_ofNat] at ht
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-(3/2:ℝ)) < -1) (by norm_num : (0:ℝ)<31)] at ht
  norm_num only at ht
  simp_rw [reciprocal_three_half_kernel]
  exact ht.trans_eq (by ring)

lemma odd_reciprocal_three_half_tail_le :
    (∑' n : ℕ,if Nat.Coprime (n+32) 2 then
      1/(((n+32 : ℕ) : ℝ)*Real.sqrt ((n+32 : ℕ) : ℝ)) else 0) ≤ (31:ℝ)^(-(1/2:ℝ)) := by
  let f : ℕ→ℝ := fun n => 1/(((n+32 : ℕ) : ℝ)*Real.sqrt ((n+32 : ℕ) : ℝ))
  have hf : Summable f := (summable_nat_add_iff 32).mpr reciprocal_three_half_summable
  have he : Summable (fun n => f (2*n)) := hf.comp_injective (by intro a b h;omega)
  have ho : Summable (fun n => f (2*n+1)) := hf.comp_injective (by intro a b h;dsimp at h;omega)
  have hsum := tsum_even_add_odd (f:=f) he ho
  have hanti (n : ℕ) : f (2*n+1) ≤ f (2*n) := by
    dsimp [f]
    simp_rw [reciprocal_three_half_kernel]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast;linarith) (by norm_num)
  have hle := ho.tsum_le_tsum hanti he
  have htotal : (∑' n : ℕ,f (2*n+1)) ≤ (31:ℝ)^(-(1/2:ℝ)) := by
    have ht := reciprocal_three_half_tail_thirtyone
    change (∑' n : ℕ,f n) ≤ _ at ht
    linarith
  have hg : Summable (fun n : ℕ => if Nat.Coprime (n+32) 2 then f n else 0) := by
    apply Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) _ hf
    intro n;split_ifs
    · exact le_rfl
    · dsimp [f];positivity
  have hge : Summable (fun n : ℕ => if Nat.Coprime (2*n+32) 2 then f (2*n) else 0) := by
    exact hg.comp_injective (by intro a b h;omega)
  have hgo : Summable (fun n : ℕ => if Nat.Coprime (2*n+1+32) 2 then f (2*n+1) else 0) := by
    exact hg.comp_injective (by intro a b h;dsimp at h;omega)
  have hi := tsum_even_add_odd (f:=fun n : ℕ => if Nat.Coprime (n+32) 2 then f n else 0) hge hgo
  have hzero (n : ℕ) : ¬Nat.Coprime (2*n+32) 2 := by
    rw [Nat.coprime_two_right]
    rintro ⟨k,hk⟩
    omega
  have hone (n : ℕ) : Nat.Coprime (2*n+1+32) 2 := Nat.coprime_two_right.mpr ⟨n+16,by omega⟩
  simp only [if_neg (hzero _),if_pos (hone _),tsum_zero,zero_add] at hi
  change (∑' n : ℕ,if Nat.Coprime (n+32) 2 then f n else 0) ≤ _
  rw [←hi]
  exact htotal

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat Real
open scoped BigOperators Classical
namespace Helfgott

lemma reciprocal_three_half_of_certificate (n c t : ℕ) (hn : 1 ≤ n) (hc : 1 ≤ c)
    (hroot : c^2 ≤ n*10^12) (ht : 10^15 ≤ t*n*c) :
    1/((n : ℝ)*Real.sqrt (n : ℝ)) ≤ (t : ℝ)/1000000000 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hcR : (0:ℝ)<c := by exact_mod_cast hc
  have hrootR : (c : ℝ)^2 ≤ (n : ℝ)*10^12 := by exact_mod_cast hroot
  have htR : (10^15:ℝ) ≤ (t : ℝ)*(n : ℝ)*(c : ℝ) := by exact_mod_cast ht
  have hs := Real.sq_sqrt hnR.le
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  have hlow : (c : ℝ)/1000000 ≤ Real.sqrt (n : ℝ) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hlow (show 0 ≤ (t : ℝ)*(n : ℝ) by positivity)
  apply (div_le_iff₀ (mul_pos hnR (Real.sqrt_pos.mpr hnR))).mpr
  nlinarith

structure OddSeriesBoundRow where
  n : ℕ
  c : ℕ
  t : ℕ
  deriving DecidableEq

def oddSeriesRows : Finset OddSeriesBoundRow :=
  {⟨1,1000000,1000000000⟩,⟨3,1732050,192450180⟩,⟨5,2236067,89442759⟩,⟨7,2645751,53994932⟩,
   ⟨9,3000000,37037038⟩,⟨11,3316624,27410129⟩,⟨13,3605551,21334625⟩,⟨15,3872983,17213261⟩,
   ⟨17,4123105,14266804⟩,⟨19,4358898,12074515⟩,⟨21,4582575,10391330⟩,⟨23,4795831,9065846⟩,
   ⟨25,5000000,8000000⟩,⟨27,5196152,7127782⟩,⟨29,5385164,6403289⟩,⟨31,5567764,5793720⟩}

lemma oddSeriesRows_checked : ∀ row∈oddSeriesRows,
    1 ≤ row.n ∧ 1 ≤ row.c ∧ row.c^2 ≤ row.n*10^12 ∧ 10^15 ≤ row.t*row.n*row.c := by
  decide +kernel

lemma oddSeriesRows_exact : ((Finset.range 32).filter (fun n => Nat.Coprime n 2))=
    oddSeriesRows.image OddSeriesBoundRow.n := by decide +kernel

lemma oddSeriesRows_injective : ∀ r∈oddSeriesRows,∀ t∈oddSeriesRows,r.n = t.n → r = t := by decide +kernel

lemma oddSeriesRows_sum_upper : (∑ row∈oddSeriesRows,row.t) ≤ 1520000000 := by decide +kernel

lemma odd_reciprocal_three_half_prefix_le :
    (∑ n∈Finset.range 32,if Nat.Coprime n 2 then 1/((n : ℝ)*Real.sqrt (n : ℝ)) else 0) ≤ (38/25:ℝ) := by
  rw [←Finset.sum_filter,oddSeriesRows_exact,Finset.sum_image oddSeriesRows_injective]
  calc
    _ ≤ ∑ row∈oddSeriesRows,(row.t : ℝ)/1000000000 := by
      apply Finset.sum_le_sum
      intro row hrow
      obtain ⟨hn,hc,hr,ht⟩ := oddSeriesRows_checked row hrow
      exact reciprocal_three_half_of_certificate row.n row.c row.t hn hc hr ht
    _ ≤ _ := by
      rw [←Finset.sum_div]
      have h : (∑ row∈oddSeriesRows,(row.t : ℝ)) ≤ (1520000000:ℝ) := by exact_mod_cast oddSeriesRows_sum_upper
      exact (div_le_div_of_nonneg_right h (by norm_num)).trans_eq (by norm_num)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat Real
open scoped BigOperators Classical
namespace Helfgott

theorem odd_reciprocal_three_half_le_seventeen_tenths :
    (∑' n : ℕ,if Nat.Coprime n 2 then 1/((n : ℝ)*Real.sqrt (n : ℝ)) else 0) ≤ (17/10:ℝ) := by
  have hsplit := odd_reciprocal_three_half_summable.sum_add_tsum_nat_add 32
  have hp := odd_reciprocal_three_half_prefix_le
  have ht := odd_reciprocal_three_half_tail_le
  have hr : (31:ℝ)^(-(1/2:ℝ)) ≤ (9/50:ℝ) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 31),←Real.sqrt_eq_rpow]
    have hroot : (50/9:ℝ) ≤ Real.sqrt 31 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 31),Real.sqrt_nonneg (31:ℝ)]
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<50/9) hroot
    norm_num at h
    exact h
  linarith

lemma odd_vaughan_density_error_constant_le :
    (127/100:ℝ)*(∏ p∈(2 : ℕ).primeFactors,(1+1/Real.sqrt (p : ℝ)))*
      (∑' n : ℕ,if Nat.Coprime n 2 then 1/((n : ℝ)*Real.sqrt (n : ℝ)) else 0)^3 ≤ (107/10:ℝ) := by
  have hz := odd_reciprocal_three_half_le_seventeen_tenths
  have hzn := odd_reciprocal_three_half_nonneg
  have hw : (∏ p∈(2 : ℕ).primeFactors,(1+1/Real.sqrt (p : ℝ))) ≤ (171/100:ℝ) := by
    rw [Nat.prime_two.primeFactors,Finset.prod_singleton]
    norm_num only [Nat.cast_ofNat,one_div]
    have hroot : (100/71:ℝ) ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<100/71) hroot
    norm_num at h
    linarith
  calc
    _ ≤ (127/100:ℝ)*(171/100)*(17/10)^3 := by gcongr
    _ ≤ _ := by norm_num

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem actual_vaughan_odd_mobius_interval_density_decimal_error (U A B : ℕ)
     (hAB : A ≤ B) (hhalf : B ≤ 2*A) :
    let rho : ℕ→ℝ := fun q => (6/Real.pi^2)*∏ p∈q.primeFactors,(p : ℝ)/((p : ℝ)+1)
    let omega : ℕ→ℝ := fun q => ∏ p∈q.primeFactors,(1+1/Real.sqrt (p : ℝ))
    let L : ℕ→ℕ→ℕ→ℝ := fun s r t => max ((A : ℝ)/(r*t*s : ℕ)) (max ((U : ℝ)/r) ((U : ℝ)/t))
    |(∑ m∈Finset.Ioc A B,if Nat.Coprime m 2 then
        ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)-
      (∑ s∈Finset.Icc 1 (B/(U+1)),∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
        if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) 2 then
          ((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
            (((B : ℝ)/(r*t*s : ℕ)-L s r t)*rho (r*t*2)) else 0)| ≤
      (107/10:ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := by
  dsimp only
  exact (actual_vaughan_odd_mobius_interval_density_uniform_error U A B hAB hhalf).trans
    (mul_le_mul_of_nonneg_right odd_vaughan_density_error_constant_le (by positivity))

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma prime_ratio_product_mul (m n : ℕ) (hc : Nat.Coprime m n) :
    (∏ p∈(m*n).primeFactors,(p : ℝ)/((p : ℝ)+1))=
      (∏ p∈m.primeFactors,(p : ℝ)/((p : ℝ)+1))*
      (∏ p∈n.primeFactors,(p : ℝ)/((p : ℝ)+1)) := by
  rw [hc.primeFactors_mul,Finset.prod_union hc.disjoint_primeFactors]

lemma signed_mobius_prime_ratio_normalization (n : ℕ) :
    ((moebius n : ℤ) : ℝ)*(∏ p∈n.primeFactors,(p : ℝ)/((p : ℝ)+1))=
      ((moebius n : ℤ) : ℝ)*(n : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1)) := by
  by_cases hn : Squarefree n
  · rw [Finset.prod_div_distrib,←Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hn]
    ring
  · rw [moebius_eq_zero_of_not_squarefree hn]
    simp

lemma signed_mobius_pair_density_normalization (r t v : ℕ)
    (hrt : Nat.Coprime r t) (hrtv : Nat.Coprime (r*t) v) :
    ((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
      ((6/Real.pi^2)*(∏ p∈(r*t*v).primeFactors,(p : ℝ)/((p : ℝ)+1)))=
      ((6/Real.pi^2)*(∏ p∈v.primeFactors,(p : ℝ)/((p : ℝ)+1)))*
      (((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)))*
      (((moebius t : ℤ) : ℝ)/(∏ p∈t.primeFactors,((p : ℝ)+1)))*(r : ℝ)*(t : ℝ) := by
  rw [prime_ratio_product_mul (r*t) v hrtv,prime_ratio_product_mul r t hrt]
  have hr := signed_mobius_prime_ratio_normalization r
  have ht := signed_mobius_prime_ratio_normalization t
  calc
    _=(6/Real.pi^2)*(∏ p∈v.primeFactors,(p : ℝ)/((p : ℝ)+1))*
      (((moebius r : ℤ) : ℝ)*(∏ p∈r.primeFactors,(p : ℝ)/((p : ℝ)+1)))*
      (((moebius t : ℤ) : ℝ)*(∏ p∈t.primeFactors,(p : ℝ)/((p : ℝ)+1))) := by ring
    _=_ := by rw [hr,ht];ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma density_cutoff_product_normalization (U A B r t s : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hs : 1 ≤ s) :
    (r : ℝ)*(t : ℝ)*((B : ℝ)/(r*t*s : ℕ)-
      max ((A : ℝ)/(r*t*s : ℕ)) (max ((U : ℝ)/r) ((U : ℝ)/t)))=
      (B : ℝ)/(s : ℝ)-max ((A : ℝ)/(s : ℝ)) (max ((U : ℝ)*t) ((U : ℝ)*r)) := by
  have hr0 : (r : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hr
  have ht0 : (t : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt ht
  have hs0 : (s : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hs
  have hp : 0 ≤ (r : ℝ)*(t : ℝ) := by positivity
  rw [mul_assoc,←mul_assoc,mul_sub,mul_max_of_nonneg _ _ hp,mul_max_of_nonneg _ _ hp]
  have hB : (r : ℝ)*(t : ℝ)*((B : ℝ)/(r*t*s : ℕ))=(B : ℝ)/(s : ℝ) := by
    push_cast;field_simp <;> ring
  have hA : (r : ℝ)*(t : ℝ)*((A : ℝ)/(r*t*s : ℕ))=(A : ℝ)/(s : ℝ) := by
    push_cast;field_simp <;> ring
  have hUr : (r : ℝ)*(t : ℝ)*((U : ℝ)/r)=(U : ℝ)*t := by field_simp <;> ring
  have hUt : (r : ℝ)*(t : ℝ)*((U : ℝ)/t)=(U : ℝ)*r := by field_simp <;> ring
  rw [hB,hA,hUr,hUt]

lemma signed_mobius_interval_density_normalization (U A B r t s v : ℕ)
    (hr : 1 ≤ r) (ht : 1 ≤ t) (hs : 1 ≤ s)
    (hrt : Nat.Coprime r t) (hrtv : Nat.Coprime (r*t) v) :
    ((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
      (((B : ℝ)/(r*t*s : ℕ)-max ((A : ℝ)/(r*t*s : ℕ)) (max ((U : ℝ)/r) ((U : ℝ)/t)))*
        ((6/Real.pi^2)*(∏ p∈(r*t*v).primeFactors,(p : ℝ)/((p : ℝ)+1))))=
      ((6/Real.pi^2)*(∏ p∈v.primeFactors,(p : ℝ)/((p : ℝ)+1)))*
      (((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)))*
      (((moebius t : ℤ) : ℝ)/(∏ p∈t.primeFactors,((p : ℝ)+1)))*
      ((B : ℝ)/(s : ℝ)-max ((A : ℝ)/(s : ℝ)) (max ((U : ℝ)*t) ((U : ℝ)*r))) := by
  have hd := signed_mobius_pair_density_normalization r t v hrt hrtv
  calc
    _=(((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
      ((6/Real.pi^2)*(∏ p∈(r*t*v).primeFactors,(p : ℝ)/((p : ℝ)+1))))*
      ((B : ℝ)/(r*t*s : ℕ)-max ((A : ℝ)/(r*t*s : ℕ)) (max ((U : ℝ)/r) ((U : ℝ)/t))) := by ring
    _=_ := by
      rw [hd]
      linear_combination
        ((6/Real.pi^2)*(∏ p∈v.primeFactors,(p : ℝ)/((p : ℝ)+1)))*
        (((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)))*
        (((moebius t : ℤ) : ℝ)/(∏ p∈t.primeFactors,((p : ℝ)+1)))*
        (density_cutoff_product_normalization U A B r t s hr ht hs)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma actual_vaughan_signed_density_main_normalization (U A B v : ℕ) :
    let rho : ℕ→ℝ := fun q => (6/Real.pi^2)*∏ p∈q.primeFactors,(p : ℝ)/((p : ℝ)+1)
    let sigma : ℕ→ℝ := fun q => ∏ p∈q.primeFactors,((p : ℝ)+1)
    let L : ℕ→ℕ→ℕ→ℝ := fun s r t => max ((A : ℝ)/(r*t*s : ℕ)) (max ((U : ℝ)/r) ((U : ℝ)/t))
    (∑ s∈Finset.Icc 1 (B/(U+1)),∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
      if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
        ((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
          (((B : ℝ)/(r*t*s : ℕ)-L s r t)*rho (r*t*v)) else 0)=
      rho v*(∑ s∈Finset.Icc 1 (B/(U+1)),∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
        if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
          (((moebius r : ℤ) : ℝ)/sigma r)*(((moebius t : ℤ) : ℝ)/sigma t)*
            ((B : ℝ)/(s : ℝ)-max ((A : ℝ)/(s : ℝ)) (max ((U : ℝ)*t) ((U : ℝ)*r))) else 0) := by
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hc : Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v
  · rw [if_pos hc,if_pos hc]
    simpa only [mul_assoc] using signed_mobius_interval_density_normalization U A B r t s v
      (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp hs).1 hc.1
      (hc.2.of_dvd_left (dvd_mul_right (r*t) s))
  · rw [if_neg hc,if_neg hc,mul_zero]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem actual_vaughan_odd_mobius_normalized_density_error (U A B : ℕ)
    (hAB : A ≤ B) (hhalf : B ≤ 2*A) :
    let sigma : ℕ→ℝ := fun q => ∏ p∈q.primeFactors,((p : ℝ)+1)
    |(∑ m∈Finset.Ioc A B,if Nat.Coprime m 2 then
        ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)-
      (4/Real.pi^2)*(∑ s∈Finset.Icc 1 (B/(U+1)),
        ∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
          if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) 2 then
            (((moebius r : ℤ) : ℝ)/sigma r)*(((moebius t : ℤ) : ℝ)/sigma t)*
              ((B : ℝ)/(s : ℝ)-max ((A : ℝ)/(s : ℝ)) (max ((U : ℝ)*t) ((U : ℝ)*r))) else 0)| ≤
      (107/10:ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := by
  dsimp only
  have h := actual_vaughan_odd_mobius_interval_density_decimal_error U A B hAB hhalf
  dsimp only at h
  have hn := actual_vaughan_signed_density_main_normalization U A B 2
  dsimp only at hn
  rw [hn] at h
  have hrho : (6/Real.pi^2)*(∏ p∈(2 : ℕ).primeFactors,(p : ℝ)/((p : ℝ)+1))=4/Real.pi^2 := by
    rw [Nat.prime_two.primeFactors,Finset.prod_singleton]
    norm_num only [Nat.cast_ofNat]
    ring
  rw [hrho] at h
  exact h

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma cutoff_indicator_interval_integrable (c a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => if c<x then (1:ℝ) else 0) volume a b := by
  have hm : Measurable (fun x : ℝ => if c<x then (1:ℝ) else 0) :=
    Measurable.ite measurableSet_Ioi measurable_const measurable_const
  apply (intervalIntegrable_const (c:=(1:ℝ))).mono_fun' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by dsimp only;split_ifs <;> norm_num)

lemma cutoff_indicator_interval_integral (a b c : ℝ) (hab : a ≤ b) (hcb : c ≤ b) :
    (∫ x in a..b,if c<x then (1:ℝ) else 0)=b-max a c := by
  by_cases hca : c ≤ a
  · rw [max_eq_left hca]
    have he : (∫ x in a..b,if c<x then (1:ℝ) else 0)=∫ x in a..b,(1:ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab
      intro x hx
      exact if_pos (hca.trans_lt hx.1)
    rw [he,intervalIntegral.integral_const]
    simp
  · have hac : a ≤ c := le_of_not_ge hca
    rw [max_eq_right hac]
    have hleft : (∫ x in a..c,if c<x then (1:ℝ) else 0)=0 := by
      calc
        _=∫ x in a..c,(0:ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hac
          intro x hx
          exact if_neg (by linarith [hx.2])
        _=0 := by simp
    have hright : (∫ x in c..b,if c<x then (1:ℝ) else 0)=b-c := by
      calc
        _=∫ x in c..b,(1:ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hcb
          intro x hx
          exact if_pos hx.1
        _=b-c := by simp
    have h := intervalIntegral.integral_add_adjacent_intervals
      (cutoff_indicator_interval_integrable c a c) (cutoff_indicator_interval_integrable c c b)
    rw [hleft,hright,zero_add] at h
    exact h.symm

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

theorem signed_finite_cutoff_sum_integral (S : Finset ℕ) (T : Finset ℕ)
    (w : ℕ→ℕ→ℝ) (c : ℕ→ℕ→ℝ) (a b : ℝ) (hab : a ≤ b)
    (hc : ∀ r∈S,∀ t∈T,c r t ≤ b) :
    (∑ r∈S,∑ t∈T,w r t*(b-max a (c r t)))=
      ∫ x in a..b,∑ r∈S,∑ t∈T,if c r t<x then w r t else 0 := by
  have hi (r t : ℕ) : IntervalIntegrable (fun x : ℝ => if c r t<x then w r t else 0) volume a b := by
    have h := (cutoff_indicator_interval_integrable (c r t) a b).const_mul (w r t)
    apply h.congr
    intro x hx
    dsimp only
    split_ifs <;> simp
  have hs (r : ℕ) : IntervalIntegrable (fun x : ℝ => ∑ t∈T,if c r t<x then w r t else 0) volume a b :=
    by
      have he : (∑ t∈T,fun x : ℝ => if c r t<x then w r t else 0)=
          (fun x : ℝ => ∑ t∈T,if c r t<x then w r t else 0) := by
        funext x
        simp
      rw [←he]
      exact IntervalIntegrable.sum T (fun t ht => hi r t)
  rw [intervalIntegral.integral_finsetSum (fun r hr => hs r)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [intervalIntegral.integral_finsetSum (fun t ht => hi r t)]
  apply Finset.sum_congr rfl
  intro t ht
  have he : (fun x : ℝ => if c r t<x then w r t else 0)=
      (fun x : ℝ => w r t*(if c r t<x then (1:ℝ) else 0)) := by
    funext x
    split_ifs <;> simp
  rw [he,intervalIntegral.integral_const_mul,cutoff_indicator_interval_integral a b (c r t) hab (hc r hr t ht)]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Finset Nat Real
open scoped BigOperators Classical
namespace Helfgott

lemma vaughan_density_integral_cutoffs (U B r t s : ℕ)
    (hr : 1 ≤ r) (ht : 1 ≤ t) (hs : 1 ≤ s)
    (hrcap : r ≤ B/((U+1)*s)) (htcap : t ≤ B/((U+1)*s)) :
    max ((U : ℝ)*t) ((U : ℝ)*r) ≤ (B : ℝ)/(s : ℝ) := by
  have hd : 0<(U+1)*s := Nat.mul_pos (Nat.succ_pos U) hs
  have hrP := (Nat.le_div_iff_mul_le hd).mp hrcap
  have htP := (Nat.le_div_iff_mul_le hd).mp htcap
  have hrB : U*r*s ≤ B := by
    calc
      _ ≤ (U+1)*r*s := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ U))
      _=r*((U+1)*s) := by ring
      _ ≤ B := hrP
  have htB : U*t*s ≤ B := by
    calc
      _ ≤ (U+1)*t*s := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ U))
      _=t*((U+1)*s) := by ring
      _ ≤ B := htP
  have hsR : (0:ℝ)<s := by exact_mod_cast hs
  apply max_le
  · exact (le_div_iff₀ hsR).mpr (by exact_mod_cast htB)
  · exact (le_div_iff₀ hsR).mpr (by exact_mod_cast hrB)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma actual_vaughan_signed_density_main_integral (U A B v : ℕ) (hAB : A ≤ B) :
    let sigma : ℕ→ℝ := fun q => ∏ p∈q.primeFactors,((p : ℝ)+1)
    (∑ s∈Finset.Icc 1 (B/(U+1)),∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
      if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
        (((moebius r : ℤ) : ℝ)/sigma r)*(((moebius t : ℤ) : ℝ)/sigma t)*
          ((B : ℝ)/(s : ℝ)-max ((A : ℝ)/(s : ℝ)) (max ((U : ℝ)*t) ((U : ℝ)*r))) else 0)=
      ∑ s∈Finset.Icc 1 (B/(U+1)),∫ z in ((A : ℝ)/(s : ℝ))..((B : ℝ)/(s : ℝ)),
        ∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
          if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v ∧ (U : ℝ)*r<z ∧ (U : ℝ)*t<z then
            (((moebius r : ℤ) : ℝ)/sigma r)*(((moebius t : ℤ) : ℝ)/sigma t) else 0 := by
  dsimp only
  apply Finset.sum_congr rfl
  intro s hs
  let T := Finset.Icc 1 (B/((U+1)*s))
  let w : ℕ→ℕ→ℝ := fun r t => if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
    (((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)))*
    (((moebius t : ℤ) : ℝ)/(∏ p∈t.primeFactors,((p : ℝ)+1))) else 0
  have hi := signed_finite_cutoff_sum_integral T T w
    (fun r t => max ((U : ℝ)*t) ((U : ℝ)*r)) ((A : ℝ)/(s : ℝ)) ((B : ℝ)/(s : ℝ))
    (div_le_div_of_nonneg_right (by exact_mod_cast hAB) (by positivity))
    (fun r hr t ht => vaughan_density_integral_cutoffs U B r t s (Finset.mem_Icc.mp hr).1
      (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hr).2 (Finset.mem_Icc.mp ht).2)
  have hleft : (∑ r∈T,∑ t∈T,w r t*((B : ℝ)/(s : ℝ)-max ((A : ℝ)/(s : ℝ)) (max ((U : ℝ)*t) ((U : ℝ)*r))))=
      ∑ r∈T,∑ t∈T,if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
        (((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)))*
        (((moebius t : ℤ) : ℝ)/(∏ p∈t.primeFactors,((p : ℝ)+1)))*
        ((B : ℝ)/(s : ℝ)-max ((A : ℝ)/(s : ℝ)) (max ((U : ℝ)*t) ((U : ℝ)*r))) else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    dsimp [w]
    split_ifs <;> simp
  rw [hleft] at hi
  rw [hi]
  apply intervalIntegral.integral_congr
  intro z hz
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro t ht
  dsimp [w]
  split_ifs <;> simp_all only [max_lt_iff] <;> aesop

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

theorem actual_vaughan_odd_mobius_integral_density_error (U A B : ℕ)
    (hAB : A ≤ B) (hhalf : B ≤ 2*A) :
    let sigma : ℕ→ℝ := fun q => ∏ p∈q.primeFactors,((p : ℝ)+1)
    |(∑ m∈Finset.Ioc A B,if Nat.Coprime m 2 then
        ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)-
      (4/Real.pi^2)*(∑ s∈Finset.Icc 1 (B/(U+1)),
        ∫ z in ((A : ℝ)/(s : ℝ))..((B : ℝ)/(s : ℝ)),
          ∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
            if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) 2 ∧ (U : ℝ)*r<z ∧ (U : ℝ)*t<z then
              (((moebius r : ℤ) : ℝ)/sigma r)*(((moebius t : ℤ) : ℝ)/sigma t) else 0)| ≤
      (107/10:ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := by
  dsimp only
  have h := actual_vaughan_odd_mobius_normalized_density_error U A B hAB hhalf
  dsimp only at h
  have hi := actual_vaughan_signed_density_main_integral U A B 2 hAB
  dsimp only at hi
  rw [hi] at h
  exact h

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat
open scoped BigOperators Classical
namespace Helfgott

lemma finite_positive_multiples_reindex (Y d : ℕ) (hd : 1 ≤ d) (F : ℕ→ℝ) :
    (∑ r∈Finset.Icc 1 Y,if d∣r then F r else 0)=∑ a∈Finset.Icc 1 (Y/d),F (d*a) := by
  rw [←Finset.sum_filter]
  apply Finset.sum_bij (fun r hr => r/d)
  · intro r hr
    obtain ⟨hrI,hrd⟩ := Finset.mem_filter.mp hr
    have hrpos := (Finset.mem_Icc.mp hrI).1
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hrpos hrd) hd,
      Nat.div_le_div_right (Finset.mem_Icc.mp hrI).2⟩
  · intro r hr t ht he
    have hrdiv := (Finset.mem_filter.mp hr).2
    have htdiv := (Finset.mem_filter.mp ht).2
    calc r=d*(r/d) := (Nat.mul_div_cancel' hrdiv).symm
         _=d*(t/d) := by rw [he]
         _=t := Nat.mul_div_cancel' htdiv
  · intro a ha
    have hp : 1 ≤ d*a := Nat.mul_pos hd (Finset.mem_Icc.mp ha).1
    have hb : d*a ≤ Y := by
      simpa only [mul_comm] using (Nat.le_div_iff_mul_le hd).mp (Finset.mem_Icc.mp ha).2
    exact ⟨d*a,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp,hb⟩,dvd_mul_right d a⟩,Nat.mul_div_right a hd⟩
  · intro r hr
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hr).2]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

lemma finite_coprime_pair_mobius_reindex (Y : ℕ) (F : ℕ→ℕ→ℝ) :
    (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,if Nat.Coprime r t then F r t else 0)=
      ∑ d∈Finset.Icc 1 Y,((moebius d : ℤ) : ℝ)*
        (∑ a∈Finset.Icc 1 (Y/d),∑ b∈Finset.Icc 1 (Y/d),F (d*a) (d*b)) := by
  have hpoint (r t : ℕ) (hr : 1 ≤ r) :
      (if Nat.Coprime r t then F r t else 0)=
        ∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ)*F r t else 0 := by
    have hc : (∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ) else 0)=
        if Nat.Coprime r t then (1:ℝ) else 0 := by
      have h := coprime_moebius_divisor_expansion r t (by omega)
      have hR : (∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ) else 0)=
          if Nat.Coprime t r then (1:ℝ) else 0 := by exact_mod_cast h
      simpa only [Nat.coprime_comm] using hR
    calc
      _=(if Nat.Coprime r t then (1:ℝ) else 0)*F r t := by split_ifs <;> simp
      _=(∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ) else 0)*F r t := by rw [hc]
      _=_ := by rw [Finset.sum_mul];apply Finset.sum_congr rfl;intro d hd;split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (fun t ht => hpoint r t (Finset.mem_Icc.mp hr).1)),Finset.sum_comm]
  have hdiv (t : ℕ) : (∑ r∈Finset.Icc 1 Y,∑ d∈r.divisors,
      if d∣t then ((moebius d : ℤ) : ℝ)*F r t else 0)=
      ∑ d∈Finset.Icc 1 Y,∑ a∈Finset.Icc 1 (Y/d),
        if d∣t then ((moebius d : ℤ) : ℝ)*F (d*a) t else 0 := by
    have hr (r : ℕ) (hr : r∈Finset.Icc 1 Y) :
        (∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ)*F r t else 0)=
        ∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ)*F (d*(r/d)) t else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
    rw [Finset.sum_congr rfl hr,finite_positive_divisor_reindex Y
      (fun d a => if d∣t then ((moebius d : ℤ) : ℝ)*F (d*a) t else 0)]
  rw [Finset.sum_congr rfl (fun t ht => hdiv t),Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [finite_positive_multiples_reindex Y d (Finset.mem_Icc.mp hd).1
    (fun t => ((moebius d : ℤ) : ℝ)*F (d*a) t),Finset.mul_sum]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

noncomputable def mobiusSigmaWeight (n : ℕ) : ℝ :=
  ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))

lemma mobiusSigmaWeight_mul (d a : ℕ) :
    mobiusSigmaWeight (d*a)=if Nat.Coprime d a then mobiusSigmaWeight d*mobiusSigmaWeight a else 0 := by
  by_cases hc : Nat.Coprime d a
  · rw [if_pos hc]
    have hS : (∏ p∈(d*a).primeFactors,((p : ℝ)+1))=
        (∏ p∈d.primeFactors,((p : ℝ)+1))*(∏ p∈a.primeFactors,((p : ℝ)+1)) := by
      rw [hc.primeFactors_mul,Finset.prod_union hc.disjoint_primeFactors]
    dsimp [mobiusSigmaWeight]
    rw [isMultiplicative_moebius.map_mul_of_coprime hc,Int.cast_mul,hS]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · rw [if_neg hc]
    have hsf : ¬Squarefree (d*a) := fun h => hc (Nat.coprime_of_squarefree_mul h)
    simp [mobiusSigmaWeight,moebius_eq_zero_of_not_squarefree hsf]

lemma moebius_real_cube_eq_self (d : ℕ) : ((moebius d : ℤ) : ℝ)^3=((moebius d : ℤ) : ℝ) := by
  by_cases hd : moebius d=0
  · rw [hd];norm_num
  · obtain h | h := moebius_ne_zero_iff_eq_or.mp hd <;> rw [h] <;> norm_num

lemma mobiusSigmaWeight_moebius_square (d : ℕ) :
    ((moebius d : ℤ) : ℝ)*(mobiusSigmaWeight d)^2=
      ((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2 := by
  dsimp [mobiusSigmaWeight]
  rw [div_pow]
  calc
    _=((moebius d : ℤ) : ℝ)^3/(∏ p∈d.primeFactors,((p : ℝ)+1))^2 := by ring
    _=_ := by rw [moebius_real_cube_eq_self]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma mobius_sigma_pair_common_divisor (d a b q : ℕ) :
    ((moebius d : ℤ) : ℝ)*
      (if Nat.Coprime (d*a) q ∧ Nat.Coprime (d*b) q then
        mobiusSigmaWeight (d*a)*mobiusSigmaWeight (d*b) else 0)=
      if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (if Nat.Coprime a (d*q) then mobiusSigmaWeight a else 0)*
          (if Nat.Coprime b (d*q) then mobiusSigmaWeight b else 0) else 0 := by
  have hfactor := mobiusSigmaWeight_moebius_square d
  rw [mobiusSigmaWeight_mul,mobiusSigmaWeight_mul]
  simp only [Nat.coprime_mul_iff_left,Nat.coprime_mul_iff_right]
  have hca : Nat.Coprime a d ↔ Nat.Coprime d a := Nat.coprime_comm
  have hcb : Nat.Coprime b d ↔ Nat.Coprime d b := Nat.coprime_comm
  split_ifs <;> simp_all only [hca,hcb,mul_zero,zero_mul] <;> try aesop
  linear_combination (mobiusSigmaWeight a*mobiusSigmaWeight b)*hfactor

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma mobius_sigma_weighted_pair_common_divisor (d a b q : ℕ) (h : ℕ→ℝ) :
    ((moebius d : ℤ) : ℝ)*
      (if Nat.Coprime (d*a) q ∧ Nat.Coprime (d*b) q then
        (mobiusSigmaWeight (d*a)*h (d*a))*(mobiusSigmaWeight (d*b)*h (d*b)) else 0)=
      if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (if Nat.Coprime a (d*q) then mobiusSigmaWeight a*h (d*a) else 0)*
          (if Nat.Coprime b (d*q) then mobiusSigmaWeight b*h (d*b) else 0) else 0 := by
  have hp := mobius_sigma_pair_common_divisor d a b q
  have he := congrArg (fun x : ℝ => x*h (d*a)*h (d*b)) hp
  convert he using 1 <;> split_ifs <;> ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem mobius_sigma_weighted_coprime_pair_square_decomposition (q Y : ℕ) (h : ℕ→ℝ) :
    let f : ℕ→ℝ := fun n => ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))
    (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then (f r*h r)*(f t*h t) else 0)=
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then f a*h (d*a) else 0)^2 else 0 := by
  change (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then (mobiusSigmaWeight r*h r)*(mobiusSigmaWeight t*h t) else 0)=_
  have hleft : (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then (mobiusSigmaWeight r*h r)*(mobiusSigmaWeight t*h t) else 0)=
      ∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,if Nat.Coprime r t then
        (if Nat.Coprime r q ∧ Nat.Coprime t q then (mobiusSigmaWeight r*h r)*(mobiusSigmaWeight t*h t) else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    split_ifs <;> aesop
  rw [hleft,finite_coprime_pair_mobius_reindex]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  have he : (∑ a∈Finset.Icc 1 (Y/d),∑ b∈Finset.Icc 1 (Y/d),
      ((moebius d : ℤ) : ℝ)*(if Nat.Coprime (d*a) q ∧ Nat.Coprime (d*b) q then
        (mobiusSigmaWeight (d*a)*h (d*a))*(mobiusSigmaWeight (d*b)*h (d*b)) else 0))=
      ∑ a∈Finset.Icc 1 (Y/d),∑ b∈Finset.Icc 1 (Y/d),
        if Nat.Coprime d q then (((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (if Nat.Coprime a (d*q) then mobiusSigmaWeight a*h (d*a) else 0)*
          (if Nat.Coprime b (d*q) then mobiusSigmaWeight b*h (d*b) else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    exact Finset.sum_congr rfl (fun b hb => mobius_sigma_weighted_pair_common_divisor d a b q h)
  rw [he]
  by_cases hc : Nat.Coprime d q
  · rw [if_pos hc]
    simp only [if_pos hc]
    simp_rw [←Finset.mul_sum]
    rw [←Finset.sum_mul,←Finset.mul_sum]
    change _=(((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
      (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then mobiusSigmaWeight a*h (d*a) else 0)^2
    ring
  · simp only [if_neg hc,Finset.sum_const_zero]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem mobius_sigma_weighted_coprime_pair_quadratic_bound (q Y : ℕ) (h : ℕ→ℝ) :
    let f : ℕ→ℝ := fun n => ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))
    |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then (f r*h r)*(f t*h t) else 0| ≤
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then f a*h (d*a) else 0)^2 else 0 := by
  dsimp only
  rw [mobius_sigma_weighted_coprime_pair_square_decomposition]
  apply (abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hc : Nat.Coprime d q
  · rw [if_pos hc,if_pos hc,abs_mul,abs_div,
      abs_of_nonneg (sq_nonneg (∏ p∈d.primeFactors,((p : ℝ)+1))),abs_of_nonneg (sq_nonneg (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then (((moebius a : ℤ) : ℝ)/(∏ p∈a.primeFactors,((p : ℝ)+1)))*h (d*a) else 0))]
  · rw [if_neg hc,if_neg hc,abs_zero]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem mobius_sigma_cutoff_coprime_pair_quadratic_bound (q Y : ℕ) (U z : ℝ) :
    let f : ℕ→ℝ := fun n => ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))
    |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q ∧ U*r<z ∧ U*t<z then f r*f t else 0| ≤
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then f a else 0)^2 else 0 := by
  let h : ℕ→ℝ := fun n => if U*n<z then 1 else 0
  have hb := mobius_sigma_weighted_coprime_pair_quadratic_bound q Y h
  dsimp only at hb ⊢
  have hleft : (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then
        (mobiusSigmaWeight r*h r)*(mobiusSigmaWeight t*h t) else 0)=
      ∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
        if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q ∧ U*r<z ∧ U*t<z then
          mobiusSigmaWeight r*mobiusSigmaWeight t else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    dsimp [h]
    split_ifs <;> simp_all <;> try linarith <;> aesop
  have hright (d : ℕ) : (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then
        mobiusSigmaWeight a*h (d*a) else 0)=
      ∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then mobiusSigmaWeight a else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [h]
    split_ifs <;> simp_all <;> try linarith <;> aesop
  change |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
    if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then
      (mobiusSigmaWeight r*h r)*(mobiusSigmaWeight t*h t) else 0|≤_ at hb
  rw [hleft] at hb
  change |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
    if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q ∧ U*r<z ∧ U*t<z then
      mobiusSigmaWeight r*mobiusSigmaWeight t else 0|≤_
  exact hb.trans_eq (Finset.sum_congr rfl (fun d hd => by
    by_cases hc : Nat.Coprime d q
    · rw [if_pos hc,if_pos hc]
      congr 1
      exact congrArg (fun x : ℝ => x^2) (hright d)
    · rw [if_neg hc,if_neg hc]))

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma finite_coprime_cutoff_sum_measurable (S : Finset ℕ) (q : ℕ) (w c : ℕ→ℝ) :
    Measurable (fun z : ℝ => ∑ a∈S,if Nat.Coprime a q ∧ c a<z then w a else 0) := by
  apply Finset.measurable_sum
  intro a ha
  by_cases hc : Nat.Coprime a q
  · have he : (fun z : ℝ => if Nat.Coprime a q ∧ c a<z then w a else 0)=
        (fun z : ℝ => if c a<z then w a else 0) := by
      funext z
      by_cases hz : c a<z
      · rw [if_pos ⟨hc,hz⟩,if_pos hz]
      · rw [if_neg (show ¬(Nat.Coprime a q ∧ c a<z) from by aesop),if_neg hz]
    rw [he]
    exact Measurable.ite measurableSet_Ioi measurable_const measurable_const
  · have he : (fun z : ℝ => if Nat.Coprime a q ∧ c a<z then w a else 0)=(fun _ : ℝ => (0:ℝ)) := by
      funext z;simp only [hc,false_and,if_false]
    rw [he]
    exact measurable_const

lemma finite_coprime_cutoff_sum_abs_bound (S : Finset ℕ) (q : ℕ) (w c : ℕ→ℝ) (z : ℝ) :
    |∑ a∈S,if Nat.Coprime a q ∧ c a<z then w a else 0|≤∑ a∈S,|w a| := by
  apply (abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  split_ifs
  · exact le_rfl
  · simp only [abs_zero]
    exact abs_nonneg _

lemma finite_coprime_cutoff_square_interval_integrable (S : Finset ℕ) (q : ℕ) (w c : ℕ→ℝ) (l r : ℝ) :
    IntervalIntegrable (fun z : ℝ => (∑ a∈S,if Nat.Coprime a q ∧ c a<z then w a else 0)^2) volume l r := by
  have hm := (finite_coprime_cutoff_sum_measurable S q w c).pow_const 2
  apply (intervalIntegrable_const (c:=(∑ a∈S,|w a|)^2)).mono_fun' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hb := finite_coprime_cutoff_sum_abs_bound S q w c z
  have hs : 0≤∑ a∈S,|w a| := Finset.sum_nonneg (fun a ha => abs_nonneg _)
  exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hs] using hb)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma finite_interval_integrable_sum {ι : Type} (S : Finset ι) (f : ι→ℝ→ℝ) (l r : ℝ)
    (hf : ∀ i∈S,IntervalIntegrable (f i) volume l r) :
    IntervalIntegrable (fun z => ∑ i∈S,f i z) volume l r := by
  have he : (∑ i∈S,f i)=(fun z => ∑ i∈S,f i z) := by funext z;simp
  rw [←he]
  exact IntervalIntegrable.sum S hf

lemma finite_filtered_cutoff_pair_interval_integrable (S T : Finset ℕ)
    (P : ℕ→ℕ→Prop) [∀ a b,Decidable (P a b)] (w c : ℕ→ℕ→ℝ) (l r : ℝ) :
    IntervalIntegrable (fun z => ∑ a∈S,∑ b∈T,if P a b ∧ c a b<z then w a b else 0) volume l r := by
  apply finite_interval_integrable_sum
  intro a ha
  apply finite_interval_integrable_sum
  intro b hb
  by_cases hP : P a b
  · have hi := (cutoff_indicator_interval_integrable (c a b) l r).const_mul (w a b)
    apply hi.congr
    intro z hz
    dsimp only
    by_cases hc : c a b<z
    · rw [if_pos hc,if_pos ⟨hP,hc⟩,mul_one]
    · rw [if_neg hc,if_neg (show ¬(P a b ∧ c a b<z) from by aesop),mul_zero]
  · have he : (fun z : ℝ => if P a b ∧ c a b<z then w a b else 0)=(fun _ => (0:ℝ)) := by
      funext z
      exact if_neg (by aesop)
    rw [he]
    exact intervalIntegrable_const

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma mobius_sigma_cutoff_pair_interval_integrable (q Y : ℕ) (U l r : ℝ) :
    IntervalIntegrable (fun z => ∑ a∈Finset.Icc 1 Y,∑ b∈Finset.Icc 1 Y,
      if Nat.Coprime a b ∧ Nat.Coprime a q ∧ Nat.Coprime b q ∧ U*a<z ∧ U*b<z then
        mobiusSigmaWeight a*mobiusSigmaWeight b else 0) volume l r := by
  have hi := finite_filtered_cutoff_pair_interval_integrable (Finset.Icc 1 Y) (Finset.Icc 1 Y)
    (fun a b => Nat.Coprime a b ∧ Nat.Coprime a q ∧ Nat.Coprime b q)
    (fun a b => mobiusSigmaWeight a*mobiusSigmaWeight b) (fun a b => max (U*a) (U*b)) l r
  apply hi.congr
  intro z hz
  dsimp only
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp_all only [max_lt_iff] <;> aesop

lemma mobius_sigma_cutoff_quadratic_interval_integrable (q Y : ℕ) (U l r : ℝ) :
    IntervalIntegrable (fun z => ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
      (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
        (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then mobiusSigmaWeight a else 0)^2 else 0) volume l r := by
  apply finite_interval_integrable_sum
  intro d hd
  by_cases hc : Nat.Coprime d q
  · have hi := (finite_coprime_cutoff_square_interval_integrable (Finset.Icc 1 (Y/d)) (d*q)
        mobiusSigmaWeight (fun a => U*(d*a : ℕ)) l r).const_mul
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)
    simpa only [if_pos hc] using hi
  · simpa only [if_neg hc] using (intervalIntegrable_const (c:=(0:ℝ)) : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume l r)

theorem mobius_sigma_cutoff_integral_quadratic_upper (q Y : ℕ) (U l r : ℝ) (hlr : l≤r) :
    (∫ z in l..r,∑ a∈Finset.Icc 1 Y,∑ b∈Finset.Icc 1 Y,
      if Nat.Coprime a b ∧ Nat.Coprime a q ∧ Nat.Coprime b q ∧ U*a<z ∧ U*b<z then
        mobiusSigmaWeight a*mobiusSigmaWeight b else 0)≤
      ∫ z in l..r,∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then mobiusSigmaWeight a else 0)^2 else 0 := by
  apply intervalIntegral.integral_mono hlr
    (mobius_sigma_cutoff_pair_interval_integrable q Y U l r)
    (mobius_sigma_cutoff_quadratic_interval_integrable q Y U l r)
  intro z
  exact (le_abs_self _).trans (mobius_sigma_cutoff_coprime_pair_quadratic_bound q Y U z)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma mobius_cutoff_pair_parity_factor (s Y : ℕ) (U z : ℝ) :
    (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) 2 ∧ U*r<z ∧ U*t<z then
        mobiusSigmaWeight r*mobiusSigmaWeight t else 0)=
      if Nat.Coprime s 2 then (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
        if Nat.Coprime r t ∧ Nat.Coprime r 2 ∧ Nat.Coprime t 2 ∧ U*r<z ∧ U*t<z then
          mobiusSigmaWeight r*mobiusSigmaWeight t else 0) else 0 := by
  by_cases hs : Nat.Coprime s 2
  · rw [if_pos hs]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hc : Nat.Coprime r t ∧ Nat.Coprime (r*t*s) 2 ∧ U*r<z ∧ U*t<z
    · have hp := (Nat.coprime_mul_iff_left.mp hc.2.1).1
      have hr := (Nat.coprime_mul_iff_left.mp hp).1
      have ht := (Nat.coprime_mul_iff_left.mp hp).2
      rw [if_pos hc,if_pos ⟨hc.1,hr,ht,hc.2.2.1,hc.2.2.2⟩]
    · have hnot : ¬(Nat.Coprime r t ∧ Nat.Coprime r 2 ∧ Nat.Coprime t 2 ∧ U*r<z ∧ U*t<z) := by
        rintro ⟨hrt,hr,ht,hUr,hUt⟩
        apply hc
        exact ⟨hrt,Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_mul_iff_left.mpr ⟨hr,ht⟩,hs⟩,hUr,hUt⟩
      rw [if_neg hc,if_neg hnot]
  · rw [if_neg hs]
    apply Finset.sum_eq_zero
    intro r hr
    apply Finset.sum_eq_zero
    intro t ht
    apply if_neg
    intro hc
    exact hs ((Nat.coprime_mul_iff_left.mp hc.2.1).2)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

theorem actual_vaughan_odd_mobius_quadratic_integral_upper_complete (U A B : ℕ)
    (hAB : A ≤ B) (hhalf : B ≤ 2*A) :
    let sigma : ℕ→ℝ := fun q => ∏ p∈q.primeFactors,((p : ℝ)+1)
    (∑ m∈Finset.Ioc A B,if Nat.Coprime m 2 then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)≤
      (4/Real.pi^2)*(∑ s∈Finset.Icc 1 (B/(U+1)),if Nat.Coprime s 2 then
        ∫ z in ((A : ℝ)/(s : ℝ))..((B : ℝ)/(s : ℝ)),
          ∑ d∈Finset.Icc 1 (B/((U+1)*s)),if Nat.Coprime d 2 then
            (|((moebius d : ℤ) : ℝ)|/(sigma d)^2)*
              (∑ a∈Finset.Icc 1 ((B/((U+1)*s))/d),
                if Nat.Coprime a (d*2) ∧ (U : ℝ)*(d*a : ℕ)<z then
                  ((moebius a : ℤ) : ℝ)/sigma a else 0)^2 else 0 else 0)+
      (107/10:ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := by
  dsimp only
  let Y : ℕ→ℕ := fun s => B/((U+1)*s)
  let E : ℝ := ∑ m∈Finset.Ioc A B,if Nat.Coprime m 2 then
    ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0
  let eps : ℝ := (107/10:ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ))
  let K : ℕ→ℝ→ℝ := fun s z => ∑ r∈Finset.Icc 1 (Y s),∑ t∈Finset.Icc 1 (Y s),
    if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) 2 ∧ (U : ℝ)*r<z ∧ (U : ℝ)*t<z then
      mobiusSigmaWeight r*mobiusSigmaWeight t else 0
  let Q : ℕ→ℝ→ℝ := fun s z => ∑ d∈Finset.Icc 1 (Y s),if Nat.Coprime d 2 then
    (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
      (∑ a∈Finset.Icc 1 (Y s/d),if Nat.Coprime a (d*2) ∧ (U : ℝ)*(d*a : ℕ)<z then mobiusSigmaWeight a else 0)^2 else 0
  have herr : |E-(4/Real.pi^2)*(∑ s∈Finset.Icc 1 (B/(U+1)),
      ∫ z in ((A : ℝ)/(s : ℝ))..((B : ℝ)/(s : ℝ)),K s z)|≤eps :=
    actual_vaughan_odd_mobius_integral_density_error U A B hAB hhalf
  have hsum : (∑ s∈Finset.Icc 1 (B/(U+1)),
      ∫ z in ((A : ℝ)/(s : ℝ))..((B : ℝ)/(s : ℝ)),K s z)≤
      ∑ s∈Finset.Icc 1 (B/(U+1)),if Nat.Coprime s 2 then
        (∫ z in ((A : ℝ)/(s : ℝ))..((B : ℝ)/(s : ℝ)),Q s z) else 0 := by
    apply Finset.sum_le_sum
    intro s hsI
    by_cases hs : Nat.Coprime s 2
    · rw [if_pos hs]
      have he : K s=(fun z => ∑ r∈Finset.Icc 1 (Y s),∑ t∈Finset.Icc 1 (Y s),
          if Nat.Coprime r t ∧ Nat.Coprime r 2 ∧ Nat.Coprime t 2 ∧ (U : ℝ)*r<z ∧ (U : ℝ)*t<z then
            mobiusSigmaWeight r*mobiusSigmaWeight t else 0) := by
        funext z
        exact (mobius_cutoff_pair_parity_factor s (Y s) (U : ℝ) z).trans (if_pos hs)
      rw [he]
      exact mobius_sigma_cutoff_integral_quadratic_upper 2 (Y s) (U : ℝ)
        ((A : ℝ)/(s : ℝ)) ((B : ℝ)/(s : ℝ))
        (div_le_div_of_nonneg_right (by exact_mod_cast hAB) (by positivity))
    · rw [if_neg hs]
      have he : K s=(fun _ : ℝ => (0:ℝ)) := by
        funext z
        exact (mobius_cutoff_pair_parity_factor s (Y s) (U : ℝ) z).trans (if_neg hs)
      rw [he]
      simp
  have hmain := mul_le_mul_of_nonneg_left hsum (show (0:ℝ)≤4/Real.pi^2 by positivity)
  have he := (abs_le.mp herr).2
  change E≤(4/Real.pi^2)*(∑ s∈Finset.Icc 1 (B/(U+1)),if Nat.Coprime s 2 then
    (∫ z in ((A : ℝ)/(s : ℝ))..((B : ℝ)/(s : ℝ)),Q s z) else 0)+eps
  linarith

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

theorem solution  (U A B : ℕ)
    (hAB : A ≤ B) (hhalf : B ≤ 2*A) :
    let sigma : ℕ→ℝ := fun q => ∏ p∈q.primeFactors,((p : ℝ)+1)
    (∑ m∈Finset.Ioc A B,if Nat.Coprime m 2 then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)≤
      (4/Real.pi^2)*(∑ s∈Finset.Icc 1 (B/(U+1)),if Nat.Coprime s 2 then
        ∫ z in ((A : ℝ)/(s : ℝ))..((B : ℝ)/(s : ℝ)),
          ∑ d∈Finset.Icc 1 (B/((U+1)*s)),if Nat.Coprime d 2 then
            (|((moebius d : ℤ) : ℝ)|/(sigma d)^2)*
              (∑ a∈Finset.Icc 1 ((B/((U+1)*s))/d),
                if Nat.Coprime a (d*2) ∧ (U : ℝ)*(d*a : ℕ)<z then
                  ((moebius a : ℤ) : ℝ)/sigma a else 0)^2 else 0 else 0)+
      (107/10:ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := Helfgott.actual_vaughan_odd_mobius_quadratic_integral_upper_complete U A B hAB hhalf

#print axioms solution
