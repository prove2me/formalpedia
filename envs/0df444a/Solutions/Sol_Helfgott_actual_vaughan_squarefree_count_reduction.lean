-- Prove2me | solution 1 for Helfgott.actual_vaughan_squarefree_count_reduction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T14:47:13.926287+00:00
-- url     : https://prove2.me/submissions/6e21d81c-7565-4995-b0e3-f8a4f05a0673

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import Definitions.Def_Helfgott_VaughanData

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

theorem actual_vaughan_squarefree_count_reduction_complete (U A B v : ℕ) :
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

open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical

theorem solution  (U A B v : ℕ) :
    (∑ m ∈ Finset.Ioc A B,if Nat.Coprime m v then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)=
      ∑ s ∈ Finset.Icc 1 (B/(U+1)),
        ∑ r ∈ Finset.Icc 1 (B/((U+1)*s)),∑ t ∈ Finset.Icc 1 (B/((U+1)*s)),
          if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
            ((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
              (∑ g ∈ Finset.Ioc (max (A/(r*t*s)) (max (U/r) (U/t))) (B/(r*t*s)),
                if Nat.Coprime g (r*t*v) then ((moebius g : ℤ) : ℝ)^2 else 0) else 0 := Helfgott.actual_vaughan_squarefree_count_reduction_complete U A B v

#print axioms solution
