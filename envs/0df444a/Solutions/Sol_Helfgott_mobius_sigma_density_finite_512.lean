-- Prove2me | solution 1 for Helfgott.mobius_sigma_density_finite_512
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-11T23:22:32.800469+00:00
-- url     : https://prove2.me/submissions/960874a3-85c4-4e71-b884-3842b6dd0fa9

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Data.List.Nodup
import Mathlib.Data.Rat.Cast.Order
section

open scoped BigOperators
namespace Helfgott
open ArithmeticFunction

noncomputable def mobiusSigmaWeight (n : ℕ) : ℝ :=
  ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))


end Helfgott

end

section
/- Multiplicativity proof retained from VaughanMobiusIntegralSource (Apache 2.0). -/
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

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


end Helfgott

end

section
/- Reindexing proof retained from VaughanMobiusIntegralSource (Apache 2.0). -/
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

open Finset ArithmeticFunction Helfgott
open scoped BigOperators Classical
namespace HelfgottQuadratic

noncomputable def sigmaCoprimePrefix (q N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, if Nat.Coprime n q then mobiusSigmaWeight n else 0

theorem mobiusSigmaWeight_prime (p : ℕ) (hp : p.Prime) :
    mobiusSigmaWeight p= -1/((p:ℝ)+1) := by
  simp [mobiusSigmaWeight,moebius_apply_prime hp,hp.primeFactors]

theorem sigmaCoprimePrefix_prime_split (q p N : ℕ) (hp : p.Prime) (hqp : Nat.Coprime p q) :
    sigmaCoprimePrefix q N=sigmaCoprimePrefix (q*p) N-
      (1/((p:ℝ)+1))*sigmaCoprimePrefix (q*p) (N/p) := by
  have hs : sigmaCoprimePrefix q N=sigmaCoprimePrefix (q*p) N+
      ∑ n ∈ Icc 1 N, if p∣n then (if Nat.Coprime n q then mobiusSigmaWeight n else 0) else 0 := by
    unfold sigmaCoprimePrefix
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    have hc : Nat.Coprime n p ↔ ¬p∣n := by rw [Nat.coprime_comm]; exact hp.coprime_iff_not_dvd
    simp only [Nat.coprime_mul_iff_right,hc]
    by_cases hpn : p∣n <;> by_cases hnq : Nat.Coprime n q <;> simp [hpn,hnq]
  rw [hs,Helfgott.finite_positive_multiples_reindex N p hp.one_lt.le]
  have hm : (∑ a ∈ Icc 1 (N/p), if Nat.Coprime (p*a) q then mobiusSigmaWeight (p*a) else 0)=
      (-1/((p:ℝ)+1))*sigmaCoprimePrefix (q*p) (N/p) := by
    unfold sigmaCoprimePrefix
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    have he : mobiusSigmaWeight (p*a)=if Nat.Coprime p a then
        mobiusSigmaWeight p*mobiusSigmaWeight a else 0 :=
      Helfgott.mobiusSigmaWeight_mul p a
    rw [he,mobiusSigmaWeight_prime p hp]
    simp only [Nat.coprime_mul_iff_left,Nat.coprime_mul_iff_right,hqp,true_and]
    have hc : Nat.Coprime p a ↔ Nat.Coprime a p := Nat.coprime_comm
    simp only [hc]
    by_cases haq : Nat.Coprime a q <;> by_cases hap : Nat.Coprime a p <;>
      simp [haq,hap,hqp] <;> split_ifs <;> simp_all
  rw [hm]
  ring

theorem sigmaCoprimePrefix_prime_recursion (q p N : ℕ) (hp : p.Prime) (hqp : Nat.Coprime p q) :
    sigmaCoprimePrefix (q*p) N=sigmaCoprimePrefix q N+
      (1/((p:ℝ)+1))*sigmaCoprimePrefix (q*p) (N/p) := by
  linarith [sigmaCoprimePrefix_prime_split q p N hp hqp]

end HelfgottQuadratic


end

section

open Finset
open scoped BigOperators
namespace HelfgottQuadratic

noncomputable def sigmaPrefixRecursor (W : ℕ→ℝ) : ℕ→List ℕ→ℕ→ℝ
  | _, _, 0 => 0
  | 0, _, _+1 => 0
  | _+1, [], n+1 => W (n+1)
  | f+1, p::ps, n+1 => sigmaPrefixRecursor W f ps (n+1)+
      sigmaPrefixRecursor W f (p::ps) ((n+1)/p)/((p:ℝ)+1)

theorem sigmaPrefixRecursor_exact (fuel : ℕ) (ps : List ℕ) (N : ℕ)
    (hprime : ∀ p∈ps, Nat.Prime p) (hpair : ps.Pairwise Nat.Coprime)
    (hf : N+ps.length+1≤fuel) :
    sigmaPrefixRecursor (sigmaCoprimePrefix 1) fuel ps N=sigmaCoprimePrefix ps.prod N := by
  induction fuel generalizing ps N with
  | zero => omega
  | succ f ih =>
    cases N with
    | zero => simp [sigmaPrefixRecursor,sigmaCoprimePrefix]
    | succ n =>
      cases ps with
      | nil => simp [sigmaPrefixRecursor]
      | cons p ps =>
        have hp := hprime p (by simp)
        have htail : ∀ r∈ps, Nat.Prime r := fun r hr=>hprime r (by simp [hr])
        obtain ⟨hcp,hps⟩ := List.pairwise_cons.mp hpair
        have hcop : Nat.Coprime p ps.prod := Nat.coprime_list_prod_right_iff.mpr hcp
        have hdiv : (n+1)/p<n+1 := Nat.div_lt_self (by omega) hp.one_lt
        simp only [List.length_cons] at hf
        rw [sigmaPrefixRecursor,ih ps (n+1) htail hps (by omega),
          ih (p::ps) ((n+1)/p) hprime hpair (by simp only [List.length_cons]; omega)]
        simp only [List.prod_cons]
        have hh := sigmaCoprimePrefix_prime_recursion ps.prod p (n+1) hp hcop
        rw [Nat.mul_comm ps.prod p] at hh
        rw [hh]
        ring

theorem sigmaPrefixRecursor_stability (W V : ℕ→ℝ) (fuel : ℕ) (ps : List ℕ) (N M : ℕ)
    (ε : ℝ) (hε : 0≤ε) (hN : N≤M) (hp : ∀ p∈ps, 2≤p)
    (hbase : ∀ n≤M, |W n-V n|≤ε) :
    |sigmaPrefixRecursor W fuel ps N-sigmaPrefixRecursor V fuel ps N|≤ε*2^ps.length := by
  induction fuel generalizing ps N with
  | zero => cases N <;> simp [sigmaPrefixRecursor,hε]
  | succ f ih =>
    cases N with
    | zero => simp only [sigmaPrefixRecursor,sub_self,abs_zero]; positivity
    | succ n =>
      cases ps with
      | nil => simpa [sigmaPrefixRecursor] using hbase (n+1) hN
      | cons p ps =>
        have hp2 := hp p (by simp)
        have hpR : (2:ℝ)≤p := by exact_mod_cast hp2
        have htail : ∀ r∈ps, 2≤r := fun r hr=>hp r (by simp [hr])
        have h1 := ih ps (n+1) hN htail
        have h2 := ih (p::ps) ((n+1)/p) ((Nat.div_le_self _ _).trans hN) hp
        have hden : 0<(p:ℝ)+1 := by positivity
        have hscale : (1/((p:ℝ)+1):ℝ)≤1/3 := (one_div_le_one_div_of_le (by norm_num) (by linarith))
        have hpow : 0≤ε*(2:ℝ)^ps.length := by positivity
        rw [sigmaPrefixRecursor,sigmaPrefixRecursor,
          show sigmaPrefixRecursor W f ps (n+1)+sigmaPrefixRecursor W f (p::ps) ((n+1)/p)/((p:ℝ)+1)-
            (sigmaPrefixRecursor V f ps (n+1)+sigmaPrefixRecursor V f (p::ps) ((n+1)/p)/((p:ℝ)+1))=
            (sigmaPrefixRecursor W f ps (n+1)-sigmaPrefixRecursor V f ps (n+1))+
            (sigmaPrefixRecursor W f (p::ps) ((n+1)/p)-sigmaPrefixRecursor V f (p::ps) ((n+1)/p))/((p:ℝ)+1) by ring]
        have hh := abs_add_le (sigmaPrefixRecursor W f ps (n+1)-sigmaPrefixRecursor V f ps (n+1))
          ((sigmaPrefixRecursor W f (p::ps) ((n+1)/p)-sigmaPrefixRecursor V f (p::ps) ((n+1)/p))/((p:ℝ)+1))
        rw [abs_div,abs_of_pos hden] at hh
        have hquot := div_le_div_of_nonneg_right h2 hden.le
        have hq := mul_le_mul_of_nonneg_left hscale (show 0≤ε*(2:ℝ)^(p::ps).length by positivity)
        simp only [List.length_cons,pow_succ] at h2 hq hquot ⊢
        simp only [div_eq_mul_inv,one_mul] at hh hq hquot ⊢
        nlinarith

end HelfgottQuadratic

end

section
open Finset
open scoped BigOperators Classical
namespace HelfgottQuadratic

noncomputable def coprimePairPrefix (w : ℕ→ℝ) (N : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, if Nat.Coprime a b then w a*w b else 0

noncomputable def coprimeDensityPrefix (w : ℕ→ℝ) (N : ℕ) : ℝ :=
  ∑ s ∈ Icc 1 N, (1/(s:ℝ))*coprimePairPrefix w (N/s)


end HelfgottQuadratic

end

section
/- Finite hyperbola reindexing retained from accepted Prove2Me submission
4b19f26e-e6f8-4a14-8cf6-e0ea33b44440 by raresbuhai (Apache 2.0). -/
open Finset
open scoped BigOperators
namespace HelfgottQuadratic
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


end HelfgottQuadratic

end

section

open Finset
open scoped BigOperators Classical
namespace HelfgottQuadratic

noncomputable def coprimePairIncrement (w : ℕ→ℝ) (n : ℕ) : ℝ :=
  2*w n*(∑ a ∈ Icc 1 (n-1), if Nat.Coprime a n then w a else 0)+
    if n=1 then (w n)^2 else 0

theorem coprimePairPrefix_succ (w : ℕ→ℝ) (n : ℕ) :
    coprimePairPrefix w (n+1)=coprimePairPrefix w n+coprimePairIncrement w (n+1) := by
  unfold coprimePairPrefix coprimePairIncrement
  rw [sum_Icc_succ_top (by omega : 1≤n+1)]
  simp_rw [sum_Icc_succ_top (by omega : 1≤n+1)]
  rw [sum_add_distrib]
  have h1 : (∑ a ∈ Icc 1 n, if Nat.Coprime a (n+1) then w a*w (n+1) else 0)=
      w (n+1)*(∑ a ∈ Icc 1 n, if Nat.Coprime a (n+1) then w a else 0) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    split_ifs <;> ring
  have h2 : (∑ a ∈ Icc 1 n, if Nat.Coprime (n+1) a then w (n+1)*w a else 0)=
      w (n+1)*(∑ a ∈ Icc 1 n, if Nat.Coprime a (n+1) then w a else 0) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    simp only [Nat.coprime_comm (m:=n+1) (n:=a)]
    split_ifs <;> ring
  rw [h1,h2]
  simp only [Nat.add_sub_cancel,Nat.coprime_self]
  split_ifs <;> ring

theorem coprimePairPrefix_eq_sum_increment (w : ℕ→ℝ) (N : ℕ) :
    coprimePairPrefix w N=∑ n ∈ Icc 1 N, coprimePairIncrement w n := by
  induction N with
  | zero => simp [coprimePairPrefix]
  | succ N ih => rw [coprimePairPrefix_succ,ih,sum_Icc_succ_top (by omega : 1≤N+1)]

theorem coprimeDensityPrefix_eq_divisor_sum (w : ℕ→ℝ) (N : ℕ) :
    coprimeDensityPrefix w N=
      ∑ n ∈ Icc 1 N, ∑ s ∈ n.divisors, coprimePairIncrement w (n/s)/(s:ℝ) := by
  rw [finite_positive_divisor_reindex N (fun s a=>coprimePairIncrement w a/(s:ℝ))]
  unfold coprimeDensityPrefix
  simp_rw [coprimePairPrefix_eq_sum_increment,mul_sum]
  apply sum_congr rfl
  intro s hs
  apply sum_congr rfl
  intro a ha
  ring

theorem coprimeDensityPrefix_succ (w : ℕ→ℝ) (N : ℕ) :
    coprimeDensityPrefix w (N+1)=coprimeDensityPrefix w N+
      ∑ s ∈ (N+1).divisors, coprimePairIncrement w ((N+1)/s)/(s:ℝ) := by
  simp only [coprimeDensityPrefix_eq_divisor_sum]
  rw [sum_Icc_succ_top (by omega : 1≤N+1)]

end HelfgottQuadratic


end

section

open Finset
open scoped BigOperators Classical
namespace HelfgottQuadratic

theorem pair_product_stability (w v : ℕ→ℝ) (N : ℕ) (B ε : ℝ)
    (hB : 0≤B) (hε : 0≤ε)
    (hw : ∀ n ∈ Icc 1 N, |w n|≤B)
    (he : ∀ n ∈ Icc 1 N, |w n-v n|≤ε)
    (a b : ℕ) (ha : a∈Icc 1 N) (hb : b∈Icc 1 N) :
    |w a*w b-v a*v b|≤ε*(2*B+ε) := by
  have hva : |v a|≤B+ε := by
    have hh := abs_add_le (w a) (v a-w a)
    rw [show w a+(v a-w a)=v a by ring,abs_sub_comm (v a) (w a)] at hh
    linarith [hw a ha,he a ha]
  calc
    _ = |(w a-v a)*w b+v a*(w b-v b)| := by congr 1; ring
    _ ≤ |(w a-v a)*w b|+|v a*(w b-v b)| := abs_add_le _ _
    _ = |w a-v a| *|w b|+|v a| *|w b-v b| := by rw [abs_mul,abs_mul]
    _ ≤ ε*B+(B+ε)*ε := add_le_add
      (mul_le_mul (he a ha) (hw b hb) (abs_nonneg _) hε)
      (mul_le_mul hva (he b hb) (abs_nonneg _) (add_nonneg hB hε))
    _ = _ := by ring

theorem coprimePairPrefix_stability (w v : ℕ→ℝ) (N : ℕ) (δ : ℝ) (hδ : 0≤δ)
    (hp : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, |w a*w b-v a*v b|≤δ) :
    |coprimePairPrefix w N-coprimePairPrefix v N|≤(N:ℝ)^2*δ := by
  unfold coprimePairPrefix
  rw [←sum_sub_distrib]
  calc
    _ ≤ ∑ a ∈ Icc 1 N, |(∑ b ∈ Icc 1 N, if Nat.Coprime a b then w a*w b else 0)-
        (∑ b ∈ Icc 1 N, if Nat.Coprime a b then v a*v b else 0)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, δ := by
      apply sum_le_sum
      intro a ha
      rw [←sum_sub_distrib]
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro b hb
      by_cases hc : Nat.Coprime a b
      · simpa only [if_pos hc] using hp a ha b hb
      · simpa only [if_neg hc,sub_self,abs_zero] using hδ
    _ = _ := by simp; ring

theorem coprimeDensityPrefix_stability (w v : ℕ→ℝ) (N : ℕ) (δ : ℝ) (hδ : 0≤δ)
    (hp : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, |w a*w b-v a*v b|≤δ) :
    |coprimeDensityPrefix w N-coprimeDensityPrefix v N|≤(N:ℝ)^3*δ := by
  unfold coprimeDensityPrefix
  rw [←sum_sub_distrib]
  calc
    _ ≤ ∑ s ∈ Icc 1 N, |(1/(s:ℝ))*coprimePairPrefix w (N/s)-(1/(s:ℝ))*coprimePairPrefix v (N/s)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ Icc 1 N, (N:ℝ)^2*δ := by
      apply sum_le_sum
      intro s hs
      have hsp : (0:ℝ)<s := by exact_mod_cast (mem_Icc.mp hs).1
      have hs1 : (1:ℝ)≤s := by exact_mod_cast (mem_Icc.mp hs).1
      have hsub : Icc 1 (N/s)⊆Icc 1 N := fun a ha=>mem_Icc.mpr
        ⟨(mem_Icc.mp ha).1,(mem_Icc.mp ha).2.trans (Nat.div_le_self N s)⟩
      have hh := coprimePairPrefix_stability w v (N/s) δ hδ (fun a ha b hb=>hp a (hsub ha) b (hsub hb))
      rw [←mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤1/(s:ℝ))]
      calc
        _ ≤ (1/(s:ℝ))*((N/s:ℕ):ℝ)^2*δ := by nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : 0≤1/(s:ℝ))]
        _ ≤ 1*(N:ℝ)^2*δ := by gcongr; simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hs1; exact_mod_cast Nat.div_le_self N s
        _ = _ := by ring
    _ = _ := by simp; ring

theorem coprimeDensityPrefix_rounding_error (w v : ℕ→ℝ) (N : ℕ) (ε : ℝ)
    (hε : 0≤ε) (hw : ∀ n ∈ Icc 1 N, |w n|≤1)
    (he : ∀ n ∈ Icc 1 N, |w n-v n|≤ε) :
    |coprimeDensityPrefix w N-coprimeDensityPrefix v N|≤(N:ℝ)^3*ε*(2+ε) := by
  have hh := coprimeDensityPrefix_stability w v N (ε*(2+ε)) (by positivity)
    (fun a ha b hb=>by simpa only [mul_one] using pair_product_stability w v N 1 ε (by norm_num) hε hw he a b ha hb)
  exact hh.trans_eq (by ring)

end HelfgottQuadratic


end

section

open Finset
open scoped BigOperators Classical
namespace HelfgottQuadratic

def integerPairIncrement (a : ℕ→ℤ) (n : ℕ) : ℤ :=
  2*a n*(∑ k ∈ Icc 1 (n-1), if Nat.Coprime k n then a k else 0)+
    if n=1 then (a n)^2 else 0

def integerCeilDiv (a : ℤ) (n : ℕ) : ℤ := -((-a)/(n:ℤ))

theorem integerCeilDiv_eq_rat (a : ℤ) (n : ℕ) :
    integerCeilDiv a n=⌈(a:ℚ)/(n:ℚ)⌉ := (Rat.ceil_intCast_div_natCast a n).symm

theorem integerCeilDiv_upper (a : ℤ) (n : ℕ) :
    (a:ℝ)/(n:ℝ)≤(integerCeilDiv a n:ℝ) := by
  have hh := Int.le_ceil ((a:ℚ)/(n:ℚ))
  rw [integerCeilDiv_eq_rat]
  exact_mod_cast hh

theorem integerPairIncrement_cast (a : ℕ→ℤ) (n : ℕ) :
    (integerPairIncrement a n:ℝ)=coprimePairIncrement (fun k=>(a k:ℝ)) n := by
  simp only [integerPairIncrement,coprimePairIncrement,Int.cast_add,Int.cast_mul,
    Int.cast_ofNat,Int.cast_sum,apply_ite,Int.cast_zero,Int.cast_pow]
  split_ifs <;> rfl

theorem integer_pair_prefix_sound (a F : ℕ→ℤ) (K : ℕ) (hzero : F 0=0)
    (hstep : ∀ n<K, F (n+1)=F n+integerPairIncrement a (n+1)) :
    ∀ n≤K, (F n:ℝ)=coprimePairPrefix (fun k=>(a k:ℝ)) n := by
  intro n hn
  induction n with
  | zero => simp [hzero,coprimePairPrefix]
  | succ n ih =>
    rw [hstep n (by omega),Int.cast_add,integerPairIncrement_cast,
      coprimePairPrefix_succ,ih (by omega)]

theorem coprimePairPrefix_scale (a : ℕ→ℝ) (c : ℝ) (N : ℕ) :
    coprimePairPrefix (fun n=>c*a n) N=c^2*coprimePairPrefix a N := by
  unfold coprimePairPrefix
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [mul_sum]
  apply sum_congr rfl
  intro m hm
  split_ifs <;> ring

theorem coprimeDensityPrefix_scale (a : ℕ→ℝ) (c : ℝ) (N : ℕ) :
    coprimeDensityPrefix (fun n=>c*a n) N=c^2*coprimeDensityPrefix a N := by
  unfold coprimeDensityPrefix
  simp_rw [coprimePairPrefix_scale]
  rw [mul_sum]
  apply sum_congr rfl
  intro s hs
  ring

theorem integer_density_prefix_sound (a F G : ℕ→ℤ) (K : ℕ)
    (hFzero : F 0=0) (hGzero : G 0=0)
    (hFstep : ∀ n<K, F (n+1)=F n+integerPairIncrement a (n+1))
    (hGstep : ∀ n<K, G n+(∑ s ∈ (n+1).divisors,
      integerCeilDiv (F ((n+1)/s)-F ((n+1)/s-1)) s)≤G (n+1)) :
    ∀ n≤K, coprimeDensityPrefix (fun k=>(a k:ℝ)) n≤(G n:ℝ) := by
  intro n hn
  induction n with
  | zero => simp [hGzero,coprimeDensityPrefix]
  | succ n ih =>
    rw [coprimeDensityPrefix_succ]
    have hparts : (∑ s ∈ (n+1).divisors, coprimePairIncrement (fun k=>(a k:ℝ)) ((n+1)/s)/(s:ℝ))≤
        ((∑ s ∈ (n+1).divisors, integerCeilDiv (F ((n+1)/s)-F ((n+1)/s-1)) s:ℤ):ℝ) := by
      rw [Int.cast_sum]
      apply sum_le_sum
      intro s hs
      have hdvd := (Nat.mem_divisors.mp hs).1
      have hsp : 0<s := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hdp : 0<(n+1)/s := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hsp
      have hdK : (n+1)/s≤K := (Nat.div_le_self _ _).trans hn
      have he : F ((n+1)/s)-F ((n+1)/s-1)=integerPairIncrement a ((n+1)/s) := by
        have hh := hFstep ((n+1)/s-1) (by omega)
        rw [Nat.sub_add_cancel hdp] at hh
        omega
      have hh := integerCeilDiv_upper (F ((n+1)/s)-F ((n+1)/s-1)) s
      rw [he,integerPairIncrement_cast] at hh
      rw [he]
      exact hh
    have hg := hGstep n (by omega)
    have hgR : (G n:ℝ)+((∑ s ∈ (n+1).divisors,
      integerCeilDiv (F ((n+1)/s)-F ((n+1)/s-1)) s:ℤ):ℝ)≤(G (n+1):ℝ) := by exact_mod_cast hg
    exact (add_le_add (ih (by omega)) hparts).trans hgR

theorem integer_density_rounded_bound (w : ℕ→ℝ) (a F G : ℕ→ℤ) (K : ℕ) (Q C : ℝ)
    (hQ : 0<Q) (hGzero : G 0=0)
    (hw : ∀ n ∈ Icc 1 K, |w n|≤1)
    (he : ∀ n ∈ Icc 1 K, |w n-(a n:ℝ)/Q|≤1/Q)
    (hFstep : ∀ n<K, F (n+1)=F n+integerPairIncrement a (n+1))
    (hGstep : ∀ n<K, G n+(∑ s ∈ (n+1).divisors,
      integerCeilDiv (F ((n+1)/s)-F ((n+1)/s-1)) s)≤G (n+1))
    (hGbound : ∀ n≤K, (G n:ℝ)≤Q^2*C) (n : ℕ) (hn : n≤K) :
    coprimeDensityPrefix w n≤C+(K:ℝ)^3*(1/Q)*(2+1/Q) := by
  let v := fun k : ℕ=>(a k:ℝ)/Q
  have hsub : Icc 1 n⊆Icc 1 K := fun k hk=>mem_Icc.mpr ⟨(mem_Icc.mp hk).1,(mem_Icc.mp hk).2.trans hn⟩
  have herr := coprimeDensityPrefix_rounding_error w v n (1/Q) (by positivity)
    (fun k hk=>hw k (hsub hk)) (fun k hk=>he k (hsub hk))
  have hg := integer_density_prefix_sound a (fun k=>F k-F 0) G K (by simp) hGzero
    (by intro k hk; rw [hFstep k hk]; ring)
    (by intro k hk; simpa only [sub_sub_sub_cancel_right] using hGstep k hk) n hn
  have hv : coprimeDensityPrefix v n≤C := by
    have heq : v=fun k=>(1/Q)*(a k:ℝ) := by funext k; dsimp only [v]; ring
    rw [heq,coprimeDensityPrefix_scale]
    have hh := mul_le_mul_of_nonneg_left (hg.trans (hGbound n hn)) (sq_nonneg (1/Q))
    exact hh.trans_eq (by field_simp <;> ring)
  have herror : (n:ℝ)^3*(1/Q)*(2+1/Q)≤(K:ℝ)^3*(1/Q)*(2+1/Q) := by gcongr
  linarith [le_abs_self (coprimeDensityPrefix w n-coprimeDensityPrefix v n)]

end HelfgottQuadratic


end

section

namespace HelfgottQuadratic

theorem integerCeilDiv_error (a : ℤ) (n : ℕ) :
    |(integerCeilDiv a n:ℝ)-(a:ℝ)/(n:ℝ)|≤1 := by
  have hlo := integerCeilDiv_upper a n
  have hhi : (integerCeilDiv a n:ℝ)≤(a:ℝ)/(n:ℝ)+1 := by
    rw [integerCeilDiv_eq_rat]
    have hh := (Int.ceil_lt_add_one ((a:ℚ)/(n:ℚ))).le
    exact_mod_cast hh
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem rounded_add_div_error (a b : ℤ) (u v : ℝ) (d : ℕ) (hd : 0<d) :
    |((a+integerCeilDiv b d:ℤ):ℝ)-(u+v/(d:ℝ))|≤
      |(a:ℝ)-u|+1+|(b:ℝ)-v|/(d:ℝ) := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have he : ((a+integerCeilDiv b d:ℤ):ℝ)-(u+v/(d:ℝ))=
      ((a:ℝ)-u)+((integerCeilDiv b d:ℝ)-(b:ℝ)/(d:ℝ))+((b:ℝ)-v)/(d:ℝ) := by push_cast; ring
  rw [he]
  have h1 := abs_add_le (((a:ℝ)-u)+((integerCeilDiv b d:ℝ)-(b:ℝ)/(d:ℝ))) (((b:ℝ)-v)/(d:ℝ))
  have h2 := abs_add_le ((a:ℝ)-u) ((integerCeilDiv b d:ℝ)-(b:ℝ)/(d:ℝ))
  rw [abs_div,abs_of_pos hdR] at h1
  linarith [integerCeilDiv_error b d]

def integerSigmaPrefixRecursor (P : ℕ→ℤ) : ℕ→List ℕ→ℕ→ℤ
  | _, _, 0 => 0
  | 0, _, _+1 => 0
  | _+1, [], n+1 => P (n+1)
  | f+1, p::ps, n+1 => integerSigmaPrefixRecursor P f ps (n+1)+
      integerCeilDiv (integerSigmaPrefixRecursor P f (p::ps) ((n+1)/p)) (p+1)

theorem integerSigmaPrefixRecursor_error (P : ℕ→ℤ) (fuel : ℕ) (ps : List ℕ) (N : ℕ)
    (hp : ∀ p∈ps, 2≤p) :
    |(integerSigmaPrefixRecursor P fuel ps N:ℝ)-
      sigmaPrefixRecursor (fun n=>(P n:ℝ)) fuel ps N|≤3*2^ps.length := by
  induction fuel generalizing ps N with
  | zero => cases N <;> simp [integerSigmaPrefixRecursor,sigmaPrefixRecursor] <;> positivity
  | succ f ih =>
    cases N with
    | zero => simp only [integerSigmaPrefixRecursor,sigmaPrefixRecursor,Int.cast_zero,sub_self,abs_zero]; positivity
    | succ n =>
      cases ps with
      | nil => simp [integerSigmaPrefixRecursor,sigmaPrefixRecursor]
      | cons p ps =>
        have hp2 := hp p (by simp)
        have hpR : (2:ℝ)≤p := by exact_mod_cast hp2
        have htail : ∀ r∈ps, 2≤r := fun r hr=>hp r (by simp [hr])
        have h1 := ih ps (n+1) htail
        have h2 := ih (p::ps) ((n+1)/p) hp
        have hden : 0<(p:ℝ)+1 := by positivity
        have hscale : (1/((p:ℝ)+1):ℝ)≤1/3 := one_div_le_one_div_of_le (by norm_num) (by linarith)
        have hpow : (1:ℝ)≤2^ps.length := one_le_pow₀ (by norm_num)
        have hh := rounded_add_div_error (integerSigmaPrefixRecursor P f ps (n+1))
          (integerSigmaPrefixRecursor P f (p::ps) ((n+1)/p))
          (sigmaPrefixRecursor (fun n=>(P n:ℝ)) f ps (n+1))
          (sigmaPrefixRecursor (fun n=>(P n:ℝ)) f (p::ps) ((n+1)/p)) (p+1) (by omega)
        simp only [Nat.cast_add,Nat.cast_one] at hh
        have hquot := div_le_div_of_nonneg_right h2 hden.le
        have hq := mul_le_mul_of_nonneg_left hscale (show (0:ℝ)≤3*2^(p::ps).length by positivity)
        rw [integerSigmaPrefixRecursor,sigmaPrefixRecursor]
        simp only [List.length_cons,pow_succ] at h2 hq hquot ⊢
        simp only [div_eq_mul_inv,one_mul] at hh hquot hq ⊢
        nlinarith

theorem sigmaPrefixRecursor_scale (W : ℕ→ℝ) (c : ℝ) (fuel : ℕ) (ps : List ℕ) (N : ℕ) :
    sigmaPrefixRecursor (fun n=>c*W n) fuel ps N=c*sigmaPrefixRecursor W fuel ps N := by
  induction fuel generalizing ps N with
  | zero => cases N <;> simp [sigmaPrefixRecursor]
  | succ f ih =>
    cases N with
    | zero => simp [sigmaPrefixRecursor]
    | succ n => cases ps <;> simp only [sigmaPrefixRecursor,ih] <;> ring

theorem integerSigmaPrefixRecursor_approx (W : ℕ→ℝ) (P : ℕ→ℤ)
    (fuel : ℕ) (ps : List ℕ) (N M : ℕ) (Q ε : ℝ)
    (hQ : 0<Q) (hε : 0≤ε) (hN : N≤M) (hp : ∀ p∈ps, 2≤p)
    (hbase : ∀ n≤M, |W n-(P n:ℝ)/Q|≤ε) :
    |sigmaPrefixRecursor W fuel ps N-(integerSigmaPrefixRecursor P fuel ps N:ℝ)/Q|≤
      (ε+3/Q)*2^ps.length := by
  let V := fun n : ℕ=>(P n:ℝ)/Q
  have h1 := sigmaPrefixRecursor_stability W V fuel ps N M ε hε hN hp hbase
  have h2 := integerSigmaPrefixRecursor_error P fuel ps N hp
  have heq : sigmaPrefixRecursor V fuel ps N=
      sigmaPrefixRecursor (fun n=>(P n:ℝ)) fuel ps N/Q := by
    have hv : V=fun n=>(1/Q)*(P n:ℝ) := by funext n; dsimp only [V]; ring
    rw [hv,sigmaPrefixRecursor_scale]
    ring
  have herr : |sigmaPrefixRecursor V fuel ps N-(integerSigmaPrefixRecursor P fuel ps N:ℝ)/Q|≤
      (3/Q)*2^ps.length := by
    rw [heq,←sub_div,abs_div,abs_of_pos hQ,abs_sub_comm]
    exact (div_le_div_of_nonneg_right h2 hQ.le).trans_eq (by ring)
  have htri := abs_sub_le (sigmaPrefixRecursor W fuel ps N) (sigmaPrefixRecursor V fuel ps N)
    ((integerSigmaPrefixRecursor P fuel ps N:ℝ)/Q)
  nlinarith

theorem integerSigmaPrefixRecursor_coprime_approx (P : ℕ→ℤ)
    (fuel : ℕ) (ps : List ℕ) (N M : ℕ) (Q ε : ℝ)
    (hQ : 0<Q) (hε : 0≤ε) (hN : N≤M)
    (hprime : ∀ p∈ps, Nat.Prime p) (hpair : ps.Pairwise Nat.Coprime)
    (hf : N+ps.length+1≤fuel)
    (hbase : ∀ n≤M, |sigmaCoprimePrefix 1 n-(P n:ℝ)/Q|≤ε) :
    |sigmaCoprimePrefix ps.prod N-(integerSigmaPrefixRecursor P fuel ps N:ℝ)/Q|≤
      (ε+3/Q)*2^ps.length := by
  rw [←sigmaPrefixRecursor_exact fuel ps N hprime hpair hf]
  exact integerSigmaPrefixRecursor_approx _ P fuel ps N M Q ε hQ hε hN
    (fun p hp=>(hprime p hp).two_le) hbase

theorem two_pow_length_le_prod (ps : List ℕ) (hp : ∀ p∈ps, 2≤p) :
    2^ps.length≤ps.prod := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have htail : ∀ r∈ps, 2≤r := fun r hr=>hp r (by simp [hr])
    simpa only [List.length_cons,List.prod_cons,pow_succ,Nat.mul_comm] using
      Nat.mul_le_mul (hp p (by simp)) (ih htail)

end HelfgottQuadratic

end

section

open Finset ArithmeticFunction Helfgott
open scoped BigOperators Classical
namespace HelfgottQuadratic

theorem integer_prefix_sum_sound (a P : ℕ→ℤ) (K : ℕ) (hP0 : P 0=0)
    (hstep : ∀ n<K, P (n+1)=P n+a (n+1)) : ∀ n≤K, P n=∑ k ∈ Icc 1 n, a k := by
  intro n hn
  induction n with
  | zero => simp [hP0]
  | succ n ih => rw [hstep n (by omega),ih (by omega),sum_Icc_succ_top (by omega : 1≤n+1)]

theorem sigma_prefix_integer_rounding (a P : ℕ→ℤ) (K : ℕ) (Q : ℝ) (hQ : 0<Q)
    (hP0 : P 0=0) (hstep : ∀ n<K, P (n+1)=P n+a (n+1))
    (hweight : ∀ n∈Icc 1 K, |mobiusSigmaWeight n-(a n:ℝ)/Q|≤1/Q) :
    ∀ n≤K, |sigmaCoprimePrefix 1 n-(P n:ℝ)/Q|≤(K:ℝ)/Q := by
  intro n hn
  have he := integer_prefix_sum_sound a P K hP0 hstep n hn
  rw [he,Int.cast_sum,Finset.sum_div]
  simp only [sigmaCoprimePrefix,Nat.coprime_one_right_iff,ite_true]
  rw [←sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Icc 1 n, |mobiusSigmaWeight k-(a k:ℝ)/Q| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Icc 1 n, (1/Q:ℝ) := sum_le_sum (fun k hk=>hweight k
      (mem_Icc.mpr ⟨(mem_Icc.mp hk).1,(mem_Icc.mp hk).2.trans hn⟩))
    _ = (n:ℝ)/Q := by simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hn) hQ.le

theorem primeFactorsList_pairwise_coprime (n : ℕ) (hn : Squarefree n) :
    n.primeFactorsList.Pairwise Nat.Coprime := by
  apply hn.nodup_primeFactorsList.pairwise_of_forall_ne
  intro p hp q hq hpq
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactorsList hp) (Nat.prime_of_mem_primeFactorsList hq)).mpr hpq

def squarefreeSigmaPrefixApprox (P : ℕ→ℤ) (n N : ℕ) : ℤ :=
  integerSigmaPrefixRecursor P (N+n.primeFactorsList.length+1) n.primeFactorsList N

theorem squarefreeSigmaPrefixApprox_error (P : ℕ→ℤ) (n N K : ℕ) (Q : ℝ)
    (hQ : 0<Q) (hn : Squarefree n) (hnK : n≤K) (hN : N≤K)
    (hbase : ∀ k≤K, |sigmaCoprimePrefix 1 k-(P k:ℝ)/Q|≤(K:ℝ)/Q) :
    |sigmaCoprimePrefix n N-(squarefreeSigmaPrefixApprox P n N:ℝ)/Q|≤
      ((K:ℝ)+3)*(K:ℝ)/Q := by
  have hp : ∀ p∈n.primeFactorsList, Nat.Prime p := fun p hp=>Nat.prime_of_mem_primeFactorsList hp
  have hh := integerSigmaPrefixRecursor_coprime_approx P
    (N+n.primeFactorsList.length+1) n.primeFactorsList N K Q ((K:ℝ)/Q)
    hQ (by positivity) hN hp (primeFactorsList_pairwise_coprime n hn) le_rfl hbase
  rw [Nat.prod_primeFactorsList hn.ne_zero] at hh
  have hb := two_pow_length_le_prod n.primeFactorsList (fun p hp'=>(hp p hp').two_le)
  rw [Nat.prod_primeFactorsList hn.ne_zero] at hb
  have hpow : (2:ℝ)^n.primeFactorsList.length≤K := by exact_mod_cast hb.trans hnK
  apply hh.trans
  calc
    _ ≤ ((K:ℝ)/Q+3/Q)*(K:ℝ) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

end HelfgottQuadratic

end

section

open Finset ArithmeticFunction Helfgott
open scoped BigOperators Classical
namespace HelfgottQuadratic

def mobiusSigmaRat (n : ℕ) : ℚ := (moebius n:ℤ)/(∏ p ∈ n.primeFactors, ((p:ℚ)+1))

def coprimePairRat (N : ℕ) : ℚ :=
  ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, if Nat.Coprime a b then mobiusSigmaRat a*mobiusSigmaRat b else 0

def coprimeDensityRat (N : ℕ) : ℚ :=
  ∑ s ∈ Icc 1 N, (1/(s:ℚ))*coprimePairRat (N/s)

theorem mobiusSigmaRat_cast (n : ℕ) : (mobiusSigmaRat n:ℝ)=mobiusSigmaWeight n := by
  simp only [mobiusSigmaRat,mobiusSigmaWeight,Rat.cast_div,Rat.cast_intCast,Rat.cast_prod,
    Rat.cast_add,Rat.cast_natCast,Rat.cast_one]

theorem coprimePairRat_cast (N : ℕ) : (coprimePairRat N:ℝ)=coprimePairPrefix mobiusSigmaWeight N := by
  simp only [coprimePairRat,coprimePairPrefix,Rat.cast_sum,apply_ite,Rat.cast_mul,
    Rat.cast_zero,mobiusSigmaRat_cast]

theorem coprimeDensityRat_cast (N : ℕ) : (coprimeDensityRat N:ℝ)=coprimeDensityPrefix mobiusSigmaWeight N := by
  simp only [coprimeDensityRat,coprimeDensityPrefix,Rat.cast_sum,Rat.cast_mul,
    Rat.cast_div,Rat.cast_one,Rat.cast_natCast,coprimePairRat_cast]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coprimeDensityRat_check_32 :
    (List.range 33).all (fun n=>decide (coprimeDensityRat n≤1))=true := by
  decide +kernel

theorem coprimeDensityPrefix_le_one_32 (N : ℕ) (hN : N≤32) :
    coprimeDensityPrefix mobiusSigmaWeight N≤1 := by
  have hh := List.all_eq_true.mp coprimeDensityRat_check_32 N (List.mem_range.mpr (by omega))
  have hr : coprimeDensityRat N≤1 := of_decide_eq_true hh
  rw [←coprimeDensityRat_cast]
  exact_mod_cast hr

end HelfgottQuadratic

end

section

open Finset ArithmeticFunction Helfgott
open scoped BigOperators
namespace HelfgottQuadratic

inductive DensityIntTree where
  | leaf (value : ℤ)
  | branch (left right : DensityIntTree)

def densityTreeValue : ℕ→DensityIntTree→ℕ→ℤ
  | 0, .leaf v, _ => v
  | d+1, .branch l r, n =>
    if n<2^d then densityTreeValue d l n else densityTreeValue d r (n-2^d)
  | _, _, _ => 0

def densityIntegerCheck (a F G : ℕ→ℤ) (K Q T : ℕ) : Bool :=
  (G 0==0) &&
  (List.range K).all (fun n=>F (n+1)==F n+integerPairIncrement a (n+1)) &&
  (List.range K).all (fun n=>decide (G n+(∑ s ∈ (n+1).divisors,
    integerCeilDiv (F ((n+1)/s)-F ((n+1)/s-1)) s)≤G (n+1))) &&
  (List.range (K+1)).all (fun n=>decide (G n≤T)) &&
  (List.range (K+1)).all (fun n=>decide (|mobiusSigmaRat n-(a n:ℚ)/(Q:ℚ)|≤1/(Q:ℚ)))

theorem mobiusSigmaWeight_abs_le_one (n : ℕ) : |mobiusSigmaWeight n|≤1 := by
  have hp : (1:ℝ)≤∏ p ∈ n.primeFactors, ((p:ℝ)+1) := one_le_prod (by intro p hp; have := Nat.cast_nonneg (α:=ℝ) p; linarith)
  have hm : |((moebius n:ℤ):ℝ)|≤1 := by exact_mod_cast abs_moebius_le_one (n:=n)
  unfold mobiusSigmaWeight
  rw [abs_div,abs_of_nonneg (by linarith : (0:ℝ)≤∏ p ∈ n.primeFactors, ((p:ℝ)+1))]
  exact (div_le_one (by linarith : (0:ℝ)<∏ p ∈ n.primeFactors, ((p:ℝ)+1))).mpr (hm.trans hp)

theorem densityIntegerCheck_sound (a F G : ℕ→ℤ) (K Q T : ℕ) (hQ : 0<Q)
    (hcheck : densityIntegerCheck a F G K Q T=true) (n : ℕ) (hn : n≤K) :
    coprimeDensityPrefix mobiusSigmaWeight n≤(T:ℝ)/(Q:ℝ)^2+
      (K:ℝ)^3*(1/(Q:ℝ))*(2+1/(Q:ℝ)) := by
  simp only [densityIntegerCheck,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨⟨hz,hF⟩,hG⟩,hbound⟩,hweight⟩ := hcheck
  have hQR : (0:ℝ)<Q := by exact_mod_cast hQ
  apply integer_density_rounded_bound mobiusSigmaWeight a F G K (Q:ℝ) ((T:ℝ)/(Q:ℝ)^2)
    hQR hz (fun k hk=>mobiusSigmaWeight_abs_le_one k) ?_ ?_ ?_ ?_ n hn
  · intro k hk
    have hh := hweight k (List.mem_range.mpr (by have := (mem_Icc.mp hk).2; omega))
    have hhR : |(mobiusSigmaRat k:ℝ)-(a k:ℝ)/(Q:ℝ)|≤1/(Q:ℝ) := by
      have hc := (Rat.cast_le (K:=ℝ)).mpr hh
      simpa only [Rat.cast_abs,Rat.cast_sub,Rat.cast_div,Rat.cast_intCast,
        Rat.cast_natCast,Rat.cast_one] using hc
    simpa only [mobiusSigmaRat_cast] using hhR
  · intro k hk
    exact hF k (List.mem_range.mpr hk)
  · intro k hk
    exact hG k (List.mem_range.mpr hk)
  · intro k hk
    have hh : (G k:ℝ)≤T := by exact_mod_cast hbound k (List.mem_range.mpr (by omega))
    exact hh.trans_eq (by field_simp)

end HelfgottQuadratic

end

section

open Finset
open scoped BigOperators Classical
namespace HelfgottQuadratic

noncomputable def weightedDivisorPrefix (f : ℕ→ℝ) (N : ℕ) : ℝ :=
  ∑ s ∈ Icc 1 N, (1/(s:ℝ))*(∑ a ∈ Icc 1 (N/s), f a)

theorem coprimeDensityPrefix_eq_weighted_increment (w : ℕ→ℝ) (N : ℕ) :
    coprimeDensityPrefix w N=weightedDivisorPrefix (coprimePairIncrement w) N := by
  simp only [coprimeDensityPrefix,weightedDivisorPrefix,coprimePairPrefix_eq_sum_increment]

theorem weightedDivisorPrefix_eq_divisor_sum (f : ℕ→ℝ) (N : ℕ) :
    weightedDivisorPrefix f N=∑ n ∈ Icc 1 N, ∑ s ∈ n.divisors, f (n/s)/(s:ℝ) := by
  rw [finite_positive_divisor_reindex N (fun s a=>f a/(s:ℝ))]
  unfold weightedDivisorPrefix
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro s hs
  apply sum_congr rfl
  intro a ha
  ring

theorem weightedDivisorPrefix_succ (f : ℕ→ℝ) (N : ℕ) :
    weightedDivisorPrefix f (N+1)=weightedDivisorPrefix f N+
      ∑ s ∈ (N+1).divisors, f ((N+1)/s)/(s:ℝ) := by
  simp only [weightedDivisorPrefix_eq_divisor_sum]
  rw [sum_Icc_succ_top (by omega : 1≤N+1)]

theorem weightedDivisorPrefix_scale (f : ℕ→ℝ) (c : ℝ) (N : ℕ) :
    weightedDivisorPrefix (fun n=>c*f n) N=c*weightedDivisorPrefix f N := by
  unfold weightedDivisorPrefix
  simp_rw [←mul_sum]
  rw [mul_sum]
  apply sum_congr rfl
  intro s hs
  ring

theorem weightedDivisorPrefix_stability (f g : ℕ→ℝ) (N : ℕ) (ε : ℝ) (hε : 0≤ε)
    (he : ∀ n∈Icc 1 N, |f n-g n|≤ε) :
    |weightedDivisorPrefix f N-weightedDivisorPrefix g N|≤(N:ℝ)^2*ε := by
  unfold weightedDivisorPrefix
  rw [←sum_sub_distrib]
  calc
    _ ≤ ∑ s ∈ Icc 1 N, |(1/(s:ℝ))*(∑ a ∈ Icc 1 (N/s), f a)-(1/(s:ℝ))*(∑ a ∈ Icc 1 (N/s), g a)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ Icc 1 N, (N:ℝ)*ε := by
      apply sum_le_sum
      intro s hs
      have hs1 : (1:ℝ)≤s := by exact_mod_cast (mem_Icc.mp hs).1
      have hinner : |(∑ a ∈ Icc 1 (N/s), f a)-(∑ a ∈ Icc 1 (N/s), g a)|≤(N:ℝ)*ε := by
        rw [←sum_sub_distrib]
        calc
          _ ≤ ∑ a ∈ Icc 1 (N/s), |f a-g a| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ a ∈ Icc 1 (N/s), ε := sum_le_sum (fun a ha=>he a
            (mem_Icc.mpr ⟨(mem_Icc.mp ha).1,(mem_Icc.mp ha).2.trans (Nat.div_le_self _ _)⟩))
          _ = ((N/s:ℕ):ℝ)*ε := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.div_le_self N s) hε
      rw [←mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤1/(s:ℝ))]
      calc
        _ ≤ (1/(s:ℝ))*((N:ℝ)*ε) := mul_le_mul_of_nonneg_left hinner (by positivity)
        _ ≤ 1*((N:ℝ)*ε) := mul_le_mul_of_nonneg_right (by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hs1) (by positivity)
        _ = _ := by ring
    _ = _ := by simp; ring

theorem integer_weighted_divisor_prefix_sound (b G : ℕ→ℤ) (K : ℕ) (hG0 : G 0=0)
    (hstep : ∀ n<K, G n+(∑ s ∈ (n+1).divisors, integerCeilDiv (b ((n+1)/s)) s)≤G (n+1)) :
    ∀ n≤K, weightedDivisorPrefix (fun k=>(b k:ℝ)) n≤(G n:ℝ) := by
  intro n hn
  induction n with
  | zero => simp [weightedDivisorPrefix,hG0]
  | succ n ih =>
    rw [weightedDivisorPrefix_succ]
    have hh : (∑ s ∈ (n+1).divisors, (b ((n+1)/s):ℝ)/(s:ℝ))≤
        ((∑ s ∈ (n+1).divisors, integerCeilDiv (b ((n+1)/s)) s:ℤ):ℝ) := by
      rw [Int.cast_sum]
      exact sum_le_sum (fun s hs=>integerCeilDiv_upper _ _)
    have hr : (G n:ℝ)+((∑ s ∈ (n+1).divisors, integerCeilDiv (b ((n+1)/s)) s:ℤ):ℝ)≤(G (n+1):ℝ) := by
      exact_mod_cast hstep n (by omega)
    exact (add_le_add (ih (by omega)) hh).trans hr

end HelfgottQuadratic

end

section

open Finset ArithmeticFunction Helfgott
open scoped BigOperators Classical
namespace HelfgottQuadratic

theorem doubled_product_approx (w v A R ε E K : ℝ)
    (hε : 0≤ε) (hE : 0≤E) (hK : 0≤K)
    (hw : |w-v|≤ε) (hv : |v|≤2) (hA : |A|≤K) (hR : |A-R|≤E) :
    |2*w*A-2*v*R|≤2*ε*K+4*E := by
  have he : 2*w*A-2*v*R=2*((w-v)*A+v*(A-R)) := by ring
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  have hh := abs_add_le ((w-v)*A) (v*(A-R))
  rw [abs_mul,abs_mul] at hh
  have h1 := mul_le_mul hw hA (abs_nonneg _) hε
  have h2 := mul_le_mul hv hR (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
  nlinarith

theorem square_approx (w v ε : ℝ) (hε : 0≤ε) (hw : |w|≤1) (hv : |v|≤2) (he : |w-v|≤ε) :
    |w^2-v^2|≤3*ε := by
  have hid : w^2-v^2=(w-v)*(w+v) := by ring
  rw [hid,abs_mul]
  have hsum : |w+v|≤3 := by linarith [abs_add_le w v]
  exact (mul_le_mul he hsum (abs_nonneg _) hε).trans_eq (by ring)

def sigmaIncrementApprox (a P : ℕ→ℤ) (n : ℕ) : ℤ :=
  if moebius n=0 then 0 else 2*a n*squarefreeSigmaPrefixApprox P n (n-1)+
    if n=1 then (a n)^2 else 0

theorem sigmaIncrementApprox_error (a P : ℕ→ℤ) (K : ℕ) (Q : ℝ)
    (hK : 1≤K) (hQ : 1≤Q) (hP0 : P 0=0)
    (hstep : ∀ n<K, P (n+1)=P n+a (n+1))
    (hweight : ∀ n∈Icc 1 K, |mobiusSigmaWeight n-(a n:ℝ)/Q|≤1/Q)
    (n : ℕ) (hn : n∈Icc 1 K) :
    |coprimePairIncrement mobiusSigmaWeight n-(sigmaIncrementApprox a P n:ℝ)/Q^2|≤
      10*((K:ℝ)+3)*(K:ℝ)/Q := by
  have hQp : 0<Q := by linarith
  have hKR : (1:ℝ)≤K := by exact_mod_cast hK
  by_cases hmu : moebius n=0
  · have hw0 : mobiusSigmaWeight n=0 := by simp [mobiusSigmaWeight,hmu]
    simp only [sigmaIncrementApprox,if_pos hmu,Int.cast_zero,zero_div,coprimePairIncrement,
      hw0,mul_zero,zero_mul,zero_pow (by norm_num : 2≠0),ite_self,add_zero,sub_self,abs_zero]
    positivity
  have hsq := moebius_ne_zero_iff_squarefree.mp hmu
  let w := mobiusSigmaWeight n
  let v := (a n:ℝ)/Q
  let A := sigmaCoprimePrefix n (n-1)
  let R := (squarefreeSigmaPrefixApprox P n (n-1):ℝ)/Q
  let E := ((K:ℝ)+3)*(K:ℝ)/Q
  have hbase := sigma_prefix_integer_rounding a P K Q hQp hP0 hstep hweight
  have hR : |A-R|≤E := squarefreeSigmaPrefixApprox_error P n (n-1) K Q hQp hsq (mem_Icc.mp hn).2 (by have := (mem_Icc.mp hn).2; omega) hbase
  have hw : |w|≤1 := mobiusSigmaWeight_abs_le_one n
  have he : |w-v|≤1/Q := hweight n hn
  have hε : 0≤1/Q := by positivity
  have hε1 : 1/Q≤1 := (div_le_one hQp).mpr hQ
  have hv : |v|≤2 := by
    have hh := abs_add_le w (v-w)
    rw [show w+(v-w)=v by ring,abs_sub_comm v w] at hh
    linarith
  have hA : |A|≤(K:ℝ) := by
    unfold A sigmaCoprimePrefix
    calc
      _ ≤ ∑ k ∈ Icc 1 (n-1), |if Nat.Coprime k n then mobiusSigmaWeight k else 0| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Icc 1 (n-1), (1:ℝ) := by
        apply sum_le_sum
        intro k hk
        split_ifs
        · exact mobiusSigmaWeight_abs_le_one k
        · norm_num
      _ = ((n-1:ℕ):ℝ) := by simp
      _ ≤ _ := by exact_mod_cast (show n-1≤K by have := (mem_Icc.mp hn).2; omega)
  have hmain := doubled_product_approx w v A R (1/Q) E (K:ℝ) hε (by dsimp [E]; positivity)
    (Nat.cast_nonneg _) he hv hA hR
  have hdiag : |(if n=1 then w^2 else 0)-(if n=1 then v^2 else 0)|≤3/Q := by
    by_cases h1 : n=1
    · simpa only [if_pos h1,mul_one_div] using square_approx w v (1/Q) hε hw hv he
    · simp only [if_neg h1,sub_self,abs_zero]; positivity
  have hreal : (sigmaIncrementApprox a P n:ℝ)/Q^2=2*v*R+(if n=1 then v^2 else 0) := by
    rw [sigmaIncrementApprox,if_neg hmu]
    dsimp only [v,R]
    split_ifs <;> push_cast <;> field_simp <;> ring
  rw [hreal]
  change |2*w*A+(if n=1 then w^2 else 0)-(2*v*R+(if n=1 then v^2 else 0))|≤_
  rw [show 2*w*A+(if n=1 then w^2 else 0)-(2*v*R+(if n=1 then v^2 else 0))=
    (2*w*A-2*v*R)+((if n=1 then w^2 else 0)-(if n=1 then v^2 else 0)) by ring]
  have htri := abs_add_le (2*w*A-2*v*R) ((if n=1 then w^2 else 0)-(if n=1 then v^2 else 0))
  have hEK : (K:ℝ)/Q≤E := by dsimp only [E]; gcongr; nlinarith
  have hE1 : 1/Q≤E := (div_le_div_of_nonneg_right hKR hQp.le).trans hEK
  rw [show 10*((K:ℝ)+3)*(K:ℝ)/Q=10*E by dsimp [E]; ring]
  simp only [one_div] at hmain hE1
  rw [div_eq_mul_inv] at hEK
  rw [div_eq_mul_inv] at hdiag
  have hE0 : 0≤E := by dsimp [E]; positivity
  nlinarith

end HelfgottQuadratic

end

section

open Finset
namespace HelfgottQuadratic

def factorDivisors : List ℕ→Finset ℕ
  | [] => {1}
  | p::ps => let ds := factorDivisors ps; ds ∪ ds.image (p*·)

theorem mem_factorDivisors (ps : List ℕ) (hp : ∀ p∈ps, Nat.Prime p) (d : ℕ) :
    d∈factorDivisors ps ↔ d∣ps.prod := by
  induction ps generalizing d with
  | nil => simp [factorDivisors]
  | cons p ps ih =>
    have hprime := hp p (by simp)
    have htail : ∀ r∈ps, Nat.Prime r := fun r hr=>hp r (by simp [hr])
    simp only [factorDivisors,mem_union,mem_image,List.prod_cons]
    constructor
    · rintro (hd | ⟨a,ha,rfl⟩)
      · exact dvd_mul_of_dvd_right ((ih htail d).mp hd) p
      · exact mul_dvd_mul_left p ((ih htail a).mp ha)
    · intro hd
      obtain ⟨a,b,ha,hb,hab⟩ := exists_dvd_and_dvd_of_dvd_mul hd
      rcases (Nat.dvd_prime hprime).mp ha with ha | ha
      · left
        apply (ih htail d).mpr
        rw [hab,ha,one_mul]
        exact hb
      · right
        exact ⟨b,(ih htail b).mpr hb,by simpa [ha] using hab.symm⟩

def fastDivisors (n : ℕ) : Finset ℕ :=
  if n=0 then ∅ else factorDivisors n.primeFactorsList

theorem fastDivisors_eq (n : ℕ) : fastDivisors n=n.divisors := by
  by_cases hn : n=0
  · subst n; simp [fastDivisors]
  · ext d
    rw [fastDivisors,if_neg hn]
    simp only [mem_factorDivisors n.primeFactorsList
      (fun p hp=>Nat.prime_of_mem_primeFactorsList hp),Nat.prod_primeFactorsList hn,
      Nat.mem_divisors,hn,ne_eq,not_false_eq_true,and_true]

end HelfgottQuadratic

end

section

open Finset ArithmeticFunction Helfgott
open scoped BigOperators
namespace HelfgottQuadratic

theorem fast_density_rounded_bound (a P b G : ℕ→ℤ) (K : ℕ) (Q C : ℝ)
    (hK : 1≤K) (hQ : 1≤Q) (hP0 : P 0=0) (hG0 : G 0=0)
    (hP : ∀ k<K, P (k+1)=P k+a (k+1))
    (hweight : ∀ k∈Icc 1 K, |mobiusSigmaWeight k-(a k:ℝ)/Q|≤1/Q)
    (hb : ∀ k∈Icc 1 K, b k=sigmaIncrementApprox a P k)
    (hG : ∀ k<K, G k+(∑ s ∈ (k+1).divisors, integerCeilDiv (b ((k+1)/s)) s)≤G (k+1))
    (hbound : ∀ k≤K, (G k:ℝ)≤C*Q^2) (n : ℕ) (hn : n≤K) :
    coprimeDensityPrefix mobiusSigmaWeight n≤C+10*((K:ℝ)+3)*(K:ℝ)^3/Q := by
  have hQp : 0<Q := by linarith
  let ε : ℝ := 10*((K:ℝ)+3)*(K:ℝ)/Q
  have hε : 0≤ε := by dsimp [ε]; positivity
  have he : ∀ k∈Icc 1 n,
      |coprimePairIncrement mobiusSigmaWeight k-(b k:ℝ)/Q^2|≤ε := by
    intro k hk
    have hkK : k∈Icc 1 K := mem_Icc.mpr ⟨(mem_Icc.mp hk).1,(mem_Icc.mp hk).2.trans hn⟩
    rw [hb k hkK]
    exact sigmaIncrementApprox_error a P K Q hK hQ hP0 hP hweight k hkK
  have hstab := weightedDivisorPrefix_stability (coprimePairIncrement mobiusSigmaWeight)
    (fun k=>(b k:ℝ)/Q^2) n ε hε he
  have hscale : weightedDivisorPrefix (fun k=>(b k:ℝ)/Q^2) n=
      weightedDivisorPrefix (fun k=>(b k:ℝ)) n/Q^2 := by
    simp only [div_eq_mul_inv,mul_comm _ ((Q^2)⁻¹),weightedDivisorPrefix_scale]
  have hint := integer_weighted_divisor_prefix_sound b G K hG0 hG n hn
  have hupper : weightedDivisorPrefix (fun k=>(b k:ℝ)/Q^2) n≤C := by
    rw [hscale]
    exact (div_le_div_of_nonneg_right (hint.trans (hbound n hn)) (sq_nonneg Q)).trans_eq
      (by field_simp)
  have herr : (n:ℝ)^2*ε≤10*((K:ℝ)+3)*(K:ℝ)^3/Q := by
    calc
      _ ≤ (K:ℝ)^2*ε := mul_le_mul_of_nonneg_right (by gcongr) hε
      _ = _ := by dsimp [ε]; ring
  rw [coprimeDensityPrefix_eq_weighted_increment]
  have hdiff := (le_abs_self _).trans hstab
  linarith

def fastDensityCheck (a P b G : ℕ→ℤ) (K Q T : ℕ) : Bool :=
  (P 0==0) && (G 0==0) &&
  (List.range K).all (fun n=>P (n+1)==P n+a (n+1)) &&
  (List.range K).all (fun n=>b (n+1)==sigmaIncrementApprox a P (n+1)) &&
  (List.range K).all (fun n=>decide (G n+(∑ s ∈ fastDivisors (n+1),
    integerCeilDiv (b ((n+1)/s)) s)≤G (n+1))) &&
  (List.range (K+1)).all (fun n=>decide (G n≤T)) &&
  (List.range K).all (fun n=>decide (|mobiusSigmaRat (n+1)-(a (n+1):ℚ)/(Q:ℚ)|≤1/(Q:ℚ)))

theorem fastDensityCheck_sound (a P b G : ℕ→ℤ) (K Q T : ℕ)
    (hK : 1≤K) (hQ : 1≤Q) (hcheck : fastDensityCheck a P b G K Q T=true)
    (n : ℕ) (hn : n≤K) :
    coprimeDensityPrefix mobiusSigmaWeight n≤(T:ℝ)/(Q:ℝ)^2+
      10*((K:ℝ)+3)*(K:ℝ)^3/(Q:ℝ) := by
  simp only [fastDensityCheck,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨⟨⟨⟨hP0,hG0⟩,hP⟩,hb⟩,hG⟩,hbound⟩,hweight⟩ := hcheck
  simp only [fastDivisors_eq] at hG
  have hQR : (1:ℝ)≤Q := by exact_mod_cast hQ
  apply fast_density_rounded_bound a P b G K (Q:ℝ) ((T:ℝ)/(Q:ℝ)^2)
    hK hQR hP0 hG0 (fun k hk=>hP k (List.mem_range.mpr hk)) ?_ ?_
    (fun k hk=>hG k (List.mem_range.mpr hk)) ?_ n hn
  · intro k hk
    have hk0 := (mem_Icc.mp hk).1
    have hh := hweight (k-1) (List.mem_range.mpr (by have := (mem_Icc.mp hk).2; omega))
    rw [Nat.sub_add_cancel hk0] at hh
    have hc := (Rat.cast_le (K:=ℝ)).mpr hh
    simpa only [Rat.cast_abs,Rat.cast_sub,Rat.cast_div,Rat.cast_intCast,
      Rat.cast_natCast,Rat.cast_one,mobiusSigmaRat_cast] using hc
  · intro k hk
    have hh := hb (k-1) (List.mem_range.mpr (by have := mem_Icc.mp hk; omega))
    simpa only [Nat.sub_add_cancel (mem_Icc.mp hk).1] using hh
  · intro k hk
    have hh : (G k:ℝ)≤T := by exact_mod_cast hbound k (List.mem_range.mpr (by omega))
    exact hh.trans_eq (by
      have hQ0 : (Q:ℝ)≠0 := by linarith
      field_simp)

end HelfgottQuadratic

end

section

namespace HelfgottQuadratic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def fast512PTree : DensityIntTree := .branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (1000000000000000000000000000000)))
  (.branch (.leaf (666666666666666666666666666667))
  (.leaf (416666666666666666666666666667))))
  (.branch (.branch (.leaf (416666666666666666666666666667))
  (.leaf (250000000000000000000000000001)))
  (.branch (.leaf (333333333333333333333333333334))
  (.leaf (208333333333333333333333333334)))))
  (.branch (.branch (.branch (.leaf (208333333333333333333333333334))
  (.leaf (208333333333333333333333333334)))
  (.branch (.leaf (263888888888888888888888888889))
  (.leaf (180555555555555555555555555556))))
  (.branch (.branch (.leaf (180555555555555555555555555556))
  (.leaf (109126984126984126984126984128)))
  (.branch (.leaf (150793650793650793650793650794))
  (.leaf (192460317460317460317460317460))))))
  (.branch (.branch (.branch (.branch (.leaf (192460317460317460317460317460))
  (.leaf (136904761904761904761904761905)))
  (.branch (.leaf (136904761904761904761904761905))
  (.leaf (86904761904761904761904761905))))
  (.branch (.branch (.leaf (86904761904761904761904761905))
  (.leaf (118154761904761904761904761905)))
  (.branch (.leaf (145932539682539682539682539682))
  (.leaf (104265873015873015873015873016)))))
  (.branch (.branch (.branch (.leaf (104265873015873015873015873016))
  (.leaf (104265873015873015873015873016)))
  (.branch (.leaf (128075396825396825396825396825))
  (.leaf (128075396825396825396825396825))))
  (.branch (.branch (.leaf (128075396825396825396825396825))
  (.leaf (94742063492063492063492063492)))
  (.branch (.leaf (80853174603174603174603174604))
  (.leaf (49603174603174603174603174604)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (49603174603174603174603174604))
  (.leaf (70436507936507936507936507937)))
  (.branch (.leaf (88955026455026455026455026455))
  (.leaf (109788359788359788359788359788))))
  (.branch (.branch (.leaf (109788359788359788359788359788))
  (.leaf (83472570314675577833472570315)))
  (.branch (.leaf (100139236981342244500139236981))
  (.leaf (117996379838485101642996379838)))))
  (.branch (.branch (.branch (.leaf (117996379838485101642996379838))
  (.leaf (94186856028961292119186856029)))
  (.branch (.leaf (83770189362294625452520189363))
  (.leaf (61042916635021898179792916636))))
  (.branch (.branch (.leaf (61042916635021898179792916636))
  (.leaf (61042916635021898179792916636)))
  (.branch (.leaf (74931805523910787068681805524))
  (.leaf (54098472190577453735348472191))))))
  (.branch (.branch (.branch (.branch (.leaf (54098472190577453735348472191))
  (.leaf (54098472190577453735348472191)))
  (.branch (.leaf (54098472190577453735348472191))
  (.leaf (67987361079466342624237361079))))
  (.branch (.branch (.leaf (67987361079466342624237361079))
  (.leaf (49468842560947824105718842561)))
  (.branch (.leaf (49468842560947824105718842561))
  (.leaf (63357731449836712994607731449)))))
  (.branch (.branch (.branch (.leaf (63357731449836712994607731449))
  (.leaf (75857731449836712994607731449)))
  (.branch (.leaf (86968842560947824105718842560))
  (.leaf (70302175894281157439052175894))))
  (.branch (.branch (.leaf (70302175894281157439052175894))
  (.leaf (54173143636216641310019917830)))
  (.branch (.leaf (64589810302883307976686584496))
  (.leaf (64589810302883307976686584496))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (64589810302883307976686584496))
  (.leaf (76494572207645212738591346400)))
  (.branch (.leaf (69550127763200768294146901956))
  (.leaf (54844245410259591823558666662))))
  (.branch (.branch (.leaf (54844245410259591823558666662))
  (.leaf (65260912076926258490225333328)))
  (.branch (.leaf (58316467632481814045780888884))
  (.leaf (44427578743592925156891999996)))))
  (.branch (.branch (.branch (.leaf (44427578743592925156891999996))
  (.leaf (30914065230079411643378486483)))
  (.branch (.leaf (39685995054640815152150416307))
  (.leaf (39685995054640815152150416307))))
  (.branch (.branch (.leaf (39685995054640815152150416307))
  (.leaf (50102661721307481818817082973)))
  (.branch (.leaf (44150280768926529437864702021))
  (.leaf (31650280768926529437864702021))))))
  (.branch (.branch (.branch (.branch (.leaf (31650280768926529437864702021))
  (.leaf (31650280768926529437864702021)))
  (.branch (.leaf (39586788705434465945801209957))
  (.leaf (27682026800672561183896448053))))
  (.branch (.branch (.leaf (27682026800672561183896448053))
  (.leaf (36941286059931820443155707312)))
  (.branch (.leaf (44517043635689396200731464887))
  (.leaf (52850376969022729534064798220)))))
  (.branch (.branch (.branch (.leaf (52850376969022729534064798220))
  (.leaf (41739265857911618422953687109)))
  (.branch (.leaf (41739265857911618422953687109))
  (.leaf (50667837286483046994382258537))))
  (.branch (.branch (.leaf (50667837286483046994382258537))
  (.leaf (58480337286483046994382258537)))
  (.branch (.leaf (65424781730927491438826702981))
  (.leaf (73758115064260824772160036314)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (73758115064260824772160036314))
  (.leaf (63554033431607763547670240396)))
  (.branch (.leaf (63554033431607763547670240396))
  (.leaf (63554033431607763547670240396))))
  (.branch (.branch (.leaf (63554033431607763547670240396))
  (.leaf (53750111862980312567278083534)))
  (.branch (.leaf (49120482233350682937648453905))
  (.leaf (39505097617966067553033069290)))))
  (.branch (.branch (.branch (.leaf (39505097617966067553033069290))
  (.leaf (34296764284632734219699735957)))
  (.branch (.leaf (40469603790805573725872575463))
  (.leaf (31210344531546314466613316204))))
  (.branch (.branch (.leaf (31210344531546314466613316204))
  (.leaf (22119435440637223557522407114)))
  (.branch (.leaf (17489805811007593927892777485))
  (.leaf (24068753179428646559471724853))))))
  (.branch (.branch (.branch (.branch (.leaf (24068753179428646559471724853))
  (.leaf (15296823354867243050699795029)))
  (.branch (.leaf (11130156688200576384033128363))
  (.leaf (18074601132645020828477572807))))
  (.branch (.branch (.leaf (18074601132645020828477572807))
  (.leaf (18074601132645020828477572807)))
  (.branch (.leaf (23630156688200576384033128362))
  (.leaf (30574601132645020828477572806)))))
  (.branch (.branch (.branch (.leaf (30574601132645020828477572806))
  (.leaf (30574601132645020828477572806)))
  (.branch (.leaf (35950945218666526204821658827))
  (.leaf (41903326171047478585774039779))))
  (.branch (.branch (.leaf (41903326171047478585774039779))
  (.leaf (41903326171047478585774039779)))
  (.branch (.leaf (41903326171047478585774039779))
  (.leaf (34090826171047478585774039779)))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (34090826171047478585774039779))
  (.leaf (39772644352865660403955857960)))
  (.branch (.leaf (35804390384611692149987603992))
  (.leaf (28228632808854116392411846417))))
  (.branch (.branch (.leaf (28228632808854116392411846417))
  (.leaf (34478632808854116392411846417)))
  (.branch (.leaf (39380593593167841882607924848))
  (.leaf (39380593593167841882607924848)))))
  (.branch (.branch (.branch (.leaf (39380593593167841882607924848))
  (.leaf (32134216781573638984057200211)))
  (.branch (.leaf (28661994559351416761834977989))
  (.leaf (21519137416494273904692120847))))
  (.branch (.branch (.leaf (21519137416494273904692120847))
  (.leaf (26727470749827607238025454180)))
  (.branch (.leaf (31357100379457236867655083809))
  (.leaf (37309481331838189248607464761))))))
  (.branch (.branch (.branch (.branch (.leaf (37309481331838189248607464761))
  (.leaf (42865036887393744804163020316)))
  (.branch (.leaf (47369541391898249308667524820))
  (.leaf (47369541391898249308667524820))))
  (.branch (.branch (.leaf (47369541391898249308667524820))
  (.leaf (40702874725231582642000858154)))
  (.branch (.leaf (40702874725231582642000858154))
  (.leaf (34123927356810530010421910786)))))
  (.branch (.branch (.branch (.leaf (34123927356810530010421910786))
  (.leaf (34123927356810530010421910786)))
  (.branch (.leaf (30651705134588307788199688564))
  (.leaf (35860038467921641121533021897))))
  (.branch (.branch (.leaf (35860038467921641121533021897))
  (.leaf (29530924543871008210140616834)))
  (.branch (.leaf (33697591210537674876807283500))
  (.leaf (38327220840167304506436913129)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (38327220840167304506436913129))
  (.leaf (43535554173500637839770246462)))
  (.branch (.leaf (43535554173500637839770246462))
  (.leaf (37437993197890881742209270853))))
  (.branch (.branch (.leaf (37437993197890881742209270853))
  (.leaf (33965770975668659519987048631)))
  (.branch (.leaf (37934024943922627773955302599))
  (.leaf (31981643991541675393002921647)))))
  (.branch (.branch (.branch (.leaf (31981643991541675393002921647))
  (.leaf (31981643991541675393002921647)))
  (.branch (.leaf (28895224238455255639916501894))
  (.leaf (28895224238455255639916501894))))
  (.branch (.branch (.leaf (28895224238455255639916501894))
  (.leaf (23148097801673646444514203044)))
  (.branch (.leaf (20370320023895868666736425267))
  (.leaf (20370320023895868666736425267))))))
  (.branch (.branch (.branch (.branch (.leaf (20370320023895868666736425267))
  (.leaf (24536986690562535333403091933)))
  (.branch (.leaf (28240690394266239037106795636))
  (.leaf (22685134838710683481551240081))))
  (.branch (.branch (.leaf (22685134838710683481551240081))
  (.leaf (17190629344205188976056734587)))
  (.branch (.leaf (14214438868014712785580544111))
  (.leaf (18246696932530841817838608627)))))
  (.branch (.branch (.branch (.leaf (18246696932530841817838608627))
  (.leaf (22632661844811543572224573539)))
  (.branch (.leaf (20028495178144876905557906873))
  (.leaf (24658124807774506535187536502))))
  (.branch (.branch (.leaf (24658124807774506535187536502))
  (.leaf (24658124807774506535187536502)))
  (.branch (.leaf (21880347029996728757409758725))
  (.leaf (16672013696663395424076425392))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (16672013696663395424076425392))
  (.leaf (11517374521405663465313538795)))
  (.branch (.leaf (14918735065623350540143470767))
  (.leaf (11942544589432874349667280291))))
  (.branch (.branch (.leaf (11942544589432874349667280291))
  (.leaf (6892039538927823844616775241)))
  (.branch (.leaf (6892039538927823844616775241))
  (.leaf (1892039538927823844616775241)))))
  (.branch (.branch (.branch (.leaf (1892039538927823844616775241))
  (.leaf (5568510127163117962263834064)))
  (.branch (.leaf (8836483983372268289061219684))
  (.leaf (13003150650038934955727886350))))
  (.branch (.branch (.leaf (13003150650038934955727886350))
  (.leaf (16971404618292903209696140318)))
  (.branch (.leaf (20176532823421108337901268523))
  (.leaf (20176532823421108337901268523))))))
  (.branch (.branch (.branch (.branch (.leaf (20176532823421108337901268523))
  (.leaf (24343199490087775004567935189)))
  (.branch (.leaf (26079310601198886115679046300))
  (.leaf (21362329469123414417565838753))))
  (.branch (.branch (.leaf (21362329469123414417565838753))
  (.leaf (24834551691345636639788060975)))
  (.branch (.leaf (27920971444432056392874480728))
  (.leaf (31708850232310844271662359515)))))
  (.branch (.branch (.branch (.leaf (31708850232310844271662359515))
  (.leaf (35615100232310844271662359515)))
  (.branch (.leaf (38645403262613874574692662545))
  (.leaf (42023781640992252953071040923))))
  (.branch (.branch (.leaf (42023781640992252953071040923))
  (.leaf (45992035609246221207039294891)))
  (.branch (.leaf (43799053153105870329846312435))
  (.leaf (39334767438820156044132026721)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (39334767438820156044132026721))
  (.leaf (39334767438820156044132026721)))
  (.branch (.leaf (42258744047007290547056003329))
  (.leaf (37872779134726588792670038417))))
  (.branch (.branch (.leaf (37872779134726588792670038417))
  (.leaf (33524953047770067053539603635)))
  (.branch (.leaf (31210138232955252238724788821))
  (.leaf (28605971566288585572058122155)))))
  (.branch (.branch (.branch (.leaf (28605971566288585572058122155))
  (.leaf (24332467292784312067784617882)))
  (.branch (.leaf (24332467292784312067784617882))
  (.leaf (27804689515006534290006840104))))
  (.branch (.branch (.leaf (27804689515006534290006840104))
  (.leaf (30929689515006534290006840104)))
  (.branch (.leaf (28614874700191719475192025290))
  (.leaf (24448208033525052808525358624))))))
  (.branch (.branch (.branch (.branch (.leaf (24448208033525052808525358624))
  (.leaf (20315976628566375122574945401)))
  (.branch (.leaf (20315976628566375122574945401))
  (.leaf (20315976628566375122574945401))))
  (.branch (.branch (.leaf (20315976628566375122574945401))
  (.leaf (20315976628566375122574945401)))
  (.branch (.leaf (18331849644439390995590818417))
  (.leaf (21903278215867962424162246988)))))
  (.branch (.branch (.branch (.leaf (21903278215867962424162246988))
  (.leaf (24879468692058438614638437464)))
  (.branch (.leaf (24879468692058438614638437464))
  (.leaf (20911214723804470360670183496))))
  (.branch (.branch (.leaf (20911214723804470360670183496))
  (.leaf (24383436946026692582892405718)))
  (.branch (.leaf (26987603612693359249559072384))
  (.leaf (24672788797878544434744257570))))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (24672788797878544434744257570))
  (.leaf (20796819805630482419240381602)))
  (.branch (.leaf (18902880411691088479846442209))
  (.leaf (22192354095901614795635915893))))
  (.branch (.branch (.leaf (22192354095901614795635915893))
  (.leaf (22192354095901614795635915893)))
  (.branch (.leaf (24717606621154140048161168418))
  (.leaf (20929727833275352169373289631)))))
  (.branch (.branch (.branch (.leaf (20929727833275352169373289631))
  (.leaf (24016147586361771922459709384)))
  (.branch (.leaf (21932814253028438589126376051))
  (.leaf (24710592030806216366904153828))))
  (.branch (.branch (.leaf (24710592030806216366904153828))
  (.leaf (21006888327102512663200450125)))
  (.branch (.leaf (21006888327102512663200450125))
  (.leaf (17330417738867218545553391302))))))
  (.branch (.branch (.branch (.branch (.leaf (17330417738867218545553391302))
  (.leaf (15098274881724361402696248445)))
  (.branch (.leaf (17513733818922429035546489990))
  (.leaf (17513733818922429035546489990))))
  (.branch (.branch (.leaf (17513733818922429035546489990))
  (.leaf (13916611516764155654251525962)))
  (.branch (.leaf (16297563897716536606632478342))
  (.leaf (16297563897716536606632478342)))))
  (.branch (.branch (.branch (.leaf (16297563897716536606632478342))
  (.leaf (12751464606936394762660847137)))
  (.branch (.leaf (11015353495825283651549736026))
  (.leaf (7494226735261903369859595181))))
  (.branch (.branch (.leaf (7494226735261903369859595181))
  (.leaf (5410893401928570036526261848)))
  (.branch (.leaf (3426766417801585909542134864))
  (.leaf (6402956893992062100018325340)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (6402956893992062100018325340))
  (.leaf (6402956893992062100018325340)))
  (.branch (.leaf (4551105042140210248166473489))
  (.leaf (7102125450303475554288922468))))
  (.branch (.branch (.leaf (7102125450303475554288922468))
  (.leaf (3700764906085788479458990496)))
  (.branch (.leaf (3700764906085788479458990496))
  (.leaf (6478542683863566257236768273)))))
  (.branch (.branch (.branch (.leaf (6478542683863566257236768273))
  (.leaf (6478542683863566257236768273)))
  (.branch (.leaf (8700764906085788479458990495))
  (.leaf (11676955382276264669935180971))))
  (.branch (.branch (.leaf (11676955382276264669935180971))
  (.leaf (14517864473185355579026090061)))
  (.branch (.leaf (16710846929325706456219072517))
  (.leaf (19161827321482569201317111732))))))
  (.branch (.branch (.branch (.branch (.leaf (19161827321482569201317111732))
  (.leaf (21849999364493321889489154742)))
  (.branch (.leaf (21849999364493321889489154742))
  (.leaf (18603246117740075136242401496))))
  (.branch (.branch (.leaf (18603246117740075136242401496))
  (.leaf (21007092271586228982396247649)))
  (.branch (.leaf (19270981160475117871285136538))
  (.leaf (16065852955346912743080008333)))))
  (.branch (.branch (.branch (.leaf (16065852955346912743080008333))
  (.leaf (12881139579550734399130963748)))
  (.branch (.leaf (14990844220900945369595098769))
  (.leaf (14990844220900945369595098769))))
  (.branch (.branch (.leaf (14990844220900945369595098769))
  (.leaf (11846190132850630904186293738)))
  (.branch (.leaf (10302980256307421027643083862))
  (.leaf (13080758034085198805420861639))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (13080758034085198805420861639))
  (.leaf (15395572848900013620235676453)))
  (.branch (.leaf (13659461737788902509124565342))
  (.leaf (16437239515566680286902343119))))
  (.branch (.branch (.leaf (16437239515566680286902343119))
  (.leaf (16437239515566680286902343119)))
  (.branch (.leaf (18469759840769932319422668322))
  (.leaf (20742487113497205046695395594)))))
  (.branch (.branch (.branch (.leaf (20742487113497205046695395594))
  (.leaf (23346653780163871713362062260)))
  (.branch (.leaf (24504061187571279120769469667))
  (.leaf (21492012994800194783420072077))))
  (.branch (.branch (.leaf (21492012994800194783420072077))
  (.leaf (21492012994800194783420072077)))
  (.branch (.leaf (23476139978927178910404199061))
  (.leaf (25927120371084041655502238276))))))
  (.branch (.branch (.branch (.branch (.leaf (25927120371084041655502238276))
  (.leaf (22968540489427236921774427626)))
  (.branch (.leaf (22968540489427236921774427626))
  (.leaf (25161522945567587798967410082))))
  (.branch (.branch (.leaf (25161522945567587798967410082))
  (.leaf (27765689612234254465634076748)))
  (.branch (.leaf (27765689612234254465634076748))
  (.leaf (27765689612234254465634076748)))))
  (.branch (.branch (.branch (.leaf (27765689612234254465634076748))
  (.leaf (26029578501123143354522965637)))
  (.branch (.leaf (27945287313383679752990398587))
  (.leaf (25071724094992875155289249162))))
  (.branch (.branch (.leaf (25071724094992875155289249162))
  (.leaf (22214581237850018012432106305)))
  (.branch (.leaf (22214581237850018012432106305))
  (.leaf (22214581237850018012432106305)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (22214581237850018012432106305))
  (.leaf (19389722480787871119776739074)))
  (.branch (.leaf (18000833591898982230887850186))
  (.leaf (20315648406713797045702665000))))
  (.branch (.branch (.leaf (20315648406713797045702665000))
  (.leaf (18579537295602685934591553889)))
  (.branch (.leaf (20431389147454537786443405740))
  (.leaf (17653611369676760008665627963)))))
  (.branch (.branch (.branch (.leaf (17653611369676760008665627963))
  (.leaf (17653611369676760008665627963)))
  (.branch (.leaf (19485113201178591510497129794))
  (.leaf (19485113201178591510497129794))))
  (.branch (.branch (.leaf (19485113201178591510497129794))
  (.leaf (21737365453430843762749382046)))
  (.branch (.leaf (20393279431925467418663360541))
  (.leaf (17675888127577641331706838802))))))
  (.branch (.branch (.branch (.branch (.leaf (17675888127577641331706838802))
  (.leaf (17675888127577641331706838802)))
  (.branch (.leaf (16213899823484074080244850498))
  (.leaf (18528714638298888895059665312))))
  (.branch (.branch (.leaf (18528714638298888895059665312))
  (.leaf (15854917846855038627679986168)))
  (.branch (.leaf (14311707970311828751136776292))
  (.leaf (14311707970311828751136776292)))))
  (.branch (.branch (.branch (.leaf (14311707970311828751136776292))
  (.leaf (16692660351264209703517728672)))
  (.branch (.leaf (16692660351264209703517728672))
  (.leaf (14061081403895788650886149725))))
  (.branch (.branch (.leaf (14061081403895788650886149725))
  (.leaf (16014206403895788650886149725)))
  (.branch (.leaf (17750317515006899761997260836))
  (.leaf (15146150848340233095330594170)))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (15146150848340233095330594170))
  (.leaf (13410039737229121984219483059)))
  (.branch (.leaf (15128252795648365970473778591))
  (.leaf (15128252795648365970473778591))))
  (.branch (.branch (.leaf (15128252795648365970473778591))
  (.leaf (12564150231545801867909676027)))
  (.branch (.leaf (13556213723609293931401739519))
  (.leaf (15871028538424108746216554333)))))
  (.branch (.branch (.branch (.leaf (15871028538424108746216554333))
  (.leaf (17764967932363502685610493726)))
  (.branch (.leaf (19448469615865186187293995409))
  (.leaf (21531802949198519520627328742))))
  (.branch (.branch (.leaf (21531802949198519520627328742))
  (.leaf (19019240135128167761833358893)))
  (.branch (.leaf (20685906801794834428500025559))
  (.leaf (19123406801794834428500025559))))))
  (.branch (.branch (.branch (.branch (.leaf (19123406801794834428500025559))
  (.leaf (16635844612740108060340821579)))
  (.branch (.leaf (15410354416661676687791801972))
  (.leaf (17642497273804533830648944829))))
  (.branch (.branch (.leaf (17642497273804533830648944829))
  (.leaf (17642497273804533830648944829)))
  (.branch (.leaf (16253608384915644941760055941))
  (.leaf (18446590841055995818953038397)))))
  (.branch (.branch (.branch (.leaf (18446590841055995818953038397))
  (.leaf (16007566450812093379928648154)))
  (.branch (.leaf (14684815128060770628605896832))
  (.leaf (16496409330959321353243577991))))
  (.branch (.branch (.leaf (16496409330959321353243577991))
  (.leaf (18579742664292654686576911324)))
  (.branch (.leaf (18579742664292654686576911324))
  (.leaf (20563869648419638813561038308)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (20563869648419638813561038308))
  (.leaf (22349583934133924527846752593)))
  (.branch (.leaf (20960695045245035638957863705))
  (.leaf (18579742664292654686576911325))))
  (.branch (.branch (.leaf (18579742664292654686576911325))
  (.leaf (16210074417847157056245157771)))
  (.branch (.leaf (17782401461872314288949560286))
  (.leaf (17782401461872314288949560286)))))
  (.branch (.branch (.branch (.leaf (17782401461872314288949560286))
  (.leaf (17782401461872314288949560286)))
  (.branch (.leaf (16624994054464906881542152879))
  (.leaf (18641123086722971397671185137))))
  (.branch (.branch (.leaf (18641123086722971397671185137))
  (.leaf (17153027848627733302433089899)))
  (.branch (.leaf (15890401586001470676170463637))
  (.leaf (13575586771186655861355648823))))))
  (.branch (.branch (.branch (.branch (.leaf (13575586771186655861355648823))
  (.leaf (11271439305748867842922469100)))
  (.branch (.leaf (9969355972415534509589135767))
  (.leaf (8580467083526645620700246879))))
  (.branch (.branch (.leaf (8580467083526645620700246879))
  (.leaf (10663800416859978954033580212)))
  (.branch (.leaf (9537674290733852827907454086))
  (.leaf (7264947018006580100634726814)))))
  (.branch (.branch (.branch (.leaf (7264947018006580100634726814))
  (.leaf (7264947018006580100634726814)))
  (.branch (.leaf (5942195695255257349311975492))
  (.leaf (3689943443003005097059723240))))
  (.branch (.branch (.leaf (3689943443003005097059723240))
  (.leaf (5541795294854856948911575091)))
  (.branch (.leaf (7029890532950095044149670329))
  (.leaf (8696557199616761710816336995))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (8696557199616761710816336995))
  (.leaf (6474334977394539488594114773)))
  (.branch (.leaf (6474334977394539488594114773))
  (.leaf (8458461961521523615578241757))))
  (.branch (.branch (.leaf (8458461961521523615578241757))
  (.leaf (10103198803626786773472978599)))
  (.branch (.leaf (11565187107720354024934966903))
  (.leaf (10077091869625115929696871665)))))
  (.branch (.branch (.branch (.leaf (10077091869625115929696871665))
  (.leaf (7893685756087998025766740661)))
  (.branch (.leaf (9342961118406838605476885588))
  (.leaf (9342961118406838605476885588))))
  (.branch (.branch (.leaf (9342961118406838605476885588))
  (.leaf (7178458953904674103312383424)))
  (.branch (.leaf (8046514509460229658867938979))
  (.leaf (5891342095667126210592076911))))))
  (.branch (.branch (.branch (.branch (.leaf (5891342095667126210592076911))
  (.leaf (4589258762333792877258743578)))
  (.branch (.leaf (6013760186835217378683245002))
  (.leaf (3877008050083080626546492866))))
  (.branch (.branch (.leaf (3877008050083080626546492866))
  (.leaf (5715243344200727685370022277)))
  (.branch (.leaf (4557835936793320277962614870))
  (.leaf (6140114417805978505810716135)))))
  (.branch (.branch (.branch (.leaf (6140114417805978505810716135))
  (.leaf (8034053811745372445204655528)))
  (.branch (.leaf (6992387145078705778537988862))
  (.leaf (6992387145078705778537988862))))
  (.branch (.branch (.leaf (6992387145078705778537988862))
  (.leaf (6992387145078705778537988862)))
  (.branch (.leaf (8381276033967594667426877750))
  (.leaf (6297942700634261334093544417)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (6297942700634261334093544417))
  (.leaf (8177641948754562085973243665)))
  (.branch (.leaf (9555052417074121314623381406))
  (.leaf (8252969083740787981290048073))))
  (.branch (.branch (.leaf (8252969083740787981290048073))
  (.leaf (9953649355849631518705014059)))
  (.branch (.leaf (9953649355849631518705014059))
  (.leaf (7904469027980779059688620617)))))
  (.branch (.branch (.branch (.leaf (7904469027980779059688620617))
  (.leaf (9428859271883218084078864519)))
  (.branch (.leaf (9428859271883218084078864519))
  (.leaf (7396338946679966051558539316))))
  (.branch (.branch (.leaf (7396338946679966051558539316))
  (.leaf (9248190798531817903410391167)))
  (.branch (.leaf (8057714608055627427219914977))
  (.leaf (8057714608055627427219914977))))))
  (.branch (.branch (.branch (.branch (.leaf (8057714608055627427219914977))
  (.leaf (9793825719166738538331026088)))
  (.branch (.leaf (8801762227103246474838962596))
  (.leaf (6801762227103246474838962596))))
  (.branch (.branch (.leaf (6801762227103246474838962596))
  (.leaf (8289857465198484570077057834)))
  (.branch (.leaf (9612608787949807321399809156))
  (.leaf (7628481803822823194415682172)))))
  (.branch (.branch (.branch (.leaf (7628481803822823194415682172))
  (.leaf (9262468731927398357814374982)))
  (.branch (.leaf (8105061324519990950406967575))
  (.leaf (8105061324519990950406967575))))
  (.branch (.branch (.leaf (8105061324519990950406967575))
  (.leaf (6144277010794500754328536203)))
  (.branch (.leaf (6915881949066105692600141141))
  (.leaf (8605071138255294881789330330)))))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (8605071138255294881789330330))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))))))

private def fast512P : ℕ→ℤ := densityTreeValue 10 fast512PTree

private def fast512bTree : DensityIntTree := .branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (1000000000000000000000000000000000000000000000000000000000000)))
  (.branch (.leaf (-666666666666666666666666666666000000000000000000000000000000))
  (.leaf (-333333333333333333333333333333500000000000000000000000000000))))
  (.branch (.branch (.leaf (0))
  (.leaf (-138888888888888888888888888888444444444444444444444444444444)))
  (.branch (.leaf (138888888888888888888888888888611111111111111111111111111110))
  (.leaf (-83333333333333333333333333333500000000000000000000000000000)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (69444444444444444444444444443972222222222222222222222222220))
  (.leaf (-43981481481481481481481481481324074074074074074074074074074))))
  (.branch (.branch (.leaf (0))
  (.leaf (-25793650793650793650793650793507936507936507936507936507936)))
  (.branch (.leaf (35714285714285714285714285713845238095238095238095238095236))
  (.leaf (35714285714285714285714285713845238095238095238095238095236))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (-21384479717813051146384479717563932980599647266313932980600)))
  (.branch (.leaf (0))
  (.leaf (-13690476190476190476190476190500000000000000000000000000000))))
  (.branch (.branch (.leaf (0))
  (.leaf (18452380952380952380952380952500000000000000000000000000000)))
  (.branch (.leaf (19681437389770723104056437389282253086419753086419753086418))
  (.leaf (-12161044973544973544973544973305423280423280423280423280424)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (14318783068783068783068783068542129629629629629629629629628))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (-8538359788359788359788359788247949735449735449735449735450)))
  (.branch (.leaf (-14991181657848324514991181656957231040564373897707231040560))
  (.leaf (-5053323412698412698412698412750000000000000000000000000000)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (8866567460317460317460317460233134920634920634920634920634)))
  (.branch (.leaf (8928571428571428571428571428379629629629629629629629629628))
  (.leaf (9348820546737213403880070546642085537918871252204585537918))))
  (.branch (.branch (.leaf (0))
  (.leaf (-5778334725703146755778334725533973823447507658033973823448)))
  (.branch (.leaf (7667780562517404622667780562259955444165970481759955444164))
  (.leaf (8377280005569479253689780005540124617098301308827624617098)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (-5618875230404052459190303801685908554454920369707337125884)))
  (.branch (.leaf (-8680011661097187412976886660611145920356446672236145920352))
  (.leaf (-3807735880104301156932735880090670805802384749753170805802))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (5361678607292642380361678606990185902466604220990185902464))
  (.leaf (-3122158563496282794528408563450045462984059475287545462984))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (4736127460908162662548627460669110064724099811819110064720))))
  (.branch (.branch (.leaf (0))
  (.leaf (-2518050410350605282379161521373939032954627496537827921844)))
  (.branch (.leaf (0))
  (.leaf (4074751799532501286887251799322549218163253250972549218160)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (4054181381484013062960431381500000000000000000000000000000)))
  (.branch (.leaf (4124733832336171517458067165625419328343304951492085995010))
  (.leaf (-2898961418698260803523961418550708209918736234525708209920))))
  (.branch (.branch (.leaf (0))
  (.leaf (-2267812125621972820614586319088720334560742031030655818432)))
  (.branch (.leaf (3140291462438816711595432591299021346403915730457892314144))
  (.leaf (0))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (3403876813711885261727609532401199502970058390868480608960)))
  (.branch (.leaf (-4344960622225525074044221374652478075733121950816725387560))
  (.leaf (-2045591993035316714533732410454223499349835113342553670128))))
  (.branch (.branch (.leaf (0))
  (.leaf (2969638710597339379922022486497443122521770279684990560852)))
  (.branch (.leaf (-4155868781785645418478291298914579953521274248772944912408))
  (.leaf (-1619901878680050390160580246674104057542254552807500641984)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (-1200745371448457436672756756603020324533607266055083891896)))
  (.branch (.leaf (2210753043628638688394339381279564436786714492363814911168))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (2418226748823535500854985524782733488075293727945280926404)))
  (.branch (.leaf (-3228867997511023482023087297948114352921199259055284317680))
  (.leaf (-1103757019223163235946617550525000000000000000000000000000))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (1927354356973629696867265805305220749725116270829066417024))
  (.leaf (-942542588224630141566695475106343941020290337606398156256))))
  (.branch (.branch (.leaf (0))
  (.leaf (1749647566659525187512877589821380238503903665120009797854)))
  (.branch (.leaf (1783266223660377926498636242473188529149113722501651527250))
  (.leaf (2036593584404347079536000605201869589957159450151893309122)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (-1174452821533838434090328849321588805117994948992430044840)))
  (.branch (.leaf (0))
  (.leaf (1852557751997854864128708131381436303872137288695762679584))))
  (.branch (.branch (.leaf (0))
  (.leaf (1853502913950503958493571996015625000000000000000000000000)))
  (.branch (.leaf (1802290625256100000043983975856875622205831822219407247760))
  (.leaf (2010827490929920271775859511702900233696136522462298952862)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (-1505267654372669893309388496149891997095645108330657932504)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (-1246157518266818893091573341003331244297996273928961994704)))
  (.branch (.leaf (-2120321170068733685766992203794969654203985552069022393578))
  (.leaf (-944624658333666979570162575058368859820499474663347343150)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (-2096555387444642127839685300584570455203542903818260140754)))
  (.branch (.leaf (1246317560332830340726601161199671009545248651694223068720))
  (.leaf (-749437107237140254182825471516052798034397109919917923834))))
  (.branch (.branch (.leaf (0))
  (.leaf (-567460809664478444847514840015981191760824882787975788720)))
  (.branch (.leaf (-1686621532086688296314195343668767619784358539849417581378))
  (.leaf (1107659793369858380582534420600162404803276432063770428656))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (-422258827709274501043363593885256136780992396845505431744)))
  (.branch (.leaf (-1563563116230660328095567046616496568069761014171375939168))
  (.leaf (894269886395495953599519492956655616159577147858519641336))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (950012935258257212732268175993887595363063167615662071280))
  (.leaf (1064206688276742279290289628140224105283621827458754797128)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (988257787194467129599077114853340327143505036054245890980))
  (.leaf (1173335228879843443269266343210620831065975733916481239744))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (-654739471422616852902719371546875000000000000000000000000)))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (1023024528459160542430646273875411740629153609162714209268)))
  (.branch (.leaf (-1454665161884042645175621286184679207417199048486538015456))
  (.leaf (-542490763403207456817993999824538802447558042196988478800))))
  (.branch (.branch (.leaf (0))
  (.leaf (905313267253533597762290937362500000000000000000000000000)))
  (.branch (.leaf (911576135905918253292437161469935899945660016671343403174))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (-570733240480693360617506157163742379742640911058476160352)))
  (.branch (.leaf (-1237412388922027119165180610018027829331212486595650663176))
  (.leaf (-409457065133591668026213971222293723612540428408282894876))))
  (.branch (.branch (.leaf (0))
  (.leaf (770648411746153133652007614106928501648246199446271512694)))
  (.branch (.leaf (768359923863271868812675885312169717021261692508142746250))
  (.leaf (859488660350051509699345605897373678118549084331622833600))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (934648264063340256789348079850979618038110418765509636450)))
  (.branch (.leaf (847886782971121571107221231950081725352279429081036267056))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (-631593885225309990782233664203507278144135667588443300240)))
  (.branch (.leaf (0))
  (.leaf (-535564141121468192657906028307829158126120772511999277344)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (-1080558006807228337699732477910010954231004053053883788076))
  (.leaf (739968296430621151453358748785975362361773579640318373408))))
  (.branch (.branch (.leaf (0))
  (.leaf (-453924537568628368627000277156334661145260816562145329022)))
  (.branch (.leaf (656129373087299683359027978878352633639365383995888856696))
  (.leaf (735269982516644061044734725844447726822180852142360521716)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (801750977667086670619299855625771270762639786413698142570)))
  (.branch (.leaf (0))
  (.leaf (-530921392359763876094759103129287698566901474486201090716))))
  (.branch (.branch (.leaf (0))
  (.leaf (-1066378546641907750524425613640085106348251237299770094056)))
  (.branch (.leaf (622289416193403582604507019912554429744574551665692503104))
  (.leaf (-451595535046697949689944078530621695280820855029367388496)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (-907569082148726661315034625801748559526996147310339524304))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (-332129014235117880918580481507016983633959476275958043800)))
  (.branch (.leaf (-825849384823126792098997971602095505582857831545613901220))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (553897411619096290432469121903043080807611260197471607148)))
  (.branch (.leaf (519125740179423428501379411642106850106650289325478652510))
  (.leaf (-313785448825180433745631062590843677339704178847659115960))))
  (.branch (.branch (.leaf (0))
  (.leaf (-249287196029787730566497143724318325218006781535135010028)))
  (.branch (.leaf (-738167098835237160389085227726566829484068631258908069232))
  (.leaf (449892892198997031819764578598506653256083707884993339936)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (508125753023034160208493399441164162332841603220340632960)))
  (.branch (.leaf (-730482718850371683125231393984871423974304849119940763092))
  (.leaf (533998085538051884601400045612561445552010128879394778972))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (-775474088665784794349529933521756144062469146471020507442))
  (.leaf (-227920281562465924556351653370829768646668847495060160850))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (-171876429862509231176045622566656634094920227142454542048)))
  (.branch (.leaf (413671867302982707647566554128517922704075358764540069624))
  (.leaf (-751358825558274447459685785344770178021413292505437252592))))
  (.branch (.branch (.leaf (0))
  (.leaf (-120631763529624993430982629189957025667239520858921939100)))
  (.branch (.leaf (0))
  (.leaf (-68920395389278238446167752410000000000000000000000000000)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (323997439547898507774086884688638486352161438409943253304)))
  (.branch (.leaf (333721434582043236615784364030741004852975606165881031640))
  (.leaf (353895303036038743678684767160043418180900467678077103912))))
  (.branch (.branch (.leaf (0))
  (.leaf (420686631299640522733978184457203039723807133529152380320)))
  (.branch (.leaf (378242071620066759788930487786152368417248611659724831770))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (431034598925334632974574063031034464171946458724068149904)))
  (.branch (.leaf (938189617771753180482229542155233642240385574226915087076))
  (.leaf (-246031232086781944487538172632652309607140000941844852200))))
  (.branch (.branch (.leaf (0))
  (.leaf (399838178472188824168984807599410356577779915253184972312)))
  (.branch (.leaf (380071268971718985138843901730098745209532609156853111492))
  (.leaf (467947222029127249989375322558102911155909144669131591808)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (458926409305007835951727263085937500000000000000000000000)))
  (.branch (.leaf (418771661775436940127952973897516773216395699926598642000))
  (.leaf (480657425817656610574244348716436638578692729885954903208))))
  (.branch (.branch (.leaf (0))
  (.leaf (562728985616900526642469138622715503650677096453612133856)))
  (.branch (.leaf (-612298161886782039998837731241514672025210861720776139584))
  (.leaf (-391062974581302413659342075287471969626796645525802107180)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (419068371689742924370909988663238103744020195530320240256))
  (.leaf (-370690737254449917079438625669258248956066082499898384096))))
  (.branch (.branch (.leaf (0))
  (.leaf (-329328514215013815588435116623459225401202413643706040188)))
  (.branch (.leaf (-568441554223317595743706867980464128468947761853770737956))
  (.leaf (-599620691202610262044149367627747103052131772916697761848)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (-244495483472552013436394206424140985941691853867496936630)))
  (.branch (.leaf (0))
  (.leaf (388321692840219899084169960801536300547114815347502011396))))
  (.branch (.branch (.leaf (0))
  (.leaf (381498002138492509813174601531250000000000000000000000000)))
  (.branch (.leaf (-521260555341234405668314063566516284519885489204753449560))
  (.leaf (-238457289168264328959933544045180167066411040699743966280))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (-202051306062190519078721972092303809312893786814133370304)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (-457210989498501207157727780391373417307016557662540342688))
  (.leaf (301718427165496783755353918363793788740140385949357529792)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (319051015656677482177682409003390258807496450664437849632)))
  (.branch (.leaf (0))
  (.leaf (-197456100730622528687606646527045349235779840703675714304))))
  (.branch (.branch (.leaf (0))
  (.leaf (338175414564926693789192558804745662356733580486380565124)))
  (.branch (.leaf (309581829412295064328665818899913718337119130198528217008))
  (.leaf (-504036773053449275102127393646653129959259929238125231448))))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (-191261928665725150656932229175843147811961958331050155520)))
  (.branch (.leaf (-429980004867027142837753960468548099404136355334292217320))
  (.leaf (298056613222351746931525769770398060964295803985856034944))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (284351811616494331283587766244292091565623294144368496100))
  (.leaf (-187254595614804091273948245547466024726456359915353097932)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (311072041538492543144828595843141834688774060643796651168)))
  (.branch (.leaf (-421132391503587345627663512370118817359426024699573838010))
  (.leaf (301853165949697203522323538709925557978529227458193853582))))
  (.branch (.branch (.leaf (0))
  (.leaf (-183041422450416417532623361654111018623309769557690450168)))
  (.branch (.leaf (0))
  (.leaf (-154462414169871416641179780308639765300714986591905405750))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (-432665461737444227180412465628559410448803569460453602198)))
  (.branch (.leaf (233991688549787726681129266309558340937061632915421784960))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (-125998085028218913924794891987172902842537808117424159440)))
  (.branch (.leaf (213026845518622504763290126676694023697312902856588711200))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (-115585559558273309266897009495769240137828780459147724220)))
  (.branch (.leaf (-347225893129003758922949373877083098395299314984486795626))
  (.leaf (-77572911942431575010913633984364034718897847373021163940))))
  (.branch (.branch (.leaf (0))
  (.leaf (-372126768197104941947049575469626383755129875955138734582)))
  (.branch (.leaf (-336900400498240562952568031680819326749064984923416598352))
  (.leaf (178684951393572381683649942137373686920335177096055927512)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (-343251812311713201220884193871733795966241557068022900376))
  (.leaf (202147876861707953289972451391877202772165387489787615756))))
  (.branch (.branch (.leaf (0))
  (.leaf (-48313778573493030981557295689471475479793154227244693792)))
  (.branch (.leaf (0))
  (.leaf (184677046088185493296528299320512649317530284099194298398)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (177833403626476562446071626742216659637352343755392837324))
  (.leaf (188986349434688020364630549362904873636179966696663644840))))
  (.branch (.branch (.leaf (0))
  (.leaf (198479090691215920127325542839895781887901814650164917180)))
  (.branch (.leaf (200622351249171840415989018798563678291982826774780211568))
  (.leaf (240014372391666256130880675555344995338176585538255371610))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (245705046218144242007747851689267103187951870302346730540)))
  (.branch (.leaf (0))
  (.leaf (-141883112756450142139539965824225974983360709880769585064))))
  (.branch (.branch (.leaf (0))
  (.leaf (232108939721132364367502080490413037833546023127254652254)))
  (.branch (.leaf (-340106731670569951962396346328927613617527967518851078278))
  (.leaf (-123531930515866140200545747033520261240903815930439708580)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (-102330273600935749955923619923691627922563420698377053610)))
  (.branch (.leaf (183115891990619826787687579426175825086574947883378185692))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (-94282039125163178425126407338813208305862048789418213678)))
  (.branch (.leaf (-285887495429147012138252204464182416423755066542150038808))
  (.leaf (191121421764906013351691441752041557461381871817081951850))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (192861658319232133045235369010816399975333992871780853788)))
  (.branch (.leaf (-294820269348014902843604289609603724983949268440231547686))
  (.leaf (188748430387285006101054561469372661713782420513926944996))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (194685486730309260324439399199436235417799375297005286854))
  (.leaf (202818507923896729712934536948734441100716682855497311792)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (220113232196686620875304161730109345890981558389255467916)))
  (.branch (.leaf (457975066071919344461145887188329813779721427786713684690))
  (.leaf (-147614826431152283860057046169033208780068954852455805060))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (196874188329564005475371007527082591629447586189258795200))
  (.leaf (231926489154792474903798230140942935977834577615171789660))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (-153414913438367110387587208687703336619377440848220878800)))
  (.branch (.leaf (0))
  (.leaf (199456424857667164053967411934603209861740880447914506688))))
  (.branch (.branch (.leaf (0))
  (.leaf (233205442204372632661068135565299406795680606038766557280)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (-312375887942663024209112260372369054282780677561727926446)))
  (.branch (.leaf (199082296803244255319395319420704797139598946115570046600))
  (.leaf (-160605099502205056051668957380491214187710528877591724950))))
  (.branch (.branch (.leaf (0))
  (.leaf (-143266994828530715173081423775693793115716321384203071668)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (-125506108688418180861198340677850308701954214289210982910)))
  (.branch (.leaf (-249369486157006877738740457482070195526182264913872773776))
  (.leaf (188807473037724984912793985952058288009239323829215035440))))
  (.branch (.branch (.leaf (0))
  (.leaf (-284344504208263812036526394863746396175115560474106755172)))
  (.branch (.leaf (162192768353809600255575849069835771001692028326879553838))
  (.leaf (-113507717485858543258018920745995616881737385665532479960)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (150011793467768326890720334870984680677743566344030540322))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (179258885424355787385367384515959040868508187848874888968)))
  (.branch (.leaf (-244930848473055483406470914458301082857651991527908574040))
  (.leaf (-110833040390899279449257394239245231452541182412522601598))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (-237190940951792381387683255525755452293705170632123944160))
  (.leaf (167099503694090461795280988246736530255235713003616647672))))
  (.branch (.branch (.leaf (0))
  (.leaf (-99084035498924539545773611279849545946978395717173305856)))
  (.branch (.leaf (-240958147081225957700505736584935818647161549309175067112))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (156570617444921532727761418918324133974412339289847813360)))
  (.branch (.leaf (0))
  (.leaf (-87856107111916893176409098261384355530647424428986936768))))
  (.branch (.branch (.leaf (0))
  (.leaf (156020314747858851714475868359375000000000000000000000000)))
  (.branch (.leaf (144254947431902578755158746126184350031024901626336506914))
  (.leaf (-92449570390660936260402400163832909979990800317336985552)))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (-251511738071842826709922375320708804318957614646120523534)))
  (.branch (.leaf (127668223108366197694630564811103277320876302793966673936))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (-77580783567427517797301428668691640452174694159902814648)))
  (.branch (.leaf (330124919999159619815561640524506925754974419252438975640))
  (.leaf (151709151326723411547984733664190971325585951727701966324)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (146394435360183375918414148158448966121955106150527188538)))
  (.branch (.leaf (130275994762402446892490789419090211473261983283950202654))
  (.leaf (163709647302021734274499630619639789765009855849413392430))))
  (.branch (.branch (.leaf (0))
  (.leaf (-108200014820093062917725270049697906085319322045118199916)))
  (.branch (.leaf (127374119710638192655195409622383685449078056271255169464))
  (.leaf (-242803780489602665728742990368750000000000000000000000000))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (-95141327372113604121890674419079919044418938422189049640)))
  (.branch (.leaf (-193860196895727981894407457141133988457307775907628061552))
  (.leaf (134952244773928970474127233857434484905897117318227285604))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (-205082153723754182605307140254858532727908434243714541264))
  (.leaf (154564040922113700006017758266423690854668933725930652944)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (-89983369956370711311966040927681762872240397790182320942)))
  (.branch (.leaf (-199366040000706015064170139238611941131450835295403212700))
  (.leaf (138175294024475345357448318399102752076176792340840106066))))
  (.branch (.branch (.leaf (0))
  (.leaf (158880848083194534397280509145412397640022207829768451866)))
  (.branch (.leaf (0))
  (.leaf (148464248084582544155869957875418923043221637808944957616)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (150481529841871926492980778057664530920394086545664831610)))
  (.branch (.leaf (-220104042158341722015702559525800079685327964576617028480))
  (.leaf (-99812833548785883995037446174360580866199932116270735800))))
  (.branch (.branch (.leaf (0))
  (.leaf (-88055652437405946381881096308346419692748612352823198100)))
  (.branch (.leaf (121947811188449006364989029403023503708659369021790581040))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (-184530261712612318102158819418841644173456760324336391838))
  (.leaf (145150981695987460770568928309871297617986465771470826552))))
  (.branch (.branch (.leaf (0))
  (.leaf (-219141139794774070283486922247879728957896364263761598880)))
  (.branch (.leaf (-192277806016593598226678953472812026397587757097749057212))
  (.leaf (-73566674009266067945233627923178604822812418157351837036))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (-62560307701320994752791008387283511907287138351264832058)))
  (.branch (.leaf (-175558420808814875973033938314432044272943391750903311780))
  (.leaf (-191521379810767724136011576527426316921108656552952590944))))
  (.branch (.branch (.leaf (0))
  (.leaf (100339413112577954636515578917279027235320860591490840704)))
  (.branch (.leaf (-177668379126969602755707586151272312708950575662531921520))
  (.leaf (-43353064957881149217761154922490655577114395886680066784)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (-176026594659576659978935991294196788413254637026144251068))
  (.leaf (-26766647275924582654558448159164297667258608904851615968))))
  (.branch (.branch (.leaf (0))
  (.leaf (84666265306390697178143487512905369810912131149905847578)))
  (.branch (.leaf (96598502456440540226434073776555791080883043520746314516))
  (.leaf (105527307658658843305601976464455743603203129344425876064))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (-38651365331630052048072608862801530133503661461859405780)))
  (.branch (.leaf (0))
  (.leaf (101126801318210051109042594156226297414047255141719686672))))
  (.branch (.branch (.leaf (0))
  (.leaf (103163215550456158573631638746687027888981332167077048804)))
  (.branch (.leaf (103661065187238890976832854551845223991759401035962229472))
  (.leaf (-195369580492918782680119422085710632562738912194186642700)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (-44004767989629327203916470145445626925340526304851203320)))
  (.branch (.leaf (92007084397330912172907477902189262830958576988777856352))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (-40445719127302331625441063142131744677617374214412824864)))
  (.branch (.leaf (249975151233327271143327633388627014321781657579381425640))
  (.leaf (-34683252195949265770982495583599834050697487555289497144))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (-161324544398962878674761851346721749967198836392594299378)))
  (.branch (.leaf (74206166358969558920291885481001936564149837767179763424))
  (.leaf (-25699829858270159737962585469586138522367536250869648544))))
  (.branch (.branch (.leaf (0))
  (.leaf (83386279919596453995750982965311307553447875137767591072)))
  (.branch (.leaf (-148540280846458253212600932987065672993898546721016323422))
  (.leaf (82543439268046530617701700463406525504666436990187520800)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (83378624232287108409545676155613899350482563925835041576)))
  (.branch (.leaf (-143194144683196412713542660216689080736087629196666030736))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (80881188381884085603734533670458261657816407435832120640))
  (.leaf (-34921983474864977780945323952745815977354936888382081500)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (83807484707987211607475160332982185640342953795467454400)))
  (.branch (.leaf (79556910387210053044557974132281290942151662604198527502))
  (.leaf (-158282863372099497016552862602708753643409195430429133830))))
  (.branch (.branch (.leaf (0))
  (.leaf (99118103575135637144094680028025008133833838305019013820)))
  (.branch (.leaf (0))
  (.leaf (-40793644901023079994692680557270863097629967288170802156)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (91577630446901177906048848159601252187390021738667687820)))
  (.branch (.leaf (0))
  (.leaf (-38328696227167553187312457389556184757262117713716344714))))
  (.branch (.branch (.leaf (0))
  (.leaf (88938527550901696722409639992421610659918552841024898918)))
  (.branch (.leaf (-142705614910542930709987937952441563559592351525528634320))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (90462817988313794102295293768515935204303472733008656754)))
  (.branch (.leaf (-137381877378351590274091312332477401117626768063727997280))
  (.leaf (-35207048908412985899355850384000000000000000000000000000))))
  (.branch (.branch (.leaf (0))
  (.leaf (84242983784864794632035081351751306180625796000692611936)))
  (.branch (.leaf (78392925302953930207218522354943717898821638541770778748))
  (.leaf (-38145272968054790957935750616606321577663540997739731008)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (87087652088406529611221637586726568526357282819969052580)))
  (.branch (.leaf (-134019344248975205974568028425047413046582949719174276200))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (-31784554213803886080027323814629736584840794250533525800)))
  (.branch (.leaf (209262247911716458790186156259673022068409139839187806304))
  (.leaf (77872373937191265981773765312224240064980524155987284230)))))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))))))

private def fast512b : ℕ→ℤ := densityTreeValue 10 fast512bTree

private def fast512GTree : DensityIntTree := .branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (1000000000000000000000000000000000000000000000000000000000000)))
  (.branch (.leaf (833333333333333333333333333334000000000000000000000000000000))
  (.leaf (833333333333333333333333333333833333333333333333333333333334))))
  (.branch (.branch (.leaf (750000000000000000000000000000833333333333333333333333333334))
  (.leaf (811111111111111111111111111112388888888888888888888888888890)))
  (.branch (.leaf (727777777777777777777777777778916666666666666666666666666667))
  (.leaf (787301587301587301587301587302559523809523809523809523809525)))))
  (.branch (.branch (.branch (.leaf (745634920634920634920634920636059523809523809523809523809525))
  (.leaf (745634920634920634920634920636003968253968253968253968253971)))
  (.branch (.leaf (712301587301587301587301587302553968253968253968253968253969))
  (.leaf (759229196729196729196729196730320803270803270803270803270805))))
  (.branch (.branch (.leaf (717562530062530062530062530063584692159692159692159692159694))
  (.leaf (768691956191956191956191956193153678728678728678728678728682)))
  (.branch (.leaf (738930051430051430051430051430820345395345395345395345395347))
  (.leaf (728348040848040848040848040848484102009102009102009102009102))))))
  (.branch (.branch (.branch (.branch (.leaf (707514707514707514707514707515234102009102009102009102009102))
  (.leaf (744953757208659169443483168974140757263796479482753992557914)))
  (.branch (.leaf (717175979430881391665705391196316683189722405408679918483841))
  (.leaf (756117082187773622242146493953185104242353984356048339536473))))
  (.branch (.branch (.leaf (739450415521106955575479827286460104242353984356048339536472))
  (.leaf (730125018695710130178654430461102961385211127213191196679331)))
  (.branch (.leaf (712664200193224961026818611958268631980048388717119367274167))
  (.leaf (743981416089245204873149414811050165221364238728621552689396)))))
  (.branch (.branch (.branch (.leaf (723148082755911871539816081477682109665808683173065997133841))
  (.leaf (735370304978134093762038303699993220776919794284177108244953)))
  (.branch (.leaf (723971749829578945206889748551319843691042708407091231159075))
  (.leaf (723971749829578945206889748551301325172524189888572712640558))))
  (.branch (.branch (.leaf (709090797448626564254508796170134658505857523221906045973891))
  (.leaf (735035196280956431067134229485334984632476753289411975548786)))
  (.branch (.leaf (721234490813584297028333524018522594861753649232974585778066))
  (.leaf (748439231917014916587985341734804852926269778265232650294196)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (738022565250348249921318675068179852926269778265232650294196))
  (.leaf (732228638883505216411618498701289811640395159057280109008322)))
  (.branch (.leaf (720661048884542668429462673408181592426783788583164536853533))
  (.leaf (722073361494771945325406236018345900186924882057591344613674))))
  (.branch (.branch (.leaf (708184472605883056436517347129433863149887845020554307576638))
  (.leaf (729433164907206936707766039430926916353467364389547360780218)))
  (.branch (.leaf (721483777549924842583566652073410556008159650660781000434909))
  (.leaf (721263173957610723953658548481101881276458603170259825703210)))))
  (.branch (.branch (.branch (.leaf (712929840624277390620325215147739381276458603170259825703210))
  (.leaf (731701209296312362551378813785077862965906121824942732479766)))
  (.branch (.leaf (718358499222516762439989228711633383712216341819373253226082))
  (.leaf (737806577295900833376079748645496201278506980325434035908653))))
  (.branch (.branch (.leaf (729076168044658248800161839394079036575925611077398121206072))
  (.leaf (725548831183988054796634502533300288780511148996269373410659)))
  (.branch (.leaf (717583610492914007505958684015985589129722634744749782455521))
  (.leaf (735738047674098575775260062686578096858227936971589896567006))))))
  (.branch (.branch (.branch (.branch (.leaf (725321381007431909108593396019894069080450159193812118789229))
  (.leaf (733824782367976126795668225951843048672286893887689669809638)))
  (.branch (.leaf (727158115701309460129001559285153048672286893887689669809638))
  (.leaf (724766083256279939076088693506624377155242483826423743390630))))
  (.branch (.branch (.leaf (719066805682002364798514415932287688612303940887880804847691))
  (.leaf (735416679799953646308588084599592994862368181315871278812640)))
  (.branch (.leaf (726157420540694387049328825340318303504343489957846587454618))
  (.leaf (726991431599486147595475336398971997503651524353600281453924)))))
  (.branch (.branch (.branch (.leaf (719550955409009957119284860208388664170318191020266948120591))
  (.leaf (719041644727001906690181799526379892240493629616758176190767)))
  (.branch (.leaf (713150072228376574832343387947329612563181032360623916628398))
  (.leaf (727200263352051195384751629918609412827838567312538886384580))))
  (.branch (.branch (.leaf (720299910618365128365351277185203217942477015284320191499220))
  (.leaf (734425541115693975216867838407098104165293322433617404533248)))
  (.branch (.leaf (729662826785762080202912835770538254543955302680204329105457))
  (.leaf (726554361177296471737304370162085873591574350299251948153079))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (721346027843963138403971036828773373591574350299251948153079))
  (.leaf (724292029199799565790240770903361874681845995991707730349342)))
  (.branch (.leaf (716034826948318522571789516232595834062689219506125359085025))
  (.leaf (728914608089611564066211007702738625488712518721141014370121))))
  (.branch (.branch (.leaf (723130813090130290075133095056184515881906833484083228292727))
  (.leaf (722046770142879304940063935884906238200809249419776193702135)))
  (.branch (.leaf (716612930682081313842573298906810320063866458416153160606306))
  (.leaf (729077535845654784579173282040417906147169274285880871231928)))))
  (.branch (.branch (.branch (.leaf (722133091401210340134728837595961887628650755767362352713410))
  (.leaf (734630976166748184067919094537989004290418518364320967451651)))
  (.branch (.leaf (729448057343020744873919762052015095328994992541181308964609))
  (.leaf (727331655226618628471803359935547846651746315292504060287362))))
  (.branch (.branch (.leaf (723356961547977581409703666256789666479092458428120880114708))
  (.leaf (724903374924987745097186838409766363411131196119510124485077)))
  (.branch (.leaf (719926876410657608304822370594917271141552255641310112250741))
  (.leaf (731481347239535710891660563170974549622564913869158213516564))))))
  (.branch (.branch (.branch (.branch (.leaf (727314680572869044224993896504293299622564913869158213516565))
  (.leaf (727314680572869044224993896504287126783058741029652040677060)))
  (.branch (.leaf (722367556664234143627225360002261588377507616627822560482362))
  (.leaf (733473206847093850835056254888601027569017446772143873169480))))
  (.branch (.branch (.leaf (726801851810196050779361462351878787942172556769359133542639))
  (.leaf (727869374675123031097074568181220061323118622484484330600583)))
  (.branch (.leaf (723872803966483196429602960514671170263320032204202419980747))
  (.leaf (723063277621434280722542841190451309481690498228580427745869)))))
  (.branch (.branch (.branch (.leaf (718698072995812988434583886564742727130399813604562470394579))
  (.leaf (728759575230458925281392434119915520347753728767929590911537)))
  (.branch (.leaf (724159340074668213935125532297644723757512694082450460987967))
  (.leaf (726905845149184819889433902037266784516295000567029705265321))))
  (.branch (.branch (.leaf (722923234803647796244095992778609434690900743441269909787753))
  (.leaf (723092296580032162636451998637036350013481388602560232368400)))
  (.branch (.leaf (719787408632759979395260147125508628436110084304157143480414))
  (.leaf (722276515154600509525014285668140768435888092171648682199359)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (717068181821267176191680952334798754546999203282759793310471))
  (.leaf (725872192517409970215897337034525151209697372607418826099617)))
  (.branch (.leaf (721620491837137861372359922068477532162078324988371207051999))
  (.leaf (719689183048190183535793196612847518400120118585720359956709))))
  (.branch (.branch (.leaf (716355849714856850202459863279502518400120118585720359956709))
  (.leaf (725010682295599932299467299839489286165723112410801298952105)))
  (.branch (.leaf (719768574594893188787523986791180706969409412750394157212494))
  (.leaf (728532687800637191710866445575345639080462699683497800160607)))))
  (.branch (.branch (.branch (.leaf (725683049013498404572079306788177294808993428214226330889138))
  (.leaf (723325971979123385355132373650120622858870930073992516872515)))
  (.branch (.leaf (720168610246230598589260589019199362087787921581191410885975))
  (.leaf (728764967531516822821059071958898262560781561854449063055599))))
  (.branch (.branch (.leaf (724135337901887193191429442329260916881769216175436717376589))
  (.leaf (732742189018828219333737890791997229267990042668795530578695)))
  (.branch (.leaf (729600779686010747850500157647400143103527490327945294452638))
  (.leaf (728782327904146223979156580492817809729343759702826569102309))))))
  (.branch (.branch (.branch (.branch (.leaf (725062089808908128741061342397526143062677093036159902435643))
  (.leaf (733489388503322748045327713316915223209081941347278998773811)))
  (.branch (.leaf (729841131987979828955850577871097366759827737745156262953459))
  (.leaf (730960197710584204596590654069895353178839856875991548180258))))
  (.branch (.branch (.leaf (728014411461271538667671448280370213340183558247924418399075))
  (.leaf (727940876930500165791035413749600655096283209084417360155177)))
  (.branch (.leaf (724616550399347145709350333984692069942619107524600676596074))
  (.leaf (726127231973874684603582896818436606143111183103930550211100)))))
  (.branch (.branch (.branch (.leaf (722677055607031651093882720451733508700430407089821202768422))
  (.leaf (726943201918632508149285230399712311883779044983913642315408)))
  (.branch (.leaf (724065313205857518923221823098201619912494638020846002920124))
  (.leaf (723365690024602678213427654840846206184758567127461664467502))))
  (.branch (.branch (.leaf (720984332859636730706450153522566281374089557250755126753607))
  (.leaf (723428777304081175150894597967028503596311779472977348975830)))
  (.branch (.leaf (718981207279482641780431402942547010511748519471120855891272))
  (.leaf (726200483556091520990520809555252104015685527345136603922769)))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (723596316889424854323854142888595854015685527345136603922769))
  (.leaf (723350096124515914480640543869103832852054971309032757320802)))
  (.branch (.leaf (721317658339776784755299016319365847209716615049794053423422))
  (.leaf (728408755362633119283213846747022224437803408152635232883554))))
  (.branch (.branch (.leaf (724280154236892597673988219411639204128225019909844047251397))
  (.leaf (726362517271421462456856131544836290594390433443678633717564)))
  (.branch (.leaf (723763735221754995984722498520989562505855205754424968942391))
  (.leaf (722587956268198264650213386234063313240717051727382053010588)))))
  (.branch (.branch (.branch (.leaf (719696058768457627654674429910786258437314209108853159971892))
  (.leaf (726424595600969635023983931052892589050272298124801983081613)))
  (.branch (.leaf (722809199535055894681462701407389155845465702742518142791114))
  (.leaf (729593987074238849776026415493720818956385536414829284356670))))
  (.branch (.branch (.leaf (726877067343839854227281097004672859887914140913017767808756))
  (.leaf (726606996234420579762756968430959560469276920478857552535918)))
  (.branch (.leaf (724217987378568239582029260296230452805414378838623916792163))
  (.leaf (726342414803857056030493544667091686697393141783169399839626))))))
  (.branch (.branch (.branch (.branch (.leaf (722870192581634833808271322444863677438133882523910140580368))
  (.leaf (724204448581512806431417174812291120748928789147747717357851)))
  (.branch (.leaf (722168857655928649055877515382843801901055360834212170583070))
  (.leaf (720836658109443388284902458693507067207177809813804007317767))))
  (.branch (.branch (.leaf (718245198697579668687902792450520112726466046902234178074246))
  (.leaf (724325014208327513059536666168866941018791709892363855579376)))
  (.branch (.leaf (721564873114853086251776525075504463064647089081076377625234))
  (.leaf (727651825530023008787595440239249614038971299434392192917427)))))
  (.branch (.branch (.branch (.leaf (725664478690702485256545593399870523952644371002200602831100))
  (.leaf (724867134542359311572241304807027633446962900981778627358099)))
  (.branch (.leaf (721960161725626142837737108335645210577157550847371105373615))
  (.leaf (723660791504391633420834092276447494183246922993319667474622))))
  (.branch (.branch (.leaf (721172542247226565024651858369022948048457452754219661357456))
  (.leaf (727088044461250293343922947263841135680305822510905923671747)))
  (.branch (.leaf (725082590683375800438844531446368380719008479034142318857558))
  (.leaf (724978510529108909405762878998418370780757733739639994600295)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (722895177195775576072429545665077745780757733739639994600296))
  (.leaf (724547627752791310414677883609395909999037544645709284448149)))
  (.branch (.leaf (721461207999704890661591463856304346213029314193034387328809))
  (.leaf (727065255932498501018625539109003279373358118240020578876130))))
  (.branch (.branch (.leaf (724591693978181050719741270857990510170582556039105838778781))
  (.leaf (722762779796013741361943892942052395935576521173262206222736)))
  (.branch (.leaf (720905765789580773648865453830845513334569986700703012900725))
  (.leaf (726442194206629884082409042686446628166235273630104783236780)))))
  (.branch (.branch (.branch (.leaf (723106516688180984054561646418085508352812828628712413423361))
  (.leaf (727039549467367609395033140735744661165811795473833104697899)))
  (.branch (.leaf (724693286168756135731043379846217253000461535887789067406273))
  (.leaf (724523515941420118921342359618880995690520015419952810096333))))
  (.branch (.branch (.leaf (722525230587100201587606555785606550160620720279811854786416))
  (.leaf (727973448393674332261601270101787394448663061381570578823541)))
  (.branch (.leaf (725244183895381333524090418764661236297728530549876081761075))
  (.leaf (725526646417427188903279131286694097849756749244761443313105))))))
  (.branch (.branch (.branch (.branch (.leaf (723344044104616542759299653973839806674111406932752464637461))
  (.leaf (722931621043336218781890802622889788826189043967882044807405)))
  (.branch (.leaf (720990861196718760446530538209129528240028831614171982594799))
  (.leaf (726263667926664529733455298207991198529169574362698625154817))))
  (.branch (.branch (.leaf (723963550348769174060321847296855800234049057019959060193033))
  (.leaf (729239125031192425003788499324402200140875249133451549492398)))
  (.branch (.leaf (727340996329258493320698956254640118106736749698898217977798))
  (.leaf (727034951846250166078980525393539652408035427593160970853669)))))
  (.branch (.branch (.branch (.leaf (725043646673481654256311570764210977495338299030281073114885))
  (.leaf (726047757133015710717016048870209010556645302765558282646821)))
  (.branch (.leaf (723760397080159708445761921591782790289357607819422513873750))
  (.leaf (725110799168376272812797372698929299994348073465188798088632))))
  (.branch (.branch (.leaf (723458355194740181192201446943165439205662421315987253644640))
  (.leaf (722422199991918311703665291740347978888202103855669793327182)))
  (.branch (.leaf (721062262177261068220363814091161242897189318119413492332375))
  (.leaf (726069943989939439992142540971821826741108094298096442642730))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (723465777323272773325475874305150819796663649853651998198287))
  (.leaf (728475248043669331451812782050459810830962512009929232775410)))
  (.branch (.leaf (726418073025366735226551358823874207497386806051641845940638))
  (.leaf (725943218271915451472871921350178134767381096090548366504728))))
  (.branch (.branch (.leaf (723817367931779397051103213867154325243571572281024556980920))
  (.leaf (728772878300229467489144312456238479893031236313465127427607)))
  (.branch (.leaf (726020477549735786416327227565983133019978977484937670339504))
  (.leaf (730976682782487211695468999512065595331536766429661288429957)))))
  (.branch (.branch (.branch (.leaf (729310016115820545028802332845393095331536766429661288429957))
  (.leaf (728952149557690004631731842259927838422583261437255554589239)))
  (.branch (.leaf (727012627216636988256785338303298497963703080490615370465112))
  (.leaf (728199301991615060518852221261622627380268008898971634552631))))
  (.branch (.branch (.leaf (725578248141261688762880564737468337782111159068768063682827))
  (.leaf (726365674631629570284291387310650689734250215190686371944205)))
  (.branch (.leaf (724653481396736525237143132951043580002854301443655199803431))
  (.leaf (724292133747652863525453413227284154109155106755552854939901))))))
  (.branch (.branch (.branch (.branch (.leaf (722867314354083469956059843833699981973420471020917120304167))
  (.leaf (724523634388820556190259703332548888137043064298709060153523)))
  (.branch (.leaf (722327274490442502897297987086889198021383301029690406415538))
  (.leaf (726820579751246716213473956023261285048269052024009225070448))))
  (.branch (.branch (.leaf (725241898884800322830538063707800654662727547777608672077179))
  (.leaf (725101769770379161524653521766506349582284200588404896741601)))
  (.branch (.leaf (723549490086978416301704068197282160246233543988396183414541))
  (.leaf (724677078763477639392658317532462955869613989103011321672063)))))
  (.branch (.branch (.branch (.leaf (722362263948662824577843502717644283030107816263505148832559))
  (.leaf (724019409901161453948430589500869621451766802438620356205833)))
  (.branch (.leaf (722625399170337067568275457837639881574056914137519939430538))
  (.leaf (722705808139005238366625449934153028332768240061825889200832))))
  (.branch (.branch (.leaf (721135103472596502625006583361854485250536963891400771137805))
  (.leaf (723060485781651040314776411706295345390959728740334292614316)))
  (.branch (.leaf (720523627157789290316318312939268765090351136976421671682871))
  (.leaf (724616869115943413911627580729452145138661560061837573611566)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (722756750068324366292579961681806311805328226728504240278234))
  (.leaf (722051282696190327491874494309650562246245334312278490719153)))
  (.branch (.leaf (720784295400338117531505433415831349272749300787262164438228))
  (.leaf (724818891006696002416188109327607024944498080519740239622414))))
  (.branch (.branch (.leaf (722994762749024542871449541604698096719870978718678871712239))
  (.leaf (727032246461883764863721368496808261948618247920755689689519)))
  (.branch (.leaf (725317895712643385786642257671832316132853994578179434494249))
  (.leaf (723848883489926744331578172078961708060745305156731796338028)))))
  (.branch (.branch (.branch (.leaf (722375990365270411367118569184199138141417155842698231447438))
  (.leaf (726423340375360091113338827338290018614702931799989532794070)))
  (.branch (.leaf (724764507537250045515884004733340321191509951640589528715959))
  (.leaf (725828633924010394198852091090208349581493351487593469625304))))
  (.branch (.branch (.leaf (724166470658433884158009551207754057004661300707685127845753))
  (.leaf (724180049654164655589173853292441530633353283830047997044066)))
  (.branch (.leaf (722188239529944733647828703398800814973200195545385242337907))
  (.leaf (726133882659186511159872953955174044847974788688785916781669))))))
  (.branch (.branch (.branch (.branch (.leaf (724408794475764994405022865771822496126634400681731243060331))
  (.leaf (728356120763063799736566550438734341694914867890767732096667)))
  (.branch (.leaf (726768773626474238904581476029385766294445528027488474878017))
  (.leaf (726768773626474238904581476029383708681276803747653083931516))))
  (.branch (.branch (.leaf (725329829270086744291549772378628362695634600266119264233874))
  (.leaf (725531588214405212419541709894366120947083327905323093913896)))
  (.branch (.leaf (723334496761400582057255661383812060048607975904523872608568))
  (.leaf (725274124063317058855148924176932521146647004536729897447660)))))
  (.branch (.branch (.branch (.leaf (724083445480834085101660173517792558741312499598376628590713))
  (.leaf (724088315633749219203315624101758492987651385213614034123200)))
  (.branch (.leaf (722754982300415885869982290768420492987651385213614034123201))
  (.leaf (726541589944705183660019783723487073136423573500400398249535))))
  (.branch (.branch (.leaf (724317804932405916974788186211246326594141943499472151707258))
  (.leaf (725590761648599971384661616593447951504464881567902150650784)))
  (.branch (.leaf (724260637784295708678706901729204348982644520383140048946534))
  (.leaf (723238939167083025431374610734362838684488853021587590125497))))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (721936855833749692098041277401034713684488853021587590125497))
  (.leaf (725636644488741554496022477467578714894653544759754594444686)))
  (.branch (.leaf (723739991679849485732658864760357803035812000335212598686114))
  (.leaf (724821323512437282408945094320941880511959470720869276993386))))
  (.branch (.branch (.leaf (723805104620067717546274330546072887690790292591249925044698))
  (.leaf (723535262505051412310587624104666267430247114599375927633074)))
  (.branch (.leaf (722276104303923045916006744133089893174024073376238595782905))
  (.leaf (725891131077129534600398195127086153385039061883243394776228)))))
  (.branch (.branch (.branch (.leaf (723826830514259273795785381459394643230249867761847801960152))
  (.leaf (724787332306012760586437606262501781325433670201590741622341)))
  (.branch (.leaf (723369946574789876468063606816834384839696951739448354401670))
  (.leaf (723280315466894960860222487405768574803460119354695588427572))))
  (.branch (.branch (.leaf (721980924442061727624155670893845210759192505510068756039986))
  (.leaf (725515355138570419013314497346317493792613805405938574883499)))
  (.branch (.leaf (723981943419973515231225530072227228262533460510778864908979))
  (.leaf (727517517906172647504621250660922278534133114527876996403599))))))
  (.branch (.branch (.branch (.branch (.leaf (726071569156302329006851772499283751132431693218612549884253))
  (.leaf (725507569928990602115700528775500145528268690532452420785010)))
  (.branch (.leaf (724239649985134593040418403746687686693932971855824005949649))
  (.leaf (724406452196892945149647705958418425493794578734974744749512))))
  (.branch (.branch (.leaf (722598754163936074978387091135666708891391281043832824604264))
  (.leaf (726082864382156953537386483969311304941617335293477133296810)))
  (.branch (.leaf (724892121927722689081038345767455988794155859996518069769206))
  (.leaf (724948475853184144545157014386931627235016075050281510629423)))))
  (.branch (.branch (.branch (.leaf (723590015987984646770784355142407647700780377299375752355467))
  (.leaf (727033149289636337874328846033267750346763544960197743421283)))
  (.branch (.leaf (725378601738159659294506011428314914614063872513080989230220))
  (.leaf (728834597730810867295466829243093801462737200814117862059213))))
  (.branch (.branch (.leaf (727640093302884697205102975175729247630805929994001044187336))
  (.leaf (727279432303226977600703652042374469918656000735530553697417)))
  (.branch (.leaf (726158405227366090588261885808062396692692138685368007777593))
  (.leaf (726986193949561406927575724637992027345700795342749775126148)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (725250082838450295816464613526878022716071165713120145496520))
  (.leaf (727452379879270981389168640671519590672229663970811021411157)))
  (.branch (.leaf (726398137699265871944774748201754670060164785758105797968258))
  (.leaf (726098529691336689933628257821094865050846650198832445310981))))
  (.branch (.branch (.leaf (725080734228544611245858428106371205626909936042064671923591))
  (.leaf (728445389733247568726822263302149310943239016607973946001131)))
  (.branch (.leaf (726539288294133911568052322577371528192711905178606877536323))
  (.leaf (727179954600738565427951026577923518785733070513352719269951)))))
  (.branch (.branch (.branch (.leaf (725884224894806705629451193456430041545377189057567804648191))
  (.leaf (725240455298490813017262284971220036958057786923350855616429)))
  (.branch (.leaf (723983923526842442190581221868773251656475420426600617407661))
  (.leaf (725460463405678485699257862469301280576757386169517839881757))))
  (.branch (.branch (.leaf (724080392858941272295377791922620041599685075763874100904687))
  (.leaf (725119184321134753055766110900083197033900211650818663347949)))
  (.branch (.leaf (723948271842441292345107010039390097788758273164185126040052))
  (.leaf (723772900375410685636874032934609348870980616008248710911779))))))
  (.branch (.branch (.branch (.branch (.leaf (722779226955750423871349109514919803827817151792152915868617))
  (.leaf (723573191070468945862530843563636499905987308626012337264251)))
  (.branch (.leaf (721825821836900031358549739214200306840549408739209956684383))
  (.leaf (724941267714371594245726160160428198129409696237798242473912))))
  (.branch (.branch (.leaf (723487781306005009878474061924736986694507021170594481481671))
  (.leaf (723405015359614919916318176480206325322756387757183468249316)))
  (.branch (.leaf (722482349910173281537291458980950350949923110370737645143153))
  (.leaf (725574252063258701570724353748386284064887994336157687749686)))))
  (.branch (.branch (.branch (.leaf (724330127434676167372633236794674010997493259216607684691105))
  (.leaf (727422685339988969641846642248232747484586670236803876327591)))
  (.branch (.leaf (726317267837929882503004481493755915214769404585323379301003))
  (.leaf (725531575493138209430688837114403691231395238538578774628798))))
  (.branch (.branch (.leaf (724528848604200962978149629205667313750746566800196972221704))
  (.leaf (727589140697567913364393272514416828618150483931218279560077)))
  (.branch (.leaf (726094325267757773716585325290653212910835516669457213656636))
  (.leaf (727127425591846409639873823220951475919259728814449396369795))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (726085758925179742973207156554281163419259728814449396369796))
  (.leaf (726028808214419928354858116766118404587491509876600207697572)))
  (.branch (.leaf (724738175591909371356565091021908199384215159003737732517438))
  (.leaf (726092078193126781785154829165984114272956204571225848748287))))
  (.branch (.branch (.leaf (724548868316583571908611619289438332379952089344888400188618))
  (.leaf (725138068587750857385865566104356032598006418483379556627871)))
  (.branch (.leaf (724044798490775722335954486892690211487208251784010148485933))
  (.leaf (724058463395478126250718249816298756479067592588505127874269)))))
  (.branch (.branch (.branch (.leaf (722821682418319401101276115690792371877679811488047757825595))
  (.leaf (723862237031009526552922944059766699652870942604678610142265)))
  (.branch (.leaf (722513042423232731369401978318574619423082576150214921839975))
  (.leaf (725386575633055355520587238492949392860828186953670623134613))))
  (.branch (.branch (.leaf (724458068629838871664048018937345951560324919717391026473608))
  (.leaf (724185251369217363706933493219151840435597009509018118023500)))
  (.branch (.leaf (723158323798007610673691636698395648107729759242542992525651))
  (.leaf (723893238024542072807347063239155530755114575387871079783608))))))
  (.branch (.branch (.branch (.branch (.leaf (722225399265317622793423365104974970848403352887174894876899))
  (.leaf (725039343402324359540602543474922282348579227671845961831927)))
  (.branch (.leaf (724162531467820117344052654617332022572742528758223971286862))
  (.leaf (724221234950108026341092167497970065477423584857422499027217))))
  (.branch (.branch (.leaf (723048103300802289509097287053206361394748455064400480381405))
  (.leaf (724335709557992154546605598745693024980972831228167062731019)))
  (.branch (.leaf (723119624052877848183446553597087072831221430027459484124237))
  (.leaf (724334395675812736424457243587365498487198106412299134270010)))))
  (.branch (.branch (.branch (.leaf (723335252998652777757589341670728275722248458842228656615052))
  (.leaf (722644071066782593951309048541188575030484423897756061213853)))
  (.branch (.leaf (721713697719666737840350271153578314688408199175097814088265))
  (.leaf (724434937000567990997555086346053731255200315735557398155823))))
  (.branch (.branch (.leaf (723070304751421491628799660677490652179733050319710149624592))
  (.leaf (725792367269486943721649501889818110249081517379414771767824)))
  (.branch (.leaf (724705599377327345502151374494198926621692959178690165148661))
  (.leaf (724681087867070221209939362983942407207059509457521145734030)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (723589786710664898137949624327515261619236838301516656396209))
  (.leaf (726297141791778179673802307006667439639146782104224612552110)))
  (.branch (.leaf (724745802374869356431942213316554839058980062764913142267483))
  (.leaf (725471349346975453185458259015306661824995718157836569224607))))
  (.branch (.branch (.leaf (724500969423666724017778126808426531531915611980981538118305))
  (.leaf (723681088807063763914995535925360332533946339794017318123609)))
  (.branch (.leaf (722755290154543158344933231066229718533317285878171764767512))
  (.leaf (725427297757391561640115323566096536286909086096963056800087)))))
  (.branch (.branch (.branch (.leaf (724277238968443883803548598110528837139348827425593274319197))
  (.leaf (726326770692490843307571814045100859300013647370191612269337)))
  (.branch (.leaf (725431328574868211323507094279568248353993989755712826685862))
  (.leaf (724904607996064299186261623700760062782550842554989868387148))))
  (.branch (.branch (.leaf (723955543645097333344716852165879021765481592837713202629850))
  (.leaf (724731791964603382728481519036218973392889346086810725885037)))
  (.branch (.leaf (723297137918445084361404596101078674943135061132756501577804))
  (.leaf (725911100518381160558794575764060138158549004963967957177841))))))
  (.branch (.branch (.branch (.branch (.leaf (724915447931996904647460098449395800702200440682528008308450))
  (.leaf (724682240204911957744195375696943996126288417051399895490911)))
  (.branch (.leaf (723662528375726194604112072643937284206119670760993253409069))
  (.leaf (724592997137959596620356332354644077963473032465057503803756))))
  (.branch (.branch (.leaf (723449317111531595484729268715430967829829184991989619417221))
  (.leaf (726031198223485754055103066149727525790584619464905153886164)))
  (.branch (.leaf (724869798654772305324729055265638617485685744148395275940690))
  (.leaf (724446518231491882044305774842345167750236008698659826205242)))))
  (.branch (.branch (.branch (.leaf (723620296244673836234007811964463237355893182624059053983246))
  (.leaf (724883153614957234743143584274164602028511581883197890611114)))
  (.branch (.leaf (723400630273424390286322519266004104333657161882579059582930))
  (.leaf (725951296593753106638528695919721611798706989392187011960147))))
  (.branch (.branch (.leaf (725271327686424484896877957095128243803200596524058861462745))
  (.leaf (725209101510698138130958193172970681467242591274715029441748)))
  (.branch (.leaf (724366795968308668131379329670076372398918868140028390842060))
  (.leaf (726885312455359260458826499071479119123403629297935596937448)))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (725583229122025927125493165738143615651181407075713374715227))
  (.leaf (725269248432513638063475090452257183840033618299107254958246)))
  (.branch (.leaf (724447420582314238419329539311142471753674910135998388143542))
  (.leaf (724365346994011258471591672971311798032464724790630439276221))))
  (.branch (.branch (.leaf (723336759484859960358960961358018996365676871811486745858836))
  (.leaf (725829872788696131812886024967910716036278681693162318622595)))
  (.branch (.leaf (725091901561832647304282036533302074062544233500633351750168))
  (.leaf (726156039895782500483034809784652680389061815735576433266059)))))
  (.branch (.branch (.branch (.leaf (725093114725714473272150456043140775627157053830814528504156))
  (.leaf (725058678906606920829129538858023106061165446332568604062357)))
  (.branch (.leaf (724282615330941228207394524796471583242038591093494159285310))
  (.leaf (724999131942893694650316550424727432595797975070299972115153))))
  (.branch (.branch (.leaf (723622931567646854113908007979599759159271845656036243571104))
  (.leaf (726033623240484191781468872130204973091977458323915558620559)))
  (.branch (.leaf (725289016224476740268636327047210296475918998691744602734748))
  (.leaf (724784414504981944020727576293590199358124512476205755616957))))))
  (.branch (.branch (.branch (.branch (.leaf (723951081171648610687394242960253949358124512476205755616958))
  (.leaf (726349705430311409801476841063889732281972861617584065320436)))
  (.branch (.leaf (725036989571791687854731732044455368041176575248211447658656))
  (.leaf (726432560957729112827411538903347906311186257469314778729366))))
  (.branch (.branch (.leaf (725462799787202604639938286925033236081746166995994686667303))
  (.leaf (725070873469350360861768582829391152993366782320313714690037)))
  (.branch (.leaf (723995831237455949742904191459599116938323419421577871899539))
  (.leaf (724893405889809727506153219829316838304159973863505100227467)))))
  (.branch (.branch (.branch (.leaf (723582878964633041628167391567239693505081548948403314792566))
  (.leaf (725937883369737795611231953643671424945143293880686482104876)))
  (.branch (.leaf (724959435863659929737981065296250209281787911975692198067788))
  (.leaf (724907366744190840629799344895593514695604376347558558285855))))
  (.branch (.branch (.leaf (724051270126744318106225217715789959829906419474042972215469))
  (.leaf (724804891756821384987495992033581881224192433357812167339527)))
  (.branch (.leaf (723599759734850138206655582151747403489256901563717553909363))
  (.leaf (724295993912411615338294632425584150678982276646722756049651)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (723583584215626918553597847728792064611114958779404888731784))
  (.leaf (723597580057090926590748757183107765526730453298687360943760)))
  (.branch (.leaf (722748779454830515427501127795489882344118482849102677655222))
  (.leaf (725035601466150464627038309919721249686879967881186884246391))))
  (.branch (.branch (.leaf (723937421516961437980557451796891404629050086246677557377401))
  (.leaf (726224662776638046285957043384668568898193442147388867195929)))
  (.branch (.leaf (725433705556301271776634345476257635915344977013570067104424))
  (.leaf (725343681853161513621792969285019869442465903535516662013479)))))
  (.branch (.branch (.branch (.leaf (724554341419938316930325023127289554249695151412316385516846))
  (.leaf (724767845992923712993867644293157808925884364555341424928436)))
  (.branch (.leaf (723595662228433817218530726183171614662812440367088494147294))
  (.leaf (724392640205454690685411779657619865491090367666834508287842))))
  (.branch (.branch (.leaf (723616500363754318073937052873007770823065039366830151624313))
  (.leaf (723218113928444361331160522970425193562640357998059775545797)))
  (.branch (.leaf (722460495591714364424434210144915840826372634664216954346570))
  (.leaf (724707114532554286291523779301215400040575344287822943576820))))))
  (.branch (.branch (.branch (.branch (.leaf (723549707125146878884116371893806063620822257868069857157068))
  (.leaf (725796615639616458582204227536688987961108966110780947983209)))
  (.branch (.leaf (724978120373254823144486910923909742770085737255024797336892))
  (.leaf (724571346229167664479112956661489719914820044141439872152978))))
  (.branch (.branch (.leaf (723874340863755471289035390829874849975965099990889663765331))
  (.leaf (725027716702473124734330921095278342423223909524855411504320)))
  (.branch (.leaf (724031329223921755940297365493147064947788657215712288170361))
  (.leaf (726265880486982098025703750124101567458498558765155904231140)))))
  (.branch (.branch (.branch (.leaf (725480528153777730154894316837952295917382920679943345199628))
  (.leaf (725036461638282643231235964608173384352757070339807290777861)))
  (.branch (.leaf (724335629490065392037080916669224058308260577714980436174049))
  (.leaf (726566199185904591607925229552893336448516569670409670336863))))
  (.branch (.branch (.leaf (725297769873973716608696180169380046298212273788453359871142))
  (.leaf (725834187272850992552888967000641617677286728003462707300265)))
  (.branch (.leaf (724987870132560877551457628392532285017186499719736247628457))
  (.leaf (724882866145144433064502485814261119766508995434157456386545))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (723952806621334909254978676290438203099842328767490789719880))
  (.leaf (726141326748208178980213454461085423841423747155026703142608)))
  (.branch (.leaf (725221279717050036710960074096631264523375540217930877157896))
  (.leaf (725956175518938396546718565133883528369464827938764801640632))))
  (.branch (.branch (.leaf (725322681871012291566534034686973921882716811176256638500170))
  (.leaf (725247323706188924994221697649616895438471037019131636319662)))
  (.branch (.leaf (724431425012146883126365125435096226075429697299622495172065))
  (.leaf (724464513078607023043785476981366419329344281370083474991842)))))
  (.branch (.branch (.branch (.leaf (723552448949771293271416193119911955217030730469552791036756))
  (.leaf (725696627989221488889507681463770885957720269593138530643065)))
  (.branch (.leaf (724896168778665606925909661048575319406977264517890608317752))
  (.leaf (724630387395884549031141564850961022571750107844416616493420))))
  (.branch (.branch (.leaf (723773212021264359492602009438473049663867981173128488895786))
  (.leaf (725901963699100180805228195273378640261923552519087611862680)))
  (.branch (.leaf (724584657411472322019946698661169271030875628285733465249831))
  (.leaf (726709801373099266922642238843771416337213699696666296703011))))))
  (.branch (.branch (.branch (.branch (.leaf (725973354810771100440412437396390131377549625039649514257717))
  (.leaf (725751143540394360406481006710981013187523123216576179521965)))
  (.branch (.leaf (724987794382756681998740326099833635618240890646722915538105))
  (.leaf (727103422176024750168766817475820152263444433174711874583352))))
  (.branch (.branch (.leaf (726274005756969727370039406173345303551847943095011872544298))
  (.leaf (726953579676832395139158625376278774828577427318563390463945)))
  (.branch (.leaf (726338222652951610187249739121381613841446655107069549921818))
  (.leaf (726269457913030113928325107396125180575444302545757705984750)))))
  (.branch (.branch (.branch (.leaf (725438376280241858907903837454898034287028277155803535094975))
  (.leaf (726266936851322388625098998481712287384128617311580953308932)))
  (.branch (.leaf (725294389674858572337188548679582892887320138115586855012428))
  (.leaf (725792210979226678363139376388109320887275739689085162756219))))
  (.branch (.branch (.leaf (724796305917116717392466801441288963057199195546753785403142))
  (.leaf (724761612532361087048106250625305626411115613781919677317388)))
  (.branch (.leaf (724025915006423831995729321036886548982545663999549570509282))
  (.leaf (726078675695182787477238563604374304210409645179571418072876)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (725216131603472029099813519512698529849739451176044081212209))
  (.leaf (726237328183463848437358383768332218467665173783640255098896)))
  (.branch (.leaf (725524296508593130589093179649920422542747559050762698144566))
  (.leaf (725072948657044529324616175360000007815185002246999805272028))))
  (.branch (.branch (.leaf (724279275088749748908623638155325720114950332315360176662704))
  (.leaf (724707351116204073362065763498098566265474888220200667755546)))
  (.branch (.leaf (723678544531841933444370290247068045003472144735975702049101))
  (.leaf (725691138977289986339734940482321862436062399778954471698691)))))
  (.branch (.branch (.branch (.leaf (724971666799096239033219088656944189443241298038187561849871))
  (.leaf (724886270632089885585760217804059672301018862006058641035061)))
  (.branch (.leaf (724110007851975886857547269664331683995741320434112493449945))
  (.leaf (726108339033549126636335517288408522923000351595421180363887))))
  (.branch (.branch (.leaf (725009793307046811455192493033131492473762675595021569711224))
  (.leaf (725887477090043441890409023182134507587468767917498162758220)))
  (.branch (.leaf (725358979231011558068540060745632931547116295648628781517635))
  (.leaf (724749341170289121615940934773653560135447617360014237332289))))))
  (.branch (.branch (.branch (.branch (.leaf (724154001879047634739196559444083578932780364890837602903816))
  (.leaf (724851413657358650925583091094294023664593320127656461569462)))
  (.branch (.leaf (723919880597578639467888428217127546924806312958864391403049))
  (.leaf (725888681564702290610245585392795651133223146626199060741727))))
  (.branch (.branch (.leaf (725222014898035623943578918726126651133223146626199060741728))
  (.leaf (725155726036804922754980972447967197203651482835792758635344)))
  (.branch (.leaf (724471380287572578701056871046795670039761099812946834983236))
  (.leaf (726421306585181064665566132115264550795718227524434184715449)))))
  (.branch (.branch (.branch (.leaf (725309414079031431322950333359144177524577412523970061444311))
  (.leaf (725752330733517079134449290933595144334893235458494887162858)))
  (.branch (.leaf (724962883631114309244977733561001656648578671665652339076634))
  (.leaf (724945914124013223196523264053900989361524744935612248712659))))
  (.branch (.branch (.leaf (724280852191861091843545906621779188100614564343231197860535))
  (.leaf (726213704179886973615619120948259253845365676397703650582280)))
  (.branch (.leaf (725280197354423973768491183826945613297240505205808337138468))
  (.leaf (726001929326308189053630600299564059682724363752621817330511)))))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (725350887659641522386963933632899997182724363752621817330511))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))))
  (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))
  (.branch (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))))
  (.branch (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))
  (.branch (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0))))
  (.branch (.branch (.leaf (0))
  (.leaf (0)))
  (.branch (.leaf (0))
  (.leaf (0)))))))))))

private def fast512G : ℕ→ℤ := densityTreeValue 10 fast512GTree

private def fast512a (n : ℕ) : ℤ := fast512P n-fast512P (n-1)

theorem density_fast_512_checked : fastDensityCheck fast512a fast512P fast512b fast512G 512 1000000000000000000000000000000 1000000000000000000000000000000000000000000000000000000000000=true := by
  decide +kernel

theorem mobius_density_fast_le_1001_1000_512 (n : ℕ) (hn : n≤512) :
    coprimeDensityPrefix Helfgott.mobiusSigmaWeight n≤(1001/1000:ℝ) := by
  have hh := fastDensityCheck_sound fast512a fast512P fast512b fast512G 512 1000000000000000000000000000000 1000000000000000000000000000000000000000000000000000000000000 (by norm_num) (by norm_num) density_fast_512_checked n hn
  exact hh.trans (by norm_num)

end HelfgottQuadratic

end

open scoped BigOperators
theorem solution (N : ℕ) (hN : N≤512) :
    (∑ s ∈ Finset.Icc 1 N, (1/(s:ℝ))*(∑ a ∈ Finset.Icc 1 (N/s), ∑ b ∈ Finset.Icc 1 (N/s),
      if Nat.Coprime a b then
        (((ArithmeticFunction.moebius a:ℤ):ℝ)/(∏ p ∈ a.primeFactors, ((p:ℝ)+1)))*
        (((ArithmeticFunction.moebius b:ℤ):ℝ)/(∏ p ∈ b.primeFactors, ((p:ℝ)+1))) else 0))≤(1001/1000:ℝ) := by
  exact HelfgottQuadratic.mobius_density_fast_le_1001_1000_512 N hN
