-- Prove2me | solution 1 for LonelyRunner.MixedArithmetic.contradiction
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T18:57:47.101998+00:00
-- url     : https://prove2.me/submissions/126367a7-fe80-43a5-b384-752ca54225b0

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs
import Theorems.Thm_LonelyRunner_ElementarySmooth_five_seven
import Theorems.Thm_LonelyRunner_MixedNormalize_normalize

namespace LonelyRunner















































end LonelyRunner

namespace LonelyRunner.BadCover





















end LonelyRunner.BadCover

namespace LonelyRunner.LaminarCover

open Set





end LonelyRunner.LaminarCover

namespace LonelyRunner.Farey



















end LonelyRunner.Farey

namespace LonelyRunner.CoprimeReplacements

open Farey BadCover





























end LonelyRunner.CoprimeReplacements

namespace LonelyRunner.SingleDeletion

open BadCover









end LonelyRunner.SingleDeletion

namespace LonelyRunner.BadCover











end LonelyRunner.BadCover

namespace LonelyRunner.MatchingArithmetic





end LonelyRunner.MatchingArithmetic

namespace LonelyRunner.LargeDeletionMatching

open BadCover SingleDeletion



















end LonelyRunner.LargeDeletionMatching

namespace LonelyRunner.SeparatedBands

open BadCover









end LonelyRunner.SeparatedBands

namespace LonelyRunner

open Finset



























end LonelyRunner

namespace LonelyRunner

















end LonelyRunner

namespace LonelyRunner.FailedWindow

open Farey BadCover









end LonelyRunner.FailedWindow

namespace LonelyRunner.SeparatedReplacements

open LargeDeletionMatching SeparatedBands























end LonelyRunner.SeparatedReplacements

namespace LonelyRunner.MixedReplacements

open LargeDeletionMatching SeparatedReplacements













end LonelyRunner.MixedReplacements

namespace LonelyRunner.SeparatedMulti

open SeparatedReplacements SeparatedBands SingleDeletion























end LonelyRunner.SeparatedMulti

namespace LonelyRunner.InteractionComponents

open Set























end LonelyRunner.InteractionComponents

namespace LonelyRunner.GWArithmetic

open SeparatedReplacements

/-- A positive multiplicative interval of ratio p contains a power of p. -/
theorem power_in_window {c p : ℕ} (hc : 0 < c) (hp : 2 ≤ p) :
    ∃ j : ℕ, c ≤ p^j ∧ p^j < p*c := by
  by_cases hc1 : c=1
  · exact ⟨0,by simp [hc1],by simp [hc1]; omega⟩
  have hc2 : 1 < c := by omega
  have hp1 : 1 < p := by omega
  refine ⟨Nat.clog p c,Nat.le_pow_clog hp1 c,?_⟩
  have hh := Nat.mul_lt_mul_of_pos_left (Nat.pow_pred_clog_lt_self hp1 hc2)
    (show 0 < p by omega)
  have hlog := Nat.clog_pos hp1 hc2
  simpa [← pow_succ',Nat.pred_eq_sub_one,Nat.sub_add_cancel (show 1 ≤ Nat.clog p c by omega)] using hh

theorem deficit_at_least_two {n s k : ℕ} (hsn : s < n) (hk : 2 ≤ k)
    (hgw : GW n s k) : 2 ≤ n-s := by
  by_contra! hh
  have heq : n-s=1 := by omega
  exact hgw 1 (by omega) (by simpa [heq] using (show 1 < k by omega)) (by simp)

/-- Every prime at most the multiplier divides the accelerated speed. -/
theorem small_prime_dvd {n s k p : ℕ} (hsn : s < n)
    (hgw : GW n s k) (hp : Nat.Prime p) (hpk : p ≤ k) : p ∣ s := by
  by_contra hnot
  obtain ⟨j,hlo,hhi⟩ := power_in_window (Nat.sub_pos_of_lt hsn) hp.two_le
  apply hgw (p^j) hlo (lt_of_lt_of_le hhi (Nat.mul_le_mul_right (n-s) hpk))
  exact hp.coprime_pow_of_not_dvd hnot

end LonelyRunner.GWArithmetic

namespace LonelyRunner.ContactPreservation











end LonelyRunner.ContactPreservation

namespace LonelyRunner.GWContactArithmetic

open SeparatedReplacements ContactPreservation



















end LonelyRunner.GWContactArithmetic

namespace LonelyRunner.ComponentRestoration

open SeparatedMulti InteractionComponents









end LonelyRunner.ComponentRestoration

namespace LonelyRunner.GWGrowth

open SeparatedReplacements GWArithmetic

theorem prime_in_window_dvd {n s k p : ℕ} (hgw : GW n s k)
    (hp : Nat.Prime p) (hlo : n-s ≤ p) (hhi : p < k*(n-s)) : p ∣ s := by
  by_contra hh
  exact hgw p hlo hhi (hp.coprime_iff_not_dvd.mpr hh).symm

theorem primorial_dvd {n s k : ℕ} (hsn : s < n) (hgw : GW n s k) :
    primorial k ∣ s := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.prime
  · intro p hp
    obtain ⟨hpk,hprime⟩ := Finset.mem_filter.mp hp
    exact small_prime_dvd hsn hgw hprime (by simpa using hpk)

/-- Apart from k=4, the product of primes up to k is at least 2k. -/
theorem twice_le_primorial {k : ℕ} (hk : 3 ≤ k) (hk4 : k ≠ 4) :
    2*k ≤ primorial k := by
  by_cases hk3 : k=3
  · subst k
    decide
  have hk5 : 5 ≤ k := by omega
  have hP30 : 30 ≤ primorial k := by
    have hh := primorial_mono hk5
    norm_num [primorial,Finset.prod_range_succ] at hh ⊢
    exact hh
  have hd2 : 2 ∣ primorial k := Nat.prime_two.dvd_primorial_iff.mpr (by omega)
  obtain ⟨H,hH⟩ := hd2
  have hH15 : 15 ≤ H := by omega
  have hnot2 : ¬ 2 ∣ H := by
    intro hh
    apply (Nat.squarefree_iff_prime_squarefree.mp (squarefree_primorial k)) 2 Nat.prime_two
    rw [hH]
    exact Nat.mul_dvd_mul_left 2 hh
  have hco2 : Nat.Coprime 2 H := Nat.prime_two.coprime_iff_not_dvd.mpr hnot2
  have hzP : Nat.Coprime (H-2) (primorial k) := by
    rw [hH,Nat.coprime_mul_iff_right]
    exact ⟨(Nat.coprime_sub_self_left (by omega)).mpr hco2.symm,
      (Nat.coprime_self_sub_left (by omega)).mpr hco2⟩
  obtain ⟨p,hp,hpz⟩ := Nat.exists_prime_and_dvd (show H-2 ≠ 1 by omega)
  have hkp : k < p := by
    by_contra! hh
    have hpP := hp.dvd_primorial_iff.mpr hh
    have hone := Nat.eq_one_of_dvd_coprimes hzP hpz hpP
    exact hp.ne_one hone
  have hpzle := Nat.le_of_dvd (show 0 < H-2 by omega) hpz
  omega

/-- Bertrand supplies a prime strictly between half of kc and kc, and this
prime is beyond k and at least c. -/
theorem half_window_prime {k c : ℕ} (hk : 3 ≤ k) (hc : 2 ≤ c) :
    ∃ t : ℕ, Nat.Prime t ∧ k < t ∧ c ≤ t ∧ k*c < 2*t ∧ t < k*c := by
  obtain ⟨t,ht,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (k*c/2)
    (by
      have : 6 ≤ k*c := by nlinarith
      omega)
  have hmod := Nat.mod_lt (k*c) (by norm_num : 0 < 2)
  have hdiv := Nat.mod_add_div (k*c) 2
  have hkc : 2*k ≤ k*c := by nlinarith
  have hcc : 2*c ≤ k*c := by nlinarith
  have htlt : t < k*c := by
    have htle : t ≤ k*c := by omega
    by_contra! hh
    have heq : t=k*c := by omega
    have hkd : k ∣ t := by rw [heq]; exact dvd_mul_right k c
    rcases ht.eq_one_or_self_of_dvd k hkd with h | h
    · omega
    · nlinarith
  exact ⟨t,ht,by omega,by omega,by omega,htlt⟩

/-- General growth away from the exceptional primorial value k=4. -/
theorem growth_ne_four {n s k : ℕ} (hs : 0 < s) (hsn : s < n)
    (hk : 3 ≤ k) (hk4 : k ≠ 4) (hgw : GW n s k) : k*k*(n-s) < s := by
  have hc := deficit_at_least_two hsn (by omega) hgw
  obtain ⟨t,ht,hkt,hct,hhalf,hend⟩ := half_window_prime hk hc
  have htd : t ∣ s := prime_in_window_dvd hgw ht hct hend
  have hcop : Nat.Coprime (primorial k) t := by
    apply Nat.Coprime.symm
    apply ht.coprime_iff_not_dvd.mpr
    intro hh
    have : t ≤ k := ht.dvd_primorial_iff.mp hh
    omega
  have hprod := hcop.mul_dvd_of_dvd_of_dvd (primorial_dvd hsn hgw) htd
  have hle := Nat.le_of_dvd hs hprod
  have hP := twice_le_primorial hk hk4
  have hmul := Nat.mul_le_mul_right t hP
  nlinarith [Nat.mul_lt_mul_of_pos_left hhalf (show 0 < k by omega)]

/-- Strict version of Bertrand for an integer lower endpoint at least two. -/
theorem prime_double {c : ℕ} (hc : 2 ≤ c) :
    ∃ p : ℕ, Nat.Prime p ∧ c < p ∧ p < 2*c := by
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul c (by omega)
  refine ⟨p,hp,hlo,?_⟩
  by_contra! hh
  have heq : p=2*c := by omega
  have htwo : 2 ∣ p := by rw [heq]; exact dvd_mul_right 2 c
  rcases hp.eq_one_or_self_of_dvd 2 htwo with hh | hh
  · omega
  · omega

theorem coprime_six {p : ℕ} (hp : Nat.Prime p) (hbig : 3 < p) :
    Nat.Coprime 6 p := by
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  rw [show (6:ℕ)=2*3 by norm_num,hp.dvd_mul] at hd
  rcases hd with hd | hd
  · have := Nat.le_of_dvd (by norm_num : 0 < (2:ℕ)) hd
    omega
  · have := Nat.le_of_dvd (by norm_num : 0 < (3:ℕ)) hd
    omega

theorem six_dvd {n s k : ℕ} (hsn : s < n) (hk : 3 ≤ k) (hgw : GW n s k) :
    6 ∣ s := by
  have h2 := small_prime_dvd hsn hgw Nat.prime_two (show 2 ≤ k by omega)
  have h3 := small_prime_dvd hsn hgw Nat.prime_three hk
  exact (show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd h2 h3

theorem growth_four {n s : ℕ} (hs : 0 < s) (hsn : s < n) (hgw : GW n s 4) :
    4*4*(n-s) < s := by
  have hc := deficit_at_least_two hsn (by norm_num) hgw
  have h6 := six_dvd hsn (by norm_num : 3 ≤ 4) hgw
  by_cases hc4 : 4 ≤ n-s
  · obtain ⟨u,hu,hclu,huc⟩ := prime_double (show 2 ≤ n-s by omega)
    obtain ⟨v,hv,hcv,hvc⟩ := prime_double (show 2 ≤ 2*(n-s) by omega)
    have hud := prime_in_window_dvd hgw hu (by omega) (by omega)
    have hvd := prime_in_window_dvd hgw hv (by omega) (by omega)
    have h6u := coprime_six hu (by omega)
    have h6v := coprime_six hv (by omega)
    have huv : Nat.Coprime u v := (hu.coprime_iff_not_dvd).mpr (by
      intro hh
      rcases hv.eq_one_or_self_of_dvd u hh with hh | hh
      · exact hu.ne_one hh
      · omega)
    have h6ud := h6u.mul_dvd_of_dvd_of_dvd h6 hud
    have hprod := (h6v.mul_left huv).mul_dvd_of_dvd_of_dvd h6ud hvd
    have hle := Nat.le_of_dvd hs hprod
    have hmul := Nat.mul_lt_mul_of_pos_left hcv hu.pos
    nlinarith [Nat.mul_lt_mul_of_pos_right hclu (show 0 < n-s by omega)]
  · have h5 := prime_in_window_dvd hgw (by decide : Nat.Prime 5)
      (by omega) (by omega)
    have h7 := prime_in_window_dvd hgw (by decide : Nat.Prime 7)
      (by omega) (by omega)
    have h30 := (show Nat.Coprime 6 5 by decide).mul_dvd_of_dvd_of_dvd h6 h5
    have h210 := (show Nat.Coprime 30 7 by decide).mul_dvd_of_dvd_of_dvd h30 h7
    have hle := Nat.le_of_dvd hs h210
    omega

/-- A valid acceleration by k≥3 forces the deleted speed beyond k² times
its deficit. This is unconditional and uses only proved prime arithmetic. -/
theorem quadratic_growth {n s k : ℕ} (hs : 0 < s) (hsn : s < n)
    (hk : 3 ≤ k) (hgw : GW n s k) : k*k*(n-s) < s := by
  by_cases hk4 : k=4
  · subst k
    exact growth_four hs hsn hgw
  · exact growth_ne_four hs hsn hk hk4 hgw

theorem nearby_unit_six (c : ℕ) :
    ∃ b : ℕ, c ≤ b ∧ b ≤ c+3 ∧ Nat.Coprime 6 b := by
  have hmod := Nat.mod_lt c (by norm_num : 0 < 6)
  have hchoose : ∃ b : ℕ, c ≤ b ∧ b ≤ c+3 ∧ (b%6=1 ∨ b%6=5) := by
    interval_cases h : c%6 <;>
      first | exact ⟨c,by omega,by omega,by omega⟩
            | exact ⟨c+1,by omega,by omega,by omega⟩
            | exact ⟨c+2,by omega,by omega,by omega⟩
            | exact ⟨c+3,by omega,by omega,by omega⟩
  obtain ⟨b,hlo,hhi,hmodb⟩ := hchoose
  refine ⟨b,hlo,hhi,?_⟩
  rw [Nat.coprime_iff_gcd_eq_one,Nat.gcd_rec]
  rcases hmodb with hh | hh <;> rw [hh] <;> decide

/-- In the residual tripling case, a mild preliminary lower bound improves
to S>20c. -/
theorem tripling_growth {n s : ℕ} (hs : 0 < s) (hsn : s < n)
    (hgw : GW n s 3) (h15 : 15*(n-s) < s) : 20*(n-s) < s := by
  have hc := deficit_at_least_two hsn (by norm_num) hgw
  have h6 := six_dvd hsn (by norm_num : 3 ≤ 3) hgw
  by_cases hc6 : 6 ≤ n-s
  · obtain ⟨b,hcb,hbc,hcop⟩ := nearby_unit_six (n-s)
    have hnot := hgw b hcb (by omega)
    obtain ⟨p,hp,hps,hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have hcp : Nat.Coprime 6 p := hcop.coprime_dvd_right hpb
    have hp5 : 5 ≤ p := by
      by_contra! hh
      have hp2 := hp.two_le
      interval_cases p <;> norm_num [Nat.Coprime] at *
    have hple := Nat.le_of_dvd (show 0 < b by omega) hpb
    obtain ⟨t,ht,hkt,hct,hhalf,hend⟩ := half_window_prime (by norm_num : 3 ≤ 3) hc
    have htd := prime_in_window_dvd hgw ht hct hend
    have hpt : p < t := by omega
    have h6t := coprime_six ht hkt
    have hcpt : Nat.Coprime p t := hp.coprime_iff_not_dvd.mpr (by
      intro hh
      rcases ht.eq_one_or_self_of_dvd p hh with hh | hh
      · exact hp.ne_one hh
      · omega)
    have h6p := hcp.mul_dvd_of_dvd_of_dvd h6 hps
    have hprod := (h6t.mul_left hcpt).mul_dvd_of_dvd_of_dvd h6p htd
    have hle := Nat.le_of_dvd hs hprod
    have hprodlo := Nat.mul_le_mul_right t hp5
    nlinarith
  · have h5 := prime_in_window_dvd hgw (by decide : Nat.Prime 5)
      (by omega) (by omega)
    have h30 := (show Nat.Coprime 6 5 by decide).mul_dvd_of_dvd_of_dvd h6 h5
    by_cases hc2 : n-s=2
    · obtain ⟨z,hz⟩ := h30
      have hz2 : 2 ≤ z := by nlinarith
      nlinarith
    · have h7 := prime_in_window_dvd hgw (by decide : Nat.Prime 7)
        (by omega) (by omega)
      have h210 := (show Nat.Coprime 30 7 by decide).mul_dvd_of_dvd_of_dvd h30 h7
      have hle := Nat.le_of_dvd hs h210
      omega

end LonelyRunner.GWGrowth

namespace LonelyRunner.OddSmooth

open SeparatedReplacements GWGrowth















end LonelyRunner.OddSmooth

namespace LonelyRunner.SecondUnit

open SeparatedReplacements GWArithmetic OddSmooth



/-- In the first normalized shape a power of two supplies a different unit. -/
theorem doubling_shape {r s u a : ℕ} (ha : 0 < a) (hu : 1 < u)
    (hR : Nat.Coprime r (2*u)) (hUS : Nat.Coprime u s) (h2S : 2 ∣ s) :
    ∃ w, a ≤ w ∧ w < 2*a ∧ Nat.Coprime r w ∧ w ≠ 2*u := by
  obtain ⟨j,hlo,hhi⟩ := power_in_window (p := 2) ha (by norm_num)
  have hR2 : Nat.Coprime r 2 := (Nat.coprime_mul_iff_right.mp hR).1
  have hu2 : Nat.Coprime u 2 := hUS.coprime_dvd_right h2S
  refine ⟨2^j,hlo,hhi,hR2.pow_right j,?_⟩
  intro heq
  have hud : u ∣ 2^j := by rw [heq]; exact dvd_mul_left u 2
  have hone := (hu2.pow_right j).eq_one_of_dvd hud
  omega

/-- If S=R+2u and u is coprime to S, an odd S-smooth number is a unit modulo R. -/
theorem smooth_unit {r s u w : ℕ} (hrel : s=r+2*u) (hUS : Nat.Coprime u s)
    (hwodd : Odd w) (hws : Smooth s w) : Nat.Coprime r w := by
  by_contra hnot
  obtain ⟨p,hp,hpr,hpw⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hps := hws p hp hpw
  have hp2u : p ∣ 2*u := by
    have hh := Nat.dvd_sub hps hpr
    simpa [hrel] using hh
  rcases hp.dvd_mul.mp hp2u with hp2 | hpu
  · rcases Nat.prime_two.eq_one_or_self_of_dvd p hp2 with hh | hh
    · exact hp.ne_one hh
    · have hwmod := Nat.odd_iff.mp hwodd
      subst p
      have hd := Nat.mod_eq_zero_of_dvd hpw
      omega
  · exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hUS hpu hps)

/-- A multiple of a nontrivial unit modulo S cannot be S-smooth. -/
theorem smooth_ne_multiple {s u w k : ℕ} (hu : 1 < u)
    (hUS : Nat.Coprime u s) (hws : Smooth s w) : w ≠ k*u := by
  intro heq
  obtain ⟨p,hp,hpu⟩ := Nat.exists_prime_and_dvd (show u ≠ 1 by omega)
  have hpw : p ∣ w := by rw [heq]; exact dvd_mul_of_dvd_right hpu k
  have hps := hws p hp hpw
  exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hUS hpu hps)



end LonelyRunner.SecondUnit

namespace LonelyRunner.ElementarySmooth

open SeparatedReplacements OddSmooth GWArithmetic GWGrowth SecondUnit

theorem density_factor {C : ℕ → Prop} {seed x K : ℕ}
    (hK : 0 < K) (hseed : C seed) (hx : seed < x)
    (hstep : ∀ w, C w → ∃ v, C v ∧ w < v ∧ v < K*w) :
    ∃ w, C w ∧ x ≤ w ∧ w < K*x := by
  classical
  let w := Nat.findGreatest C (x-1)
  have hwC : C w := Nat.findGreatest_spec (show seed ≤ x-1 by omega) hseed
  have hwx : w < x := by
    have hh := Nat.findGreatest_le (P := C) (x-1)
    dsimp [w]
    omega
  obtain ⟨v,hvC,hwv,hv⟩ := hstep w hwC
  have hxv : x ≤ v := by
    by_contra! hh
    exact (Nat.findGreatest_is_greatest hwv (by omega)) hvC
  exact ⟨v,hvC,hxv,lt_trans hv (Nat.mul_lt_mul_of_pos_left hwx hK)⟩

theorem triple_cycle {L K A B C x : ℕ}
    (hL : 0 < L) (hK : 0 < K) (hAB : A < B) (hBC : B < C)
    (hCA : C < L*A) (hBA : B < K*A) (hCB : C < K*B)
    (hAC : L*A < K*C) (hx : A < x) :
    ∃ w j, (w=L^j*A ∨ w=L^j*B ∨ w=L^j*C) ∧ x ≤ w ∧ w < K*x := by
  let P : ℕ → Prop := fun w => ∃ j, w=L^j*A ∨ w=L^j*B ∨ w=L^j*C
  have hseed : P A := ⟨0,Or.inl (by simp)⟩
  have hstep : ∀ w, P w → ∃ v, P v ∧ w < v ∧ v < K*w := by
    intro w hw
    obtain ⟨j,hj⟩ := hw
    have hpow : 0 < L^j := pow_pos hL _
    rcases hj with rfl | rfl | rfl
    · refine ⟨L^j*B,⟨j,Or.inr (Or.inl rfl)⟩,Nat.mul_lt_mul_of_pos_left hAB hpow,?_⟩
      nlinarith only [Nat.mul_lt_mul_of_pos_left hBA hpow]
    · refine ⟨L^j*C,⟨j,Or.inr (Or.inr rfl)⟩,Nat.mul_lt_mul_of_pos_left hBC hpow,?_⟩
      nlinarith only [Nat.mul_lt_mul_of_pos_left hCB hpow]
    · refine ⟨L^(j+1)*A,⟨j+1,Or.inl rfl⟩,?_,?_⟩
      · simpa [pow_succ,mul_assoc] using Nat.mul_lt_mul_of_pos_left hCA hpow
      · have hh := Nat.mul_lt_mul_of_pos_left hAC hpow
        simpa [pow_succ,mul_assoc,mul_comm,mul_left_comm] using hh
  obtain ⟨w,⟨j,hj⟩,hlo,hhi⟩ := density_factor hK hseed hx hstep
  exact ⟨w,j,hj,hlo,hhi⟩



theorem smooth_pow {s a j : ℕ} (ha : Smooth s a) : Smooth s (a^j) := by
  intro p hp hd
  exact ha p hp (hp.dvd_of_dvd_pow hd)

theorem smooth_mul {s a b : ℕ} (ha : Smooth s a) (hb : Smooth s b) : Smooth s (a*b) := by
  intro p hp hd
  exact (hp.dvd_mul.mp hd).elim (ha p hp) (hb p hp)

theorem smooth_of_dvd {s a : ℕ} (ha : a ∣ s) : Smooth s a := fun _ _ hd => dvd_trans hd ha

theorem odd_smooth_cycle {s A B C x : ℕ}
    (h3 : 3 ∣ s) (hA : Odd A ∧ Smooth s A) (hB : Odd B ∧ Smooth s B)
    (hC : Odd C ∧ Smooth s C) (hAB : A < B) (hBC : B < C) (hCA : C < 3*A)
    (hBA : B < 2*A) (hCB : C < 2*B) (hAC : 3*A < 2*C) (hx : A < x) :
    ∃ w, Odd w ∧ Smooth s w ∧ x ≤ w ∧ w < 2*x := by
  obtain ⟨w,j,hw,hlo,hhi⟩ := triple_cycle (L := 3) (K := 2)
    (by norm_num) (by norm_num) hAB hBC hCA hBA hCB hAC hx
  have hpow : Odd ((3:ℕ)^j) ∧ Smooth s (3^j) :=
    ⟨(show Odd (3:ℕ) by decide).pow,smooth_pow (smooth_of_dvd h3)⟩
  refine ⟨w,?_,?_,hlo,hhi⟩
  · rcases hw with rfl | rfl | rfl
    · exact hpow.1.mul hA.1
    · exact hpow.1.mul hB.1
    · exact hpow.1.mul hC.1
  · rcases hw with rfl | rfl | rfl
    · exact smooth_mul hpow.2 hA.2
    · exact smooth_mul hpow.2 hB.2
    · exact smooth_mul hpow.2 hC.2

/-- Unconditional odd smooth coverage: no prime-spacing assumption. -/
theorem coverage {n s x : ℕ} (hsn : s < n) (hgw : GW n s 3)
    (hx : 3*(n-s) ≤ x) : ∃ w, Odd w ∧ Smooth s w ∧ x ≤ w ∧ w < 2*x := by
  have hc := deficit_at_least_two hsn (by norm_num) hgw
  have hd3 := small_prime_dvd hsn hgw Nat.prime_three (by norm_num)
  have hs3 := smooth_of_dvd hd3
  have five_case (h5 : 5 ∣ s) : ∃ w, Odd w ∧ Smooth s w ∧ x ≤ w ∧ w < 2*x := by
    have hs5 := smooth_of_dvd h5
    have h9 : Odd 9 ∧ Smooth s 9 := ⟨by decide,by simpa using (smooth_pow (j := 2) hs3)⟩
    by_cases hx9 : x ≤ 9
    · exact ⟨9,h9.1,h9.2,hx9,by omega⟩
    apply odd_smooth_cycle hd3 h9
      (B := 15) (C := 25) ⟨by decide,smooth_mul hs3 hs5⟩
      ⟨by decide,by simpa using (smooth_pow (j := 2) hs5)⟩ <;> omega
  by_cases h5 : 5 ∣ s
  · exact five_case h5
  rcases five_seven hsn hgw with h5' | h7 | hc8
  · exact False.elim (h5 h5')
  · have hc4 : 4 ≤ n-s := by
      by_contra! hh
      exact h5 (prime_in_window_dvd hgw (by decide : Nat.Prime 5) (by omega) (by omega))
    have hs7 := smooth_of_dvd h7
    have h21 : Odd 21 ∧ Smooth s 21 := ⟨by decide,smooth_mul hs3 hs7⟩
    by_cases hx21 : x ≤ 21
    · exact ⟨21,h21.1,h21.2,hx21,by omega⟩
    apply odd_smooth_cycle hd3 h21
      (B := 27) (C := 49) ⟨by decide,by simpa using (smooth_pow (j := 3) hs3)⟩
      ⟨by decide,by simpa using (smooth_pow (j := 2) hs7)⟩ <;> omega
  · have h11 := prime_in_window_dvd hgw (by decide : Nat.Prime 11) (by omega) (by omega)
    have h17 := prime_in_window_dvd hgw (by decide : Nat.Prime 17) (by omega) (by omega)
    apply odd_smooth_cycle hd3 (A := 11) (B := 17) (C := 27)
      ⟨by decide,smooth_of_dvd h11⟩ ⟨by decide,smooth_of_dvd h17⟩
      ⟨by decide,by simpa using (smooth_pow (j := 3) hs3)⟩ <;> omega

end LonelyRunner.ElementarySmooth

namespace LonelyRunner.FailedFlank

open Farey BadCover LargeDeletionMatching









end LonelyRunner.FailedFlank

namespace LonelyRunner.FlankReduction







/-- Minimality's normalized relation leaves only d=1, or exactly the mixed
doubling/tripling case d=2,e=1,m=2,k=3. -/
theorem two_shapes {e d m : ℤ}
    (he : 1 ≤ e) (hd : 1 ≤ d) (hm : 2 ≤ m)
    (horder : m < e*(d+1)) (hnear : m*(e*d) < e*(d+1)+m) :
    (d=1 ∧ 4 ≤ e*(d+1)) ∨ (d=2 ∧ e=1 ∧ m=2) := by
  have hd2 : d ≤ 2 := by
    by_contra! hh
    have hd3 : 3 ≤ d := by omega
    have hbase : m ≤ (m-1)*d-1 := by
      nlinarith [mul_nonneg (show 0 ≤ m-2 by omega) (show 0 ≤ d-3 by omega)]
    have hmul := mul_le_mul_of_nonneg_right he (show 0 ≤ (m-1)*d-1 by omega)
    nlinarith only [hnear,hbase,hmul]
  have hcases : d=1 ∨ d=2 := by omega
  rcases hcases with rfl | rfl
  · left
    constructor
    · rfl
    · have he2 : 2 ≤ e := by omega
      nlinarith only [he2]
  · right
    have hm2 : m=2 := by
      by_contra hh
      have hm3 : 3 ≤ m := by omega
      have hmul := mul_le_mul_of_nonneg_right he (show 0 ≤ 2*m-3 by omega)
      nlinarith only [hnear,hmul,hm3]
    exact ⟨rfl,by nlinarith only [hnear,he,hm2],hm2⟩



/-- The first normalized shape leaves the whole doubling interval before
the wrapped band index could occur. -/
theorem doubling_cutoff {s c u k : ℤ}
    (hc : 0 < c) (hk : 4 ≤ k) (hu : 3*u < s) (hS : k*k*c < s) :
    2*(c+u) < s+c-k*c := by
  have hk2 : 3*(k+1) ≤ k*k := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hk2 hc.le
  nlinarith only [hh,hu,hS]

/-- The exceptional doubling/tripling shape has the same cutoff after the
stronger tripling growth bound. -/
theorem tripling_cutoff {s c u : ℤ} (hu : 5*u < s) (hS : 20*c < s) :
    2*(c+2*u) < s+c-3*c := by nlinarith



end LonelyRunner.FlankReduction

namespace LonelyRunner.MixedNormalize

open SeparatedReplacements SecondUnit GWArithmetic



end LonelyRunner.MixedNormalize

namespace LonelyRunner.MixedArithmetic

open SeparatedReplacements GWArithmetic GWGrowth FlankReduction SecondUnit



end LonelyRunner.MixedArithmetic

namespace LonelyRunner.NearData

open LargeDeletionMatching SeparatedReplacements







end LonelyRunner.NearData

namespace LonelyRunner.MixedConverse

open LargeDeletionMatching SeparatedReplacements MixedReplacements
open GWArithmetic GWGrowth FlankReduction









end LonelyRunner.MixedConverse

namespace LonelyRunner.SmallComponentRigidity

open SeparatedMulti SeparatedReplacements InteractionComponents





































end LonelyRunner.SmallComponentRigidity

open LonelyRunner
open LonelyRunner.MixedArithmetic
open SeparatedReplacements GWArithmetic GWGrowth FlankReduction SecondUnit

set_option maxHeartbeats 1800000 in
/-- Once the least failed unit has the unwrapped identity, the two-shape
reduction and the elementary second-unit construction contradict uniqueness. -/
theorem solution {n r s m k B D : ℕ}
    (hrs : r < s) (hsn : s < n) (hm : 2 ≤ m) (hD2 : 2 ≤ D)
    (hnear : m*D < k+m) (hgw : GW n s k) (hBr : B < r)
    (hDB : D*B=k*(s-r)) (hBkc : k*(n-s) ≤ B)
    (hBlo : n-r ≤ B) (hBcop : Nat.Coprime r B)
    (hmin : ∀ b, n-r ≤ b → Nat.Coprime r b → B ≤ b)
    (hforced : ∀ w, n-r ≤ w → w < 2*(n-r) → Nat.Coprime r w →
      w < n-k*(n-s) → w=B) : False := by
  have hmk : m < k := by nlinarith
  have hk : 3 ≤ k := by omega
  have hc := deficit_at_least_two hsn (by omega) hgw
  have hgrowth := quadratic_growth (by omega) hsn hk hgw
  obtain ⟨e,d,u,he,hd,hu,hDe,hke,hBu,hsr,hus,hku⟩ :=
    MixedNormalize.normalize hrs hsn hm hD2 hnear hgw hDB hBkc hBlo hBcop hmin
  have hshapes := two_shapes (e := (e:ℤ)) (d := (d:ℤ)) (m := (m:ℤ))
    (by exact_mod_cast he) (by exact_mod_cast hd) (by exact_mod_cast hm)
    (by exact_mod_cast (show m < e*(d+1) by omega))
    (by exact_mod_cast (show m*(e*d) < e*(d+1)+m by simpa [← hDe,← hke] using hnear))
  have hcZ : (0:ℤ) < (n-s:ℕ) := by exact_mod_cast (show 0 < n-s by omega)
  have hsum : n=r+(n-s)+d*u := by omega
  rcases hshapes with ⟨hd1,hk4⟩ | ⟨hd2,he1,hm2⟩
  · have hd1' : d=1 := by exact_mod_cast hd1
    subst d
    have hu3 : 3*u < s := by nlinarith
    have hk4' : 4 ≤ k := by
      have hh : 4 ≤ e*(1+1) := by exact_mod_cast hk4
      omega
    have hcutZ := doubling_cutoff (s := (s:ℤ)) (c := ((n-s:ℕ):ℤ))
      (u := (u:ℤ)) (k := (k:ℤ)) hcZ (by exact_mod_cast hk4')
      (by exact_mod_cast hu3) (by exact_mod_cast hgrowth)
    have hcut : 2*(n-r)+k*(n-s) < n := by
      have hh : (2:ℤ)*((n-s:ℕ)+u)+(k:ℤ)*(n-s:ℕ) < s+(n-s:ℕ) := by linarith
      have hhN : 2*((n-s)+u)+k*(n-s) < s+(n-s) := by exact_mod_cast hh
      omega
    have h2s := small_prime_dvd hsn hgw Nat.prime_two (by omega)
    obtain ⟨w,hlo,hhi,hcop,hne⟩ := doubling_shape (a := n-r) (by omega)
      (by nlinarith) (by simpa using (hBu ▸ hBcop)) hus h2s
    have hwB := hforced w hlo hhi hcop (by omega)
    exact hne (by simpa [hBu] using hwB)
  · have hd2' : d=2 := by exact_mod_cast hd2
    have he1' : e=1 := by exact_mod_cast he1
    have hk3 : k=3 := by simpa [hd2',he1'] using hke
    subst d
    subst k
    have hu5 : 5*u < s := by nlinarith
    have h15 : 15*(n-s) < s := by nlinarith
    have h20 := tripling_growth (by omega) hsn hgw h15
    have hcutZ := tripling_cutoff (s := (s:ℤ)) (c := ((n-s:ℕ):ℤ))
      (u := (u:ℤ)) (by exact_mod_cast hu5) (by exact_mod_cast h20)
    have hcut : 2*(n-r)+3*(n-s) < n := by
      have hh : (2:ℤ)*((n-s:ℕ)+2*u)+3*(n-s:ℕ) < s+(n-s:ℕ) := by linarith
      have hhN : 2*((n-s)+2*u)+3*(n-s) < s+(n-s) := by exact_mod_cast hh
      omega
    obtain ⟨w,hwodd,hws,hlo,hhi⟩ := ElementarySmooth.coverage (x := n-r) hsn hgw (by omega)
    have hcop := smooth_unit hsr hus hwodd hws
    have hne : w ≠ 3*u := smooth_ne_multiple (by nlinarith) hus hws
    have hwB := hforced w hlo hhi hcop (by omega)
    exact hne (by simpa [hBu] using hwB)
