-- Prove2me | solution 1 for NymanBeurling.prime_coefficient_sq_le_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:45:08.722013+00:00
-- url     : https://prove2.me/submissions/97bba5a9-757f-48a5-91af-709ddcdfe624

import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

open Finset

namespace NymanPrime

def residual (c : ℕ →₀ ℚ) (m : ℕ) : ℚ :=
  1 - ∑ k ∈ c.support, c k * ((m % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ)

def mass (c : ℕ →₀ ℚ) : ℚ := 1 + ∑ k ∈ c.support, |c k|

def term (c : ℕ →₀ ℚ) (i : ℕ) : ℚ :=
  residual c (i+1)^2 / (((i:ℚ)+1)*((i:ℚ)+2))

def cost (c : ℕ →₀ ℚ) (H : ℕ) : ℚ := ∑ n ∈ range H, term c n + (mass c)^2/((H:ℚ)+1)

private lemma mass_nonneg (c : ℕ →₀ ℚ) : 0 ≤ mass c := by unfold mass; positivity
private lemma term_nonneg (c : ℕ →₀ ℚ) (n : ℕ) : 0 ≤ term c n := by unfold term; positivity

private lemma coefficient_le_mass (c : ℕ →₀ ℚ) (k : ℕ) : |1-c k| ≤ mass c := by
  refine (abs_sub _ _).trans ?_
  simp only [abs_one, mass, add_le_add_iff_left]
  by_cases h : k ∈ c.support
  · exact single_le_sum (fun i _ => abs_nonneg (c i)) h
  · simp [Finsupp.notMem_support_iff.mp h, sum_nonneg (fun i _ => abs_nonneg (c i))]

private lemma mod_step {n u : ℕ} (hu : 2 ≤ u) (h : ¬u ∣ n+1) :
    (n+1)%u = n%u+1 := by
  have hone : 1%u = 1 := Nat.mod_eq_of_lt (by omega)
  have hne : (n+1)%u ≠ 0 := fun hz => h (Nat.dvd_of_mod_eq_zero hz)
  have hb : n % u < u := Nat.mod_lt _ (by omega)
  have hlt : n%u+1 < u := by
    by_contra! hn
    have he : n%u+1=u := by omega
    apply hne
    rw [Nat.add_mod, hone, he, Nat.mod_self]
  simpa only [hone] using Nat.add_mod_of_add_mod_lt (a:=n) (b:=1) (c:=u) (by simpa only [hone] using hlt)

lemma prime_identity (c : ℕ →₀ ℚ) (k : ℕ) (hp : (k+2).Prime) :
    1 - c k = residual c 1 + residual c (k+1) - residual c (k+2) := by
  classical
  let T (m j : ℕ) := c j * ((m%(j+2):ℕ):ℚ) / ((j+2:ℕ):ℚ)
  have hi (j : ℕ) : T 1 j + T (k+1) j - T (k+2) j = if j=k then c j else 0 := by
    have he : 1%(j+2) = 1 := Nat.mod_eq_of_lt (by omega)
    by_cases hj : j=k
    · subst j
      simp only [T, he, Nat.mod_eq_of_lt (show k+1 < k+2 by omega), Nat.mod_self,
        Nat.cast_zero, Nat.cast_one, mul_zero, zero_div, sub_zero, if_true, mul_one]
      push_cast
      field_simp
      ring
    · have hnd : ¬ j+2 ∣ (k+1)+1 := by
        intro hd
        rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega
      have hm := mod_step (u:=j+2) (by omega) hnd
      simp only [T, he, hm, Nat.cast_one, Nat.cast_add, mul_one, if_neg hj]
      ring
  have hsum := sum_congr (s₁:=c.support) rfl (fun j _ => hi j)
  simp only [sum_sub_distrib,sum_add_distrib] at hsum
  have hv : (∑ j ∈ c.support, if j=k then c j else 0) = c k := by
    by_cases hk : k ∈ c.support
    · simp [hk]
    · simp [hk, Finsupp.notMem_support_iff.mp hk]
  rw [hv] at hsum
  change _ = (1-∑ j ∈ c.support, T 1 j) + (1-∑ j ∈ c.support, T (k+1) j) - (1-∑ j ∈ c.support, T (k+2) j)
  linarith

private lemma sum_le_cost (c : ℕ →₀ ℚ) (H : ℕ) (u : Finset ℕ) (hu : u ⊆ range H) :
    ∑ i ∈ u, term c i ≤ cost c H := by
  apply (sum_le_sum_of_subset_of_nonneg hu (fun i _ _ => term_nonneg c i)).trans
  unfold cost
  linarith [div_nonneg (sq_nonneg (mass c)) (show 0≤(H:ℚ)+1 by positivity)]

private lemma small_cutoff (c : ℕ →₀ ℚ) (H k : ℕ) (D : ℚ) (hD : (H:ℚ)+1 ≤ D) :
    (1-c k)^2 ≤ D * cost c H := by
  have hmass : (1-c k)^2 ≤ (mass c)^2 := by
    have h1 := coefficient_le_mass c k
    nlinarith [sq_abs (1-c k), mul_nonneg (sub_nonneg.mpr h1)
      (add_nonneg (mass_nonneg c) (abs_nonneg (1-c k)))]
  have hhc : (mass c)^2/((H:ℚ)+1) ≤ cost c H := by
    unfold cost
    linarith [sum_nonneg (s:=range H) (fun i _ => term_nonneg c i)]
  have hden : 0 < (H:ℚ)+1 := by positivity
  have hcos : 0 ≤ cost c H := (div_nonneg (sq_nonneg _) hden.le).trans hhc
  exact hmass.trans <| ((div_le_iff₀ hden).mp hhc).trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hD) hcos])

private lemma two_bound (c : ℕ →₀ ℚ) (H : ℕ) :
    (1-c 0)^2 ≤ 14*cost c H := by
  by_cases hh : H < 2
  · apply small_cutoff
    have : (H:ℚ) < 2 := by exact_mod_cast hh
    linarith
  have hsc := sum_le_cost c H {0,1} (by intro i hi; simp at hi; rcases hi with rfl|rfl <;> simp <;> omega)
  have hi := prime_identity c 0 Nat.prime_two
  simp only [zero_add] at hi
  norm_num [term] at hsc
  nlinarith [sq_nonneg (3*residual c 1+2*residual c 2), congrArg (fun x : ℚ => x^2) hi]

private lemma odd_bound (c : ℕ →₀ ℚ) (H t : ℕ) (hp : (t+3).Prime) :
    (1-c (t+1))^2 ≤ (2*((t:ℚ)+3)^2+2)*cost c H := by
  by_cases hH : H < t+3
  · apply small_cutoff
    have h : (H:ℚ) ≤ (t:ℚ)+2 := by exact_mod_cast (show H ≤ t+2 by omega)
    nlinarith [sq_nonneg ((t:ℚ)+2), Nat.cast_nonneg (α:=ℚ) t]
  have hsub : ({0,t+1,t+2}:Finset ℕ) ⊆ range H := by
    intro i hi; simp at hi; rcases hi with rfl|rfl|rfl <;> exact mem_range.mpr (by omega)
  have hu := sum_le_cost c H _ hsub
  simp only [sum_insert (by simp : 0 ∉ ({t+1,t+2} : Finset ℕ)),
    sum_insert (by simp : t+1 ∉ ({t+2}:Finset ℕ)), sum_singleton] at hu
  let F : Fin 3 → ℚ := ![residual c 1, residual c (t+2), -(residual c (t+3))]
  let G : Fin 3 → ℚ := ![2, ((t:ℚ)+2)*(t+3), ((t:ℚ)+3)*(t+4)]
  have Hcs := sq_sum_div_le_sum_sq_div univ F (g:=G) (by intro i _; fin_cases i <;> simp [G] <;> positivity)
  simp only [Fin.sum_univ_three] at Hcs
  have hsumF : F 0 + F 1 + F 2 = 1-c (t+1) := by
    change residual c 1 + residual c (t+2) + -(residual c (t+3)) = _
    simpa only [sub_eq_add_neg] using (prime_identity c (t+1) hp).symm
  have hsumG : G 0 + G 1 + G 2 = 2*((t:ℚ)+3)^2+2 := by dsimp [G]; ring
  have htmu : F 0^2/G 0 + F 1^2/G 1 + F 2^2/G 2 =
      term c 0 + (term c (t+1) + term c (t+2)) := by
    dsimp [F,G,term]
    push_cast
    ring
  rw [hsumF,hsumG,htmu] at Hcs
  have hden : 0 < 2*((t:ℚ)+3)^2+2 := by positivity
  exact ((div_le_iff₀ hden).mp Hcs).trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hu hden.le)

end NymanPrime

theorem solution (c : ℕ →₀ ℚ) (H p : ℕ) (hp : p.Prime) :
    (1 - c (p-2))^2 ≤ (if p=2 then 14 else 2*(p:ℚ)^2+2) *
      ((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ) := by
  change _ ≤ _ * NymanPrime.cost c H
  by_cases h : p = 2
  · subst p; simpa only [Nat.sub_self, if_true] using NymanPrime.two_bound c H
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    obtain ⟨t,ht⟩ := Nat.exists_eq_add_of_le hp3
    have hpt : p=t+3 := by omega
    clear ht
    subst p
    simp only [if_neg h, Nat.cast_add, Nat.cast_ofNat]
    rw [show t+3-2=t+1 by omega]
    exact NymanPrime.odd_bound c H t hp
