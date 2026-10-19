-- Prove2me | solution 1 for GreenTao.affine_window_varnavides
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T20:39:08.590164+00:00
-- url     : https://prove2.me/submissions/52623dcc-fc4f-4484-928b-ccab08cba02b

import Definitions.Def_GreenTao_Pseudorandom
import Mathlib

open scoped BigOperators Topology
open Filter GreenTao

theorem solution (k L : ℕ) (hk : 3 ≤ k) (hkL : k ≤ L)
    (δ : ℝ) (hδ : 0 < δ)
    (hinterval : ∀ S : Finset ℕ, S ⊆ Finset.range L →
      δ / 2 * (L : ℝ) ≤ (S.card : ℝ) →
      ∃ a d : ℕ, 0 < d ∧ a + (k - 1) * d < L ∧ ∀ j < k, a + j * d ∈ S)
    (m : ℕ+) (hm : Nat.Prime (m : ℕ)) (hLm : L ≤ (m : ℕ))
    (A : Finset (ZMod (m : ℕ))) (hA : δ * (m : ℝ) ≤ (A.card : ℝ)) :
    δ / (2 * (L : ℝ) ^ 2) ≤
      GreenTao.apAvg k (fun x => if x ∈ A then 1 else 0) := by
  classical
  letI : Fact (Nat.Prime (m : ℕ)) := ⟨hm⟩
  have hLpos : 0 < L := by omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast m.pos
  let W : ZMod (m : ℕ) × ZMod (m : ℕ) → Finset ℕ :=
    fun p => (Finset.range L).filter (fun i => p.1 + (i : ZMod (m : ℕ)) * p.2 ∈ A)
  let G : Finset (ZMod (m : ℕ) × ZMod (m : ℕ)) :=
    Finset.univ.filter (fun p => δ / 2 * (L : ℝ) ≤ ((W p).card : ℝ))
  let P : Finset (ZMod (m : ℕ) × ZMod (m : ℕ)) :=
    Finset.univ.filter (fun q => ∀ j : Fin k, q.1 + (j.val : ZMod (m : ℕ)) * q.2 ∈ A)
  have htranslate (c : ZMod (m : ℕ)) :
      (∑ x : ZMod (m : ℕ), if x + c ∈ A then (1 : ℝ) else 0) = A.card := by
    calc
      _ = ∑ x : ZMod (m : ℕ), if x ∈ A then (1 : ℝ) else 0 :=
        Equiv.sum_comp (Equiv.addRight c) _
      _ = _ := by simp
  have htotal : (∑ p : ZMod (m : ℕ) × ZMod (m : ℕ), ((W p).card : ℝ)) =
      (L : ℝ) * (m : ℝ) * (A.card : ℝ) := by
    simp only [W, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (ZMod (m : ℕ))))
      (t := Finset.range L)]
    simp_rw [htranslate]
    simp [ZMod.card]
    ring
  have hupper (p : ZMod (m : ℕ) × ZMod (m : ℕ)) :
      ((W p).card : ℝ) ≤ δ / 2 * (L : ℝ) + if p ∈ G then (L : ℝ) else 0 := by
    by_cases hp : p ∈ G
    · have hcard : (W p).card ≤ L := by
        exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
      have hcard' : ((W p).card : ℝ) ≤ L := by exact_mod_cast hcard
      simp only [if_pos hp]
      have hnonneg : 0 ≤ δ / 2 * (L : ℝ) := by positivity
      linarith
    · have hnot : ¬ δ / 2 * (L : ℝ) ≤ ((W p).card : ℝ) := by
        simpa [G] using hp
      simp only [if_neg hp, add_zero]
      exact (lt_of_not_ge hnot).le
  have htotalupper : (∑ p : ZMod (m : ℕ) × ZMod (m : ℕ), ((W p).card : ℝ)) ≤
      δ / 2 * (L : ℝ) * (m : ℝ) ^ 2 + (L : ℝ) * (G.card : ℝ) := by
    calc
      _ ≤ ∑ p : ZMod (m : ℕ) × ZMod (m : ℕ),
          (δ / 2 * (L : ℝ) + if p ∈ G then (L : ℝ) else 0) :=
        Finset.sum_le_sum (fun p _ => hupper p)
      _ = _ := by simp [Finset.sum_add_distrib, ZMod.card, pow_two]; ring
  have hgood : δ / 2 * (m : ℝ) ^ 2 ≤ (G.card : ℝ) := by
    rw [htotal] at htotalupper
    have hlower := mul_le_mul_of_nonneg_left hA (show 0 ≤ (L : ℝ) * (m : ℝ) by positivity)
    have hh : (L : ℝ) * (δ / 2 * (m : ℝ) ^ 2) ≤ (L : ℝ) * (G.card : ℝ) := by
      nlinarith
    exact le_of_mul_le_mul_left hh hLr
  have hlocal (p : G) : ∃ a d : ℕ, 0 < d ∧ a + (k - 1) * d < L ∧
      ∀ j < k, a + j * d ∈ W p.val := by
    apply hinterval
    · exact Finset.filter_subset _ _
    · exact (Finset.mem_filter.mp p.property).2
  choose a d hd hlast hap using hlocal
  have haL (p : G) : a p < L := by have := hlast p; omega
  have hdL (p : G) : d p < L := by
    have hh : d p ≤ (k - 1) * d p := Nat.le_mul_of_pos_left _ (by omega)
    have := hlast p
    omega
  let F : G → P × Fin L × Fin L := fun p =>
    (⟨(p.val.1 + (a p : ZMod (m : ℕ)) * p.val.2,
        (d p : ZMod (m : ℕ)) * p.val.2), by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro j
      have hh := (Finset.mem_filter.mp (hap p j.val j.isLt)).2
      convert hh using 1 <;> push_cast <;> ring⟩,
      ⟨a p, haL p⟩, ⟨d p, hdL p⟩)
  have hFinj : Function.Injective F := by
    intro p q hpq
    have heqa : a p = a q := congrArg (fun z : P × Fin L × Fin L => z.2.1.val) hpq
    have heqd : d p = d q := congrArg (fun z : P × Fin L × Fin L => z.2.2.val) hpq
    have heqstep : (d p : ZMod (m : ℕ)) * p.val.2 =
        (d q : ZMod (m : ℕ)) * q.val.2 :=
      congrArg (fun z : P × Fin L × Fin L => z.1.val.2) hpq
    have hdne : (d p : ZMod (m : ℕ)) ≠ 0 := by
      intro hz
      have hdiv : (m : ℕ) ∣ d p := (ZMod.natCast_eq_zero_iff _ _).mp hz
      have hle := Nat.le_of_dvd (hd p) hdiv
      have := hdL p
      omega
    have heqr : p.val.2 = q.val.2 := by
      apply mul_left_cancel₀ hdne
      simpa only [heqd] using heqstep
    have heqstart : p.val.1 + (a p : ZMod (m : ℕ)) * p.val.2 =
        q.val.1 + (a q : ZMod (m : ℕ)) * q.val.2 :=
      congrArg (fun z : P × Fin L × Fin L => z.1.val.1) hpq
    have heqx : p.val.1 = q.val.1 := by
      rw [heqa, heqr] at heqstart
      exact add_right_cancel heqstart
    exact Subtype.ext (Prod.ext heqx heqr)
  have hcard : G.card ≤ P.card * L ^ 2 := by
    have hh := Fintype.card_le_of_injective F hFinj
    simpa [Fintype.card_prod, pow_two, mul_assoc] using hh
  have hprod (x r : ZMod (m : ℕ)) :
      (∏ j : Fin k, if x + (j.val : ZMod (m : ℕ)) * r ∈ A then (1 : ℝ) else 0) =
        if ∀ j : Fin k, x + (j.val : ZMod (m : ℕ)) * r ∈ A then 1 else 0 := by
    by_cases hh : ∀ j : Fin k, x + (j.val : ZMod (m : ℕ)) * r ∈ A
    · simp [hh]
    · rw [if_neg hh]
      push_neg at hh
      obtain ⟨j, hj⟩ := hh
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
  have hcount : (∑ x : ZMod (m : ℕ), ∑ r : ZMod (m : ℕ),
      if ∀ j : Fin k, x + (j.val : ZMod (m : ℕ)) * r ∈ A then (1 : ℝ) else 0) =
      (P.card : ℝ) := by
    calc
      _ = ∑ q : ZMod (m : ℕ) × ZMod (m : ℕ),
          if ∀ j : Fin k, q.1 + (j.val : ZMod (m : ℕ)) * q.2 ∈ A then (1 : ℝ) else 0 :=
        (Fintype.sum_prod_type _).symm
      _ = _ := by simp [P]
  have havg : GreenTao.apAvg k (fun x => if x ∈ A then 1 else 0) =
      (P.card : ℝ) / (m : ℝ) ^ 2 := by
    simp only [GreenTao.apAvg, GreenTao.avg, ZMod.card, hprod, ← Finset.mul_sum]
    rw [hcount]
    field_simp
  rw [havg]
  have hcardr : (G.card : ℝ) ≤ (P.card : ℝ) * (L : ℝ) ^ 2 := by exact_mod_cast hcard
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * (L : ℝ) ^ 2)
    (by positivity : 0 < (m : ℝ) ^ 2)).mpr
  nlinarith [hgood.trans hcardr]
