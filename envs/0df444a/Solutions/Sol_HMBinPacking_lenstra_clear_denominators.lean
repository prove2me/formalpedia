-- Prove2me | solution 1 for HMBinPacking.lenstra_clear_denominators
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T09:58:58.007271+00:00
-- url     : https://prove2.me/submissions/c5571299-aabc-4dee-a16a-8f822c8d3be2

import Definitions.Def_HMBinPacking_Encoding
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open Finset HMBinPacking
open ExponomialAssortment.FPTAS

private lemma natlen (a : ℕ) : (encodeNat a).length = 2 * a.size + 1 := by
  simp [encodeNat, Nat.size_eq_bits_len]; omega
private lemma intlen (a : ℤ) : (encodeInt a).length = 2 * a.natAbs.size + 2 := by
  simp [encodeInt, natlen]
private lemma ratlen (a : ℚ) : (encodeRat a).length = 2 * a.num.natAbs.size + 2 * a.den.size + 3 := by
  simp [encodeRat, intlen,natlen]; omega
private lemma flattenlen {n : ℕ} (f : Fin n → List Bool) :
    (List.ofFn f).flatten.length = ∑ i, (f i).length := by
  simp [List.sum_ofFn,Function.comp_def]

theorem solution (I : Instance) (r : Fin I.d → Fin I.d) (u : Fin I.d → ℚ) :
    ∃ (q : ℕ) (w : Fin I.d → ℤ), 0 < q ∧ (∀ i, (q : ℚ) * u i = (w i : ℚ)) ∧
      (encodeNat I.d ++ encodeNatVec I.s ++ encodeNat I.B ++ encodeResidue r ++
        encodeIntVec w).length ≤ (I.d + inputLength I + (encVec u).length) ^ 2 := by
  classical
  let t (i : Fin I.d) := ∏ j ∈ univ.erase i, (u j).den
  let w (i : Fin I.d) := (u i).num * (t i : ℤ)
  let D := ∑ j, (u j).den.size
  let E := (encVec u).length
  have he : E = ∑ j, (encodeRat (u j)).length := flattenlen _
  have hd : D ≤ E := by
    rw [he]; apply Finset.sum_le_sum; intro j _; rw [ratlen]; omega
  have hnum (i : Fin I.d) : (u i).num.natAbs.size ≤ E := by
    rw [he]
    have h := Finset.single_le_sum (f := fun j => (encodeRat (u j)).length)
      (fun j (_ : j ∈ univ) => Nat.zero_le _) (Finset.mem_univ i)
    rw [ratlen] at h; omega
  have ht (i) : t i ≤ 2^D := by
    have hle : t i ≤ ∏ j ∈ univ.erase i, 2 ^ (u j).den.size :=
      Finset.prod_le_prod' fun j _ => (Nat.lt_size_self _).le
    rw [Finset.prod_pow_eq_pow_sum] at hle
    exact le_trans hle (Nat.pow_le_pow_right (by decide) (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)))
  have hsize (i) : (w i).natAbs.size ≤ (u i).num.natAbs.size + D := by
    apply Nat.size_le.mpr
    rw [pow_add]; change ((u i).num * (t i : ℤ)).natAbs < _
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self _) (ht i) (by positivity)
  have hwi (i) : (encodeInt (w i)).length ≤ 4 * E + 2 := by
    rw [intlen]; have := hsize i; have := hnum i; omega
  have hw : (encodeIntVec w).length ≤ I.d * (4 * E + 2) := by
    rw [encodeIntVec,flattenlen]
    simpa using Finset.sum_le_sum (s := univ) (fun i _ => hwi i)
  have hl : (encodeNat I.d).length ≤ inputLength I := by
    simp [inputLength,encodeInstance]; omega
  have hr : (encodeResidue r).length ≤ I.d * inputLength I := by
    rw [encodeResidue,encodeNatVec,flattenlen]
    have hri (i) : (encodeNat (r i)).length ≤ inputLength I := by
      apply le_trans _ hl
      simp only [natlen]; have := Nat.size_le_size (r i).isLt.le; omega
    simpa using Finset.sum_le_sum (s := univ) (fun i _ => hri i)
  refine ⟨∏ j, (u j).den, w, Finset.prod_pos (fun i _ => (u i).den_pos), ?_, ?_⟩
  · intro i
    have eqn : (u i).den * t i = ∏ j, (u j).den :=
      Finset.mul_prod_erase univ (fun j => (u j).den) (Finset.mem_univ i)
    have hu : (u i).num / ((u i).den : ℚ) = u i := (u i).num_div_den
    have hden : ((u i).den : ℚ) ≠ 0 := by exact_mod_cast (u i).den_ne_zero
    have hcancel := (div_eq_iff hden).mp hu
    rw [← eqn, Nat.cast_mul]
    simp only [w, Int.cast_mul,Int.cast_natCast]
    linear_combination -(t i : ℚ) * hcancel
  · have hbase : (encodeNat I.d ++ encodeNatVec I.s ++ encodeNat I.B).length ≤ inputLength I := by
      simp [inputLength,encodeInstance]; omega
    simp only [List.length_append] at hbase ⊢
    change _ ≤ (I.d + inputLength I + E)^2
    have hmin : 2*I.d ≤ E := by
      rw [he]
      calc
        _ = ∑ _ : Fin I.d, 2 := by simp [Nat.mul_comm]
        _ ≤ _ := Finset.sum_le_sum (fun i _ => by rw [ratlen]; omega)
    have hlen : 1 ≤ inputLength I := by
      simp [inputLength,encodeInstance,natlen]; omega
    nlinarith [Nat.mul_le_mul_right I.d hmin, Nat.mul_le_mul_right E hmin,
      Nat.mul_le_mul_right I.d hlen, Nat.mul_le_mul_right (inputLength I) hlen,
      Nat.mul_le_mul_right E hlen]
