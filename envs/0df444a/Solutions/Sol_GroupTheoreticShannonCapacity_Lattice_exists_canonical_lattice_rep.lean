-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.exists_canonical_lattice_rep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:41:01.606078+00:00
-- url     : https://prove2.me/submissions/2159fe9d-ad55-4b67-a529-73cd98178334

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_canonicalRep_coe
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_abs_canonicalRep_le
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_latticeOfMatrix_add_pZ

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Lattice
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity.Lattice
theorem _root_.solution (n : ℕ) [NeZero n] (p : ℕ) [hp : NeZero p]
    (A B : Matrix (Fin n) (Fin n) ℤ) (hAB : A * B = p • 1)
    (x : Fin n → ZMod p) (hx : x ∈ latticeQuotient n p A) :
    ∃ v : Fin n → ℤ,
      (fun i => (v i : ℝ)) ∈ latticeOfMatrix n (A.map (↑· : ℤ → ℝ)) ∧
      (∀ i, (v i : ZMod p) = x i) ∧
      (∀ i, |v i| ≤ p / 2) ∧
      (∀ i, v i = canonicalRep p (x i)) := by
  -- The canonical representative vector
  let v : Fin n → ℤ := canonicalRepVec n p x
  use v
  constructor
  · -- v ∈ L(A): This follows from x ∈ latticeQuotient and pℤ^n ⊆ L(A)
    -- Get the initial lattice representative w = A * y where x = w mod p
    obtain ⟨y, hy⟩ := hx
    let w : Fin n → ℤ := fun i => ∑ j, A i j * y j
    -- w is in the lattice
    have hw : (fun i => (w i : ℝ)) ∈ latticeOfMatrix n (A.map (↑· : ℤ → ℝ)) := by
      use y
      ext i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, w, Int.cast_sum, Int.cast_mul]
    -- v ≡ w (mod p), so v - w is divisible by p
    have hvw_mod : ∀ i, (v i : ZMod p) = (w i : ZMod p) := by
      intro i
      have hvi : (v i : ZMod p) = x i := canonicalRep_coe p (x i)
      have hwi : (w i : ZMod p) = x i := by
        simp only [w, Int.cast_sum, Int.cast_mul]
        rw [hy]
      rw [hvi, hwi]
    -- p divides v i - w i for each i
    have hdiv : ∀ i, (p : ℤ) ∣ (v i - w i) := by
      intro i
      have h := hvw_mod i
      rw [← sub_eq_zero] at h
      rw [← Int.cast_sub] at h
      exact ZMod.intCast_zmod_eq_zero_iff_dvd (v i - w i) p |>.mp h
    -- Define k such that v i = w i + p * k i
    let k : Fin n → ℤ := fun i => (v i - w i) / p
    have hk : ∀ i, v i = w i + p * k i := by
      intro i
      have hdivi := hdiv i
      simp only [k]
      have h := Int.ediv_mul_cancel hdivi
      linarith
    -- v = w + p * k, and since w ∈ L(A) and p * k ∈ L(A), we have v ∈ L(A)
    have hv_eq : (fun i => (v i : ℝ)) = (fun i => ((w i + p * k i) : ℝ)) := by
      ext i
      simp only [hk i, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [hv_eq]
    exact latticeOfMatrix_add_pZ n A B p hAB w hw k
  constructor
  · -- (v i : ZMod p) = x i
    intro i
    exact canonicalRep_coe p (x i)
  constructor
  · -- |v i| ≤ p / 2
    intro i
    exact abs_canonicalRep_le p (x i)
  · -- v i = canonicalRep p (x i)
    intro i
    rfl
end GroupTheoreticShannonCapacity.Lattice
