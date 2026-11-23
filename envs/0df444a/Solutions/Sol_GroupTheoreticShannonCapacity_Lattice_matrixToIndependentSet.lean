-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.matrixToIndependentSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:44:26.566055+00:00
-- url     : https://prove2.me/submissions/8c3e6519-d208-49c7-b86f-314974e2f606

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_latticeQuotient_addSubgroup
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_distMod_eq_canonicalRep_diff
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_exists_canonical_lattice_rep
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_det_mul_eq_pow_of_mul_eq_smul
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_card_latticeQuotient_eq

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Lattice
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity.Lattice
theorem _root_.solution
    (n : ℕ) [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℤ)
    (p q : ℕ) [hp : NeZero p] (hq : 0 < q)
    (hAB : A * B = p • 1)
    (hMinDist : minDistance n (latticeOfMatrix n (A.map (↑· : ℤ → ℝ))) ≥ q) :
    ∃ S : AddSubgroup (Fin n → ZMod p),
      (strongPower (fractionGraph p q) n).IsIndepSet (S : Set (Fin n → ZMod p)) ∧
      Nat.card S ≥ Int.natAbs B.det := by
  -- Get the subgroup from latticeQuotient
  obtain ⟨S, hS⟩ := latticeQuotient_addSubgroup n p A
  use S
  constructor
  · -- Prove S is independent: ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬Adj u v
    -- Proof outline:
    -- 1. u - v ∈ S (subgroup closure)
    -- 2. Get canonical representative w ∈ L(A) with (w i : ZMod p) = (u - v) i and |w_i| ≤ p/2
    -- 3. Since u ≠ v, w ≠ 0, so by minDistance, ‖w‖_∞ ≥ q
    -- 4. Get index i with |w_i| ≥ q
    -- 5. distMod(u_i, v_i) = |w_i| ≥ q (since w is canonical)
    -- 6. Contradict hadj which says distMod < q for differing coordinates
    apply (SimpleGraph.isIndepSet_iff _).2
    intro u hu v hv huv
    simp only [strongPower, fractionGraph]
    intro ⟨_, hadj⟩
    -- Step 1: u - v ∈ latticeQuotient (subgroup property)
    have hu' : u ∈ latticeQuotient n p A := by simpa [hS] using hu
    have hv' : v ∈ latticeQuotient n p A := by simpa [hS] using hv
    have huv_mem : u - v ∈ latticeQuotient n p A := by
      obtain ⟨x, hx⟩ := hu'
      obtain ⟨y, hy⟩ := hv'
      use x - y
      ext i
      simp only [Pi.sub_apply, hx, hy]
      rw [← Finset.sum_sub_distrib]
      congr 1
      ext j
      push_cast
      ring
    -- Step 2: Get canonical representative w ∈ L(A)
    obtain ⟨w, hw_lat, hw_mod, hw_bound, hw_is_canon⟩ :=
      exists_canonical_lattice_rep n p A B hAB (u - v) huv_mem
    -- Step 3: Since u ≠ v, w ≠ 0
    have hw_ne_zero : (fun i => (w i : ℝ)) ≠ 0 := by
      intro heq
      apply huv
      ext i
      have hwi_zero : (w i : ℝ) = 0 := congrFun heq i
      have hwi_int_zero : w i = 0 := by exact_mod_cast hwi_zero
      have : (w i : ZMod p) = (u - v) i := hw_mod i
      simp only [hwi_int_zero, Int.cast_zero, Pi.sub_apply] at this
      exact sub_eq_zero.mp this.symm
    -- Step 4: By minDistance, ‖w‖_∞ ≥ q
    have hinfty_ge_q : inftyNorm n (fun i => (w i : ℝ)) ≥ q := by
      have hw_in_set : inftyNorm n (fun i => (w i : ℝ)) ∈
          { d | ∃ v ∈ latticeOfMatrix n (A.map (↑· : ℤ → ℝ)), v ≠ 0 ∧ d = inftyNorm n v } :=
        ⟨_, hw_lat, hw_ne_zero, rfl⟩
      have hbdd : BddBelow { d | ∃ v ∈ latticeOfMatrix n (A.map (↑· : ℤ → ℝ)),
          v ≠ 0 ∧ d = inftyNorm n v } := by
        use 0
        intro x ⟨v, _, _, hxv⟩
        rw [hxv]
        exact Finset.le_sup'_of_le _ (Finset.mem_univ 0) (abs_nonneg _)
      calc inftyNorm n (fun i => (w i : ℝ))
          ≥ sInf { d | ∃ v ∈ latticeOfMatrix n (A.map (↑· : ℤ → ℝ)), v ≠ 0 ∧ d = inftyNorm n v } :=
            csInf_le hbdd hw_in_set
        _ = minDistance n (latticeOfMatrix n (A.map (↑· : ℤ → ℝ))) := rfl
        _ ≥ q := hMinDist
    -- Step 5: There exists i with |w_i| ≥ q
    simp only [inftyNorm] at hinfty_ge_q
    have ⟨i, hi⟩ : ∃ i : Fin n, |(w i : ℝ)| ≥ q := by
      by_contra h
      push_neg at h
      have hlt : Finset.sup' Finset.univ Finset.univ_nonempty (fun i => |(w i : ℝ)|) < q := by
        rw [Finset.sup'_lt_iff]
        intro i _
        exact h i
      linarith
    -- Step 6: w_i = canonicalRep p ((u-v)_i) - directly from exists_canonical_lattice_rep
    have hwi_is_canon : w i = canonicalRep p ((u - v) i) := hw_is_canon i
    -- Step 7: distMod(u_i, v_i) = |w_i| ≥ q
    have hdist_ge : distMod p (u i) (v i) ≥ q := by
      simp only [Pi.sub_apply] at hwi_is_canon
      rw [distMod_eq_canonicalRep_diff, ← hwi_is_canon]
      have habs_wi : |(w i : ℝ)| ≥ q := hi
      -- Convert |w i| from ℝ to ℕ via natAbs
      have habs_int : (w i).natAbs ≥ q := by
        have h1 : ((w i).natAbs : ℝ) = |(w i : ℝ)| := by
          rw [Nat.cast_natAbs, Int.cast_abs]
        have h2 : ((w i).natAbs : ℝ) ≥ (q : ℝ) := by rw [h1]; exact habs_wi
        exact Nat.cast_le.mp h2
      exact habs_int
    -- Step 8: Since |w_i| ≥ q > 0, w_i ≠ 0, so u_i ≠ v_i
    have hui_ne_vi : u i ≠ v i := by
      intro heq
      have hdist_zero : distMod p (u i) (v i) = 0 := by simp [distMod, heq]
      linarith
    -- Step 9: Contradiction with hadj
    specialize hadj i
    rcases hadj with heq | ⟨_, hlt⟩
    · exact hui_ne_vi heq
    · linarith
  · -- Prove |S| ≥ |det(B)|
    -- Step 1: S as a set equals latticeQuotient
    -- Step 2: Use card_latticeQuotient_eq to get Nat.card (latticeQuotient) = B.det.natAbs
    -- Step 3: Since S = latticeQuotient as sets, their cardinalities are equal
    -- Need: det(A) ≠ 0 (follows from hMinDist > 0, since det = 0 means degenerate lattice)
    have hdetA : A.det ≠ 0 := by
      -- From AB = pI, det(A) * det(B) = p^n ≠ 0, so det(A) ≠ 0
      have hprod := det_mul_eq_pow_of_mul_eq_smul n A B p hAB
      have hp_pos : (0 : ℤ) < p := Int.natCast_pos.mpr (NeZero.pos p)
      have hpow_pos : (0 : ℤ) < (p : ℤ) ^ Fintype.card (Fin n) := pow_pos hp_pos _
      intro hdet_zero
      rw [hdet_zero, zero_mul] at hprod
      omega
    -- The cardinality of S equals cardinality of latticeQuotient (they are equal as sets)
    have hcard_eq : Nat.card S = Nat.card (latticeQuotient n p A) := by
      -- S is a subgroup whose underlying set equals latticeQuotient
      have hset : (S : Set (Fin n → ZMod p)) = latticeQuotient n p A := hS
      -- Nat.card S = Nat.card {x : S} and {x : S} ≃ latticeQuotient via set equality
      have : Nat.card S = Nat.card (S : Set (Fin n → ZMod p)) := rfl
      rw [this, hset]
    -- Apply the lattice quotient cardinality lemma
    rw [hcard_eq]
    rw [card_latticeQuotient_eq n A B p hAB hdetA]
end GroupTheoreticShannonCapacity.Lattice
