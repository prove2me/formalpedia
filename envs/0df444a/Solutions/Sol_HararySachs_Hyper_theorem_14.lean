-- Prove2me | solution 1 for HararySachs.Hyper.theorem_14
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T03:13:15.091603+00:00
-- url     : https://prove2.me/submissions/8ea6833f-99d5-48f9-a7a7-e90aba50e792
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Veblen
import Theorems.Thm_HararySachs_Hyper_trace_identity
import Theorems.Thm_HararySachs_Hyper_lemma_13

open HararySachs.Hyper
open Classical

namespace Thm14Aux

variable {n : ℕ}

/-- `allMultisets E j` is exactly the set of multisets of `j` edges drawn from `E`. -/
lemma mem_allMultisets (E : Finset (Finset (Fin n))) (j : ℕ) (S : MultiGraph n) :
    S ∈ allMultisets E j ↔ S.card = j ∧ ∀ e ∈ S, e ∈ E := by
  unfold allMultisets
  rw [Finset.mem_image]
  constructor
  · rintro ⟨f, -, rfl⟩
    refine ⟨by simp, ?_⟩
    intro e he
    rw [Multiset.mem_coe, List.mem_ofFn] at he
    obtain ⟨i, rfl⟩ := he
    exact (f i).2
  · rintro ⟨rfl, hS⟩
    refine ⟨fun i => ⟨S.toList.get ⟨i, by simp⟩,
      hS _ (Multiset.mem_toList.mp (List.get_mem _ _))⟩, Finset.mem_univ _, ?_⟩
    conv_rhs => rw [← Multiset.coe_toList S]
    congr 1
    apply List.ext_get (by simp)
    intro p h1 h2
    simp

/-- `tuples E d m` is exactly the set of `m`-tuples of multisets of at most `d` edges of `E`. -/
lemma mem_tuples (E : Finset (Finset (Fin n))) (d m : ℕ) (T : Fin m → MultiGraph n) :
    T ∈ tuples E d m ↔ ∀ i, (T i).card ≤ d ∧ ∀ e ∈ T i, e ∈ E := by
  unfold tuples
  rw [Finset.mem_image]
  constructor
  · rintro ⟨f, -, rfl⟩ i
    refine ⟨?_, ?_⟩
    · have := (f i).1.isLt
      simp only [toMulti, Multiset.coe_card, List.length_ofFn]
      omega
    · intro e he
      simp only [toMulti, Multiset.mem_coe, List.mem_ofFn] at he
      obtain ⟨p, rfl⟩ := he
      exact ((f i).2 p).2
  · intro h
    have hex : ∀ i, ∃ a : SizedEdges E d, toMulti a = T i := by
      intro i
      have hmem := (mem_allMultisets E _ (T i)).mpr ⟨rfl, (h i).2⟩
      unfold allMultisets at hmem
      obtain ⟨f, -, hf⟩ := Finset.mem_image.mp hmem
      exact ⟨⟨⟨(T i).card, by have := (h i).1; omega⟩, f⟩, hf⟩
    choose g hg using hex
    exact ⟨g, Finset.mem_univ _, funext hg⟩

end Thm14Aux

open Thm14Aux in
theorem solution (n k d : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (E : Finset (Finset (Fin n))) (hE : ∀ e ∈ E, e.card = k)
    (hd1 : 1 ≤ d) (hdt : d ≤ n * (k - 1) ^ (n - 1))
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) :
    codegCoeff (k := k) E res d =
      ∑ m ∈ Finset.Icc 1 d,
        (-((k : ℚ) - 1) ^ n) ^ m / (Nat.factorial m : ℚ) *
          ∑ T ∈ (tuples E d m).filter (fun T =>
              (∑ i, (T i).card) = d ∧
              ∀ i, IsVeblen (T i) k ∧ HararySachs.Hyper.IsConnected (T i)),
            ∏ i, assocCoeff (T i) := by
  -- Step 0: the resultant–trace identity (milestone `trace_identity`).
  rw [trace_identity n k d hk hn E hE hd1 hdt res hres]
  unfold schurP
  rw [if_neg (by omega)]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  set c : ℚ := -((k : ℚ) - 1) ^ n with hc
  set V : ℕ → Finset (MultiGraph n) := fun j =>
    (allMultisets E j).filter (fun S => IsVeblen S k ∧ HararySachs.Hyper.IsConnected S) with hV
  -- Step 1: Lemma 13 turns each normalized trace into a sum over connected Veblen infragraphs.
  have ht : ∀ j : ℕ, 1 ≤ j →
      -(Tr (k := k) E j) / (j : ℚ) = c * ∑ S ∈ V j, assocCoeff S := by
    intro j hj
    rw [lemma_13 n k j hk hn E hE hj]
    have : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    field_simp
    ring
  -- Step 2: expand each product of sums into a sum over tuples.
  have step1 : ∀ a : Fin m → Fin (d + 1),
      (if (∀ i, 0 < (a i).val) ∧ (∑ i, (a i).val) = d then
          (∏ i, -(Tr (k := k) E (a i).val) / ((a i).val : ℚ)) / (Nat.factorial m : ℚ)
        else 0) =
      c ^ m / (Nat.factorial m : ℚ) *
        (if (∀ i, 0 < (a i).val) ∧ (∑ i, (a i).val) = d then
          ∑ T ∈ Fintype.piFinset (fun i => V (a i).val), ∏ i, assocCoeff (T i)
        else 0) := by
    intro a
    split_ifs with h
    · rw [Finset.prod_congr rfl (fun i _ => ht _ (h.1 i)), Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_univ_sum]
      ring
    · simp
  rw [Finset.sum_congr rfl (fun a _ => step1 a), ← Finset.mul_sum]
  congr 1
  -- Step 3: a tuple of connected Veblen infragraphs determines its edge-count composition.
  rw [← Finset.sum_filter, ← Finset.sum_biUnion]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext T
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.mem_piFinset, hV, mem_tuples, mem_allMultisets]
    constructor
    · rintro ⟨a, ⟨hpos, hsum⟩, hT⟩
      have hcard : ∀ i, (T i).card = (a i).val := fun i => (hT i).1.1
      refine ⟨fun i => ⟨by rw [hcard]; have := (a i).isLt; omega, (hT i).1.2⟩, ?_,
        fun i => (hT i).2⟩
      simp only [hcard]
      exact hsum
    · rintro ⟨hT, hsum, hVC⟩
      have hle : ∀ i, (T i).card ≤ d := fun i => (hT i).1
      refine ⟨fun i => ⟨(T i).card, by have := hle i; omega⟩, ⟨fun i => ?_, hsum⟩,
        fun i => ⟨⟨rfl, (hT i).2⟩, hVC i⟩⟩
      exact Multiset.card_pos.mpr (hVC i).2.1
  · intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro T hTa hTb
    apply hab
    funext i
    rw [Fintype.mem_piFinset] at hTa hTb
    apply Fin.ext
    have h1 := ((mem_allMultisets E _ _).mp (Finset.mem_filter.mp (hTa i)).1).1
    have h2 := ((mem_allMultisets E _ _).mp (Finset.mem_filter.mp (hTb i)).1).1
    omega
