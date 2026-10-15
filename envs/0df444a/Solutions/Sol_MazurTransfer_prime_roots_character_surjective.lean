-- Prove2me | solution 1 for MazurTransfer.prime_roots_character_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-14T21:54:09.698214+00:00
-- url     : https://prove2.me/submissions/589b2bbc-22ca-4541-858f-55a232a3927a

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a nontrivial homomorphism to prime roots of unity is onto.
Named downstream consumer: actual norm-kernel cyclotomic quotient maps.
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

noncomputable section
theorem solution
    (K G : Type*) [Field K] [Group G] (p : ℕ) [Fact p.Prime] [NeZero p]
    (f : G →* rootsOfUnity p K) (h : ∃ a : G, f a ≠ 1) : Function.Surjective f := by
  obtain ⟨a, ha⟩ := h
  have hne : (f a).val ≠ 1 := by
    intro he
    exact ha (Subtype.ext he)
  have hp : IsPrimitiveRoot (f a).val p :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime (mem_rootsOfUnity p _ |>.mp (f a).property) hne)
  intro z
  obtain ⟨n, _, hn⟩ := hp.eq_pow_of_mem_rootsOfUnity z.property
  refine ⟨a ^ n, ?_⟩
  apply Subtype.ext
  exact (congrArg Subtype.val (map_pow f a n)).trans hn

#print axioms solution
