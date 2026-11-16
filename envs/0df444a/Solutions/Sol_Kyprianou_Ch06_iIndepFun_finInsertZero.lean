-- Prove2me | solution 1 for Kyprianou.Ch06.iIndepFun_finInsertZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:36:21.697118+00:00
-- url     : https://prove2.me/submissions/e2869794-883e-498f-9f04-c3d955ece3bf

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_iIndepFun_of_delete_const_subtype
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

/-- Reinsert a deterministic zero increment into an independent Fin-indexed
family. The nonzero coordinates are reindexed by Fin.succAbove. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (hprob : P Set.univ = 1)
    (n : Nat) (f : Fin (n + 1) → Ω → Real)
    (g : Fin n → Ω → Real) (k : Fin (n + 1))
    (hzero : f k = fun _ => 0)
    (hrel : ∀ j : Fin n, f (k.succAbove j) = g j)
    (hInd : ProbabilityTheory.iIndepFun g P) :
    ProbabilityTheory.iIndepFun f P := by
  classical
  let emb : Fin n → {j : Fin (n + 1) // j ≠ k} :=
    fun j => ⟨k.succAbove j, Fin.succAbove_ne k j⟩
  have hinj : Function.Injective emb := by
    intro a b hab
    apply (k.succAboveOrderEmb).injective
    exact congrArg Subtype.val hab
  have hsurj : Function.Surjective emb := by
    intro j
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq j.property
    exact ⟨i, Subtype.ext hi⟩
  let E : Fin n ≃ {j : Fin (n + 1) // j ≠ k} :=
    Equiv.ofBijective emb ⟨hinj, hsurj⟩
  have haway : ProbabilityTheory.iIndepFun
      (fun j : {j : Fin (n + 1) // j ≠ k} => f j.val) P := by
    have hf := hInd.precomp E.symm.injective
    convert hf using 1
    funext j
    have hj : k.succAbove (E.symm j) = j.val := by
      exact congrArg Subtype.val (E.apply_symm_apply j)
    rw [← hj, hrel]
  exact Kyprianou.Ch06.iIndepFun_of_delete_const_subtype P hprob f k hzero haway
