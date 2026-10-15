-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finite_pairwise_comaximal_ideal_CRT
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:13:49.737894+00:00
-- url     : https://prove2.me/submissions/f8dd2742-7036-45f5-a3b6-e3391afc8c05

import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations

theorem solution
    {iota : Type} [DecidableEq iota] {R : Type} [CommRing R]
    (active : Finset iota) (I : iota -> Ideal R)
    (hpair : (i j : iota) -> i ∈ active -> j ∈ active -> Not (i = j) -> I i ⊔ I j = ⊤)
    (localValue : iota -> R) :
    Exists fun P : R => (i : iota) -> i ∈ active -> P - localValue i ∈ I i := by
  classical
  let α := {i : iota // i ∈ active}
  letI : Fintype α := Fintype.ofFinset active (by
    intro x
    simp)
  have hcop : Pairwise (fun x y : α => IsCoprime (I x.val) (I y.val)) := by
    intro x y hxy
    apply Ideal.isCoprime_iff_sup_eq.mpr
    exact hpair x.val y.val x.property y.property (fun h => hxy (Subtype.ext h))
  obtain ⟨P, hP⟩ := Ideal.exists_forall_sub_mem_ideal hcop (fun x : α => localValue x.val)
  refine ⟨P, ?_⟩
  intro i hi
  exact hP ⟨i, hi⟩