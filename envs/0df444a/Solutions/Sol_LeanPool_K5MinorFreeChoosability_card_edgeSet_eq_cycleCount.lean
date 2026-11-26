-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.card_edgeSet_eq_cycleCount
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:46:29.425097+00:00
-- url     : https://prove2.me/submissions/a32a5fd2-d0c5-49c2-bf73-321cddfe9463


import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
set_option autoImplicit true


open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} (G : SimpleGraph V)
theorem _root_.solution : Nat.card G.edgeSet = cycleCount (dartSymm G) := by
  classical
  have hsc : ∀ d d' : G.Dart, Equiv.Perm.SameCycle (dartSymm G) d d' ↔ d.edge = d'.edge := by
    intro d d'
    rw [SimpleGraph.dart_edge_eq_iff]
    have hval : ∀ x : G.Dart, dartSymm G x = x.symm := fun x => rfl
    have hsq : dartSymm G ^ (2:ℤ) = 1 := by
      ext1 x
      rw [zpow_two, Equiv.Perm.mul_apply, hval, hval, SimpleGraph.Dart.symm_symm]; rfl
    constructor
    · rintro ⟨k, hk⟩
      rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · have : dartSymm G ^ k = 1 := by
          rw [hj, ← two_mul, zpow_mul, hsq, one_zpow]
        rw [this] at hk; left; simpa using hk
      · have : dartSymm G ^ k = dartSymm G := by
          rw [hj, zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]
        rw [this, hval] at hk; right; rw [← hk, SimpleGraph.Dart.symm_symm]
    · rintro (h | h)
      · rw [h]
      · refine ⟨1, ?_⟩
        rw [zpow_one, hval, h, SimpleGraph.Dart.symm_symm]
  have key : Nat.card G.edgeSet = cycleCount (dartSymm G) := by
    refine (Nat.card_eq_of_bijective (Quotient.lift (s := Equiv.Perm.SameCycle.setoid (dartSymm G))
      (fun d : G.Dart => (⟨d.edge, d.edge_mem⟩ : G.edgeSet))
      (fun a b h => Subtype.ext ((hsc a b).1 h))) ⟨?_, ?_⟩).symm
    · intro a b
      induction a using Quotient.inductionOn
      induction b using Quotient.inductionOn
      intro h
      exact Quotient.sound ((hsc _ _).2 (congrArg Subtype.val h))
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | _ x y => exact ⟨Quotient.mk _ ⟨(x, y), he⟩, rfl⟩
  exact key

