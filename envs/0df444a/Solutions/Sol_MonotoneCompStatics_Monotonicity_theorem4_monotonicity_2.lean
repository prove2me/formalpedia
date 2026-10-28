-- Prove2me | solution 2 for MonotoneCompStatics.Monotonicity.theorem4_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:39.255925+00:00
-- url     : https://prove2.me/submissions/cbf78708-d89f-430a-a6fa-a571167edce6

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_MonotoneCompStatics_Monotonicity_argmaxOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_ArgmaxMonotone
import Definitions.Def_MonotoneCompStatics_Monotonicity_SingleCrossing
import Definitions.Def_MonotoneCompStatics_Monotonicity_StrictSingleCrossing
import Theorems.Thm_MonotoneCompStatics_Monotonicity_theorem4_necessity_scp
import Theorems.Thm_MonotoneCompStatics_Monotonicity_theorem4_sufficiency

-- carved verbatim out of submission 297d525e-fe9f-470f-ba63-1257cb06e400, lines 120-129

section
open MonotoneCompStatics.Monotonicity Supermodularity.Lattices

private lemma pair_max {X : Type*} (g : X → ℝ) (a b : X) (h : g b ≤ g a) :
    a ∈ argmaxOn g ({a, b} : Set X) := by
  refine ⟨by simp, ?_⟩
  intro z hz
  rcases (by simpa using hz : z = a ∨ z = b) with rfl | rfl
  · exact le_rfl
  · exact h

private lemma pair_order {X : Type*} [Lattice X] (x y : X) :
    InducedSetOrder ({x ⊓ y, x} : Set X) {y, x ⊔ y} := by
  intro a ha b hb
  have ha' : a = x ⊓ y ∨ a = x := by simpa using ha
  have hb' : b = y ∨ b = x ⊔ y := by simpa using hb
  rcases ha' with rfl | rfl <;>
    rcases hb' with rfl | rfl <;>
    simp [inf_assoc, inf_left_comm, inf_comm, sup_assoc, sup_left_comm, sup_comm]

private lemma qsm_necessary {X : Type*} [Lattice X] (g : X → ℝ)
    (hm : ∀ ⦃A B : Set X⦄, InducedSetOrder A B →
      InducedSetOrder (argmaxOn g A) (argmaxOn g B)) :
    QuasiSupermodularOn g Set.univ := by
  intro x hx y hy
  constructor
  · intro h
    by_contra hn
    have hb := pair_max g y (x ⊔ y) (le_of_lt (lt_of_not_ge hn))
    have ha : x ∈ argmaxOn g ({x ⊓ y, x} : Set X) := by
      simpa [Set.pair_comm] using pair_max g x (x ⊓ y) h
    have hj := (hm (pair_order x y) ha hb).2
    have hh := hj.2 y (by simp)
    exact hn hh
  · intro h
    by_contra hn
    have hb := pair_max g y (x ⊔ y) (le_of_not_gt hn)
    have ha : x ∈ argmaxOn g ({x ⊓ y, x} : Set X) := by
      simpa [Set.pair_comm] using pair_max g x (x ⊓ y) (le_of_lt h)
    have hh := (hm (pair_order x y) ha hb).1
    have hh' := hh.2 x (by simp)
    exact (not_le_of_gt h) hh'

theorem solution {X T : Type*} [Lattice X] [PartialOrder T] (f : X → T → ℝ) :
    ArgmaxMonotone f ↔ (∀ t, QuasiSupermodularOn (fun x => f x t) Set.univ) ∧ SingleCrossing f := by
  constructor
  · intro hm
    exact ⟨fun t => qsm_necessary (fun x => f x t) (fun {_ _} h => hm le_rfl h), MonotoneCompStatics.Monotonicity.theorem4_necessity_scp f hm⟩
  · rintro ⟨hq, hsc⟩
    exact MonotoneCompStatics.Monotonicity.theorem4_sufficiency f hq hsc

end
