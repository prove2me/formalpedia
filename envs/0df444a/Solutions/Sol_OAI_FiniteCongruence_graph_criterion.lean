-- Prove2me | solution 1 for OAI.FiniteCongruence.graph_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T17:26:21.172697+00:00
-- url     : https://prove2.me/submissions/8bee3d50-428a-4130-9da0-097cb4f71373

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Universal/GraphCriterion.lean:L289-L298
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.FiniteCongruence.graph_criterion.
-- The statement is the platform stub (Theorems.Thm_OAI_FiniteCongruence_graph_criterion) verbatim; the proof is the source proof;
-- inline helpers are the source spans of the proof-only lemmas it needs.
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Hom.Basic
import Definitions.Def_FiniteCongruenceGraph
import Definitions.Def_OAI_Algebra_Universal_Congruence
import Definitions.Def_OAI_Algebra_Universal_GraphCriterion

-- ---- inline helpers from OAI.Algebra.Universal.Congruence ----
namespace OAI

/-!
# Congruences of finite-signature algebras

An algebra has finitely many total operations of finite arity, including possibly nullary
operations. Its congruences are ordered by inclusion. Compatibility with every operation is
equivalent to stability under the unary translations obtained by fixing all but one input.
-/

namespace FiniteCongruence

namespace Congruence

variable {Carrier : Type} {alg : Algebra Carrier}

theorem equality_le (rel : Congruence alg) : equality alg ≤ rel := by
  intro left right equal
  cases equal
  exact rel.refl left

theorem principal_comm (left right : Carrier) :
    principal alg left right = principal alg right left := by
  apply le_antisymm
  · exact principal_le.mpr ((principal alg right left).symm (principal_pair right left))
  · exact principal_le.mpr ((principal alg left right).symm (principal_pair left right))

end Congruence

end FiniteCongruence

end OAI

-- ---- inline helpers from OAI.Algebra.Universal.GraphCriterion ----
namespace OAI

/-!
# Graph characterization of finite congruence lattices

A finite lattice is the full congruence lattice of a nonempty finite algebra if and only if
it admits a finite nonempty lattice-colored graph satisfying `IsGraphWitness`. Principal
congruences supply the colors in one direction; all label-decreasing self-maps supply the
unary operations in the other.
-/

namespace FiniteCongruence

section PrincipalColors

variable {Lat Carrier : Type} [Lattice Lat] [OrderBot Lat] {alg : Algebra Carrier}

theorem map_bot_equality (equiv : Lat ≃o Congruence alg) :
    equiv ⊥ = Congruence.equality alg := by
  apply le_antisymm
  · have : (⊥ : Lat) ≤ equiv.symm (Congruence.equality alg) := bot_le
    simpa using equiv.monotone this
  · exact Congruence.equality_le _

theorem principalColor_eq_bot (equiv : Lat ≃o Congruence alg) (left right : Carrier) :
    principalColor equiv left right = ⊥ ↔ left = right := by
  rw [← le_bot_iff, principalColor_le, map_bot_equality, Congruence.equality_apply]

omit [OrderBot Lat] in
theorem principalColor_triangle (equiv : Lat ≃o Congruence alg) (left right middle : Carrier) :
    principalColor equiv left right ≤
      principalColor equiv left middle ⊔ principalColor equiv middle right := by
  apply (principalColor_le equiv).mpr
  apply (equiv _).trans
  · exact (principalColor_le equiv).mp le_sup_left
  · exact (principalColor_le equiv).mp le_sup_right

omit [OrderBot Lat] in
theorem principalColor_reflect (equiv : Lat ≃o Congruence alg) (lower upper : Lat)
    (notBelow : ¬ lower ≤ upper) :
    ∃ left right, principalColor equiv left right ≤ lower ∧
      ¬ principalColor equiv left right ≤ upper := by
  classical
  by_contra noPair
  apply notBelow
  apply equiv.le_iff_le.mp
  intro left right related
  by_contra notRelated
  exact noPair ⟨left, right, (principalColor_le equiv).mpr related,
    by simpa [principalColor_le] using notRelated⟩

end PrincipalColors

theorem admissible_id {Lat Carrier : Type} [Preorder Lat] (color : Carrier → Carrier → Lat) :
    Admissible color id := fun _ _ => le_rfl

section Forward

variable {Lat Carrier : Type} [Lattice Lat] [OrderBot Lat] {alg : Algebra Carrier}

theorem principalColor_connected (equiv : Lat ≃o Congruence alg)
    (seeds : Finset (Carrier × Carrier)) (left right : Carrier)
    (below : principalColor equiv left right ≤
      seeds.sup (fun edge => principalColor equiv edge.1 edge.2)) :
    Connected (principalColor equiv) seeds left right := by
  have supBelow : seeds.sup (fun edge => principalColor equiv edge.1 edge.2) ≤
      equiv.symm (pathCongruence equiv seeds) := by
    apply Finset.sup_le
    intro edge member
    change equiv.symm (Congruence.principal alg edge.1 edge.2) ≤
      equiv.symm (pathCongruence equiv seeds)
    apply equiv.symm.monotone
    apply Congruence.principal_le.mpr
    exact Relation.EqvGen.rel _ _ ⟨id, admissible_id _, edge, member, rfl, rfl⟩
  have principalBelow : Congruence.principal alg left right ≤ pathCongruence equiv seeds :=
    equiv.symm.le_iff_le.mp (below.trans supBelow)
  exact Congruence.principal_le.mp principalBelow

theorem principalColor_isGraphWitness (equiv : Lat ≃o Congruence alg) :
    IsGraphWitness (principalColor equiv) := by
  refine ⟨?_, principalColor_eq_bot equiv, principalColor_triangle equiv,
    principalColor_reflect equiv, ?_⟩
  · intro left right
    simp only [principalColor, Congruence.principal_comm left right]
  · intro seeds _ left right below
    exact principalColor_connected equiv seeds left right below

end Forward

section Backward

variable {Lat Carrier : Type} [Lattice Lat] [OrderBot Lat] [Fintype Carrier]

end Backward

end FiniteCongruence

end OAI

-- ---- hoisted mission target ----
open OAI OAI.FiniteCongruence

theorem solution (Lat : Type) [Fintype Lat] [Lattice Lat] [OrderBot Lat] :
    Representable Lat ↔ HasGraphWitness Lat := by
  constructor
  · rintro ⟨size, positive, alg, ⟨equiv⟩⟩
    exact ⟨size, positive, principalColor equiv, principalColor_isGraphWitness equiv⟩
  · rintro ⟨size, positive, color, witness⟩
    have : Nonempty (Fin size) := ⟨⟨0, positive⟩⟩
    exact ⟨size, positive, graphAlgebra color, ⟨graphOrderIso color witness⟩⟩
