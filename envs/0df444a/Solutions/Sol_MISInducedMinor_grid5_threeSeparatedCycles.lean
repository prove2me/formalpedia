-- Prove2me | solution 1 for MISInducedMinor.grid5_threeSeparatedCycles
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:12:18.516107+00:00
-- url     : https://prove2.me/submissions/9a5a5061-fa57-490c-8e66-08b3de8bdbda

import Definitions.Def_MISInducedMinor_grid5
import Definitions.Def_MISInducedMinor_ThreeSeparatedCycles

set_option autoImplicit false

namespace Aux_MISgrid5

open MISInducedMinor SimpleGraph

def A (x y : Fin 5 × Fin 5) : Prop :=
  (((x.1 : ℕ) + 1 = y.1 ∨ (y.1 : ℕ) + 1 = x.1) ∧ x.2 = y.2) ∨
    (((x.2 : ℕ) + 1 = y.2 ∨ (y.2 : ℕ) + 1 = x.2) ∧ x.1 = y.1)

instance (x y : Fin 5 × Fin 5) : Decidable (A x y) := by unfold A; infer_instance

theorem hadj (x y : Fin 5 × Fin 5) : grid5.Adj x y ↔ A x y := by
  unfold grid5 A
  rw [SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj, SimpleGraph.pathGraph_adj]

instance : DecidableRel grid5.Adj := fun x y => decidable_of_iff _ (hadj x y).symm

theorem ad (x y : Fin 5 × Fin 5) (h : A x y := by decide) : grid5.Adj x y := (hadj x y).2 h

def F : Fin 3 → Finset (Fin 5 × Fin 5) :=
  ![{(0, 0), (0, 1), (1, 0), (1, 1)}, {(0, 3), (0, 4), (1, 3), (1, 4)},
    {(3, 0), (3, 1), (4, 0), (4, 1)}]

def cyc (r c r' c' : Fin 5) (h1 : A (r, c) (r, c') := by decide)
    (h2 : A (r, c') (r', c') := by decide) (h3 : A (r', c') (r', c) := by decide)
    (h4 : A (r', c) (r, c) := by decide) : grid5.Walk (r, c) (r, c) :=
  Walk.cons (ad _ _ h1) (Walk.cons (ad _ _ h2) (Walk.cons (ad _ _ h3)
    (Walk.cons (ad _ _ h4) Walk.nil)))

def C : (a : Fin 3) → Σ v : Fin 5 × Fin 5, grid5.Walk v v
  | 0 => ⟨_, cyc 0 0 1 1⟩
  | 1 => ⟨_, cyc 0 3 1 4⟩
  | 2 => ⟨_, cyc 3 0 4 1⟩

theorem c0 : (cyc 0 0 1 1).IsCycle := by
  unfold cyc; rw [Walk.cons_isCycle_iff, Walk.isPath_def]; decide

theorem c1 : (cyc 0 3 1 4).IsCycle := by
  unfold cyc; rw [Walk.cons_isCycle_iff, Walk.isPath_def]; decide

theorem c2 : (cyc 3 0 4 1).IsCycle := by
  unfold cyc; rw [Walk.cons_isCycle_iff, Walk.isPath_def]; decide

theorem cyc_isCycle (a : Fin 3) : (C a).2.IsCycle := by
  fin_cases a
  exacts [c0, c1, c2]

theorem cyc_supp (a : Fin 3) (x : Fin 5 × Fin 5) : x ∈ F a ↔ x ∈ (C a).2.support := by
  revert x
  fin_cases a <;> decide

-- walks between cycles
def w01 : grid5.Walk (0, 1) (0, 3) := Walk.cons (ad (0,1) (0,2)) (Walk.cons (ad (0,2) (0,3)) Walk.nil)
def w02 : grid5.Walk (1, 0) (3, 0) := Walk.cons (ad (1,0) (2,0)) (Walk.cons (ad (2,0) (3,0)) Walk.nil)
def w12 : grid5.Walk (1, 4) (4, 1) :=
  Walk.cons (ad (1,4) (2,4)) (Walk.cons (ad (2,4) (3,4)) (Walk.cons (ad (3,4) (4,4))
    (Walk.cons (ad (4,4) (4,3)) (Walk.cons (ad (4,3) (4,2)) (Walk.cons (ad (4,2) (4,1)) Walk.nil)))))

end Aux_MISgrid5

open MISInducedMinor Aux_MISgrid5 in
theorem solution : ThreeSeparatedCycles grid5 := by
  refine ⟨fun a => (F a : Set (Fin 5 × Fin 5)), ?_, ?_, ?_, ?_⟩
  · intro a
    exact ⟨(C a).1, (C a).2, cyc_isCycle a, fun x => by
      rw [Finset.mem_coe]; exact cyc_supp a x⟩
  · intro a b hab
    rw [Finset.disjoint_coe]
    revert hab
    revert a b
    decide
  · intro a b hab x hx y hy
    rw [Finset.mem_coe] at hx hy
    revert x y hab
    revert a b
    decide
  · intro a b c hab hac hbc
    simp only [Finset.mem_coe]
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      first
      | exact absurd rfl hab
      | exact absurd rfl hac
      | exact absurd rfl hbc
      | exact ⟨_, by decide, _, by decide, w01, by decide⟩
      | exact ⟨_, by decide, _, by decide, w01.reverse, by decide⟩
      | exact ⟨_, by decide, _, by decide, w02, by decide⟩
      | exact ⟨_, by decide, _, by decide, w02.reverse, by decide⟩
      | exact ⟨_, by decide, _, by decide, w12, by decide⟩
      | exact ⟨_, by decide, _, by decide, w12.reverse, by decide⟩
