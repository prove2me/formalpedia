-- Prove2me | solution 1 for LinearOptimization.lp_basic_solutions_finite
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-05T05:42:55.476822+00:00
-- url     : https://prove2.me/submissions/3f735932-985d-4f6d-95e8-c84912f75a9f

import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Definitions.Def_BasicSolution

open Matrix LinearOptimization

/-- The subspace of vectors orthogonal to a fixed `d`. -/
private def orthTo {n : ℕ} (d : Fin n → ℝ) : Submodule ℝ (Fin n → ℝ) where
  carrier := {v | v ⬝ᵥ d = 0}
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq, add_dotProduct] at *
    rw [hu, hv, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c v hv
    simp only [Set.mem_setOf_eq, smul_dotProduct] at *
    rw [hv, smul_zero]

/-- `n` linearly independent constraints pin down at most one point: this is the
uniqueness half of B&T Theorem 2.2. -/
private lemma unique_of_indep {ι : Type} {n : ℕ} (C : ι → LinearConstraint n) (s : Finset ι)
    (hcard : s.card = n) (hli : LinearIndependent ℝ (fun i : s => (C i.1).a))
    {x y : Fin n → ℝ} (hx : ∀ i ∈ s, (C i).a ⬝ᵥ x = (C i).b)
    (hy : ∀ i ∈ s, (C i).a ⬝ᵥ y = (C i).b) : x = y := by
  have hfr : Module.finrank ℝ (Fin n → ℝ) = n := by
    rw [Module.finrank_pi ℝ, Fintype.card_fin]
  have hspan : Submodule.span ℝ (Set.range (fun i : s => (C i.1).a)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_coe, hcard, hfr])
  have hsub : Set.range (fun i : s => (C i.1).a) ⊆ (orthTo (x - y) : Set (Fin n → ℝ)) := by
    rintro w ⟨i, rfl⟩
    show (C i.1).a ⬝ᵥ (x - y) = 0
    rw [dotProduct_sub, hx i.1 i.2, hy i.1 i.2, sub_self]
  have htop : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ orthTo (x - y) := by
    rw [← hspan]; exact Submodule.span_le.mpr hsub
  have : (x - y) ⬝ᵥ (x - y) = 0 := htop (Submodule.mem_top)
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp this)

theorem solution {ι : Type} [Fintype ι] {n : ℕ}
    (C : ι → LinearConstraint n) :
    {x | IsBasicSolution C x}.Finite ∧
    {x | IsBasicFeasibleSolution C x}.Finite := by
  classical
  have key : {x : Fin n → ℝ | IsBasicSolution C x}.Finite := by
    have hsub : {x : Fin n → ℝ | IsBasicSolution C x} ⊆
        ⋃ s ∈ {s : Finset ι | s.card = n ∧ LinearIndependent ℝ (fun i : s => (C i.1).a)},
          {x : Fin n → ℝ | ∀ i ∈ s, (C i).a ⬝ᵥ x = (C i).b} := by
      rintro x ⟨-, s, hcard, hact, hli⟩
      refine Set.mem_biUnion (show s ∈ _ from ⟨hcard, hli⟩) ?_
      intro i hi
      exact hact i hi
    refine Set.Finite.subset (Set.Finite.biUnion (Set.toFinite _) ?_) hsub
    rintro s ⟨hcard, hli⟩
    refine Set.Subsingleton.finite ?_
    intro x hx y hy
    exact unique_of_indep C s hcard hli hx hy
  refine ⟨key, key.subset ?_⟩
  intro x hx
  exact hx.1
