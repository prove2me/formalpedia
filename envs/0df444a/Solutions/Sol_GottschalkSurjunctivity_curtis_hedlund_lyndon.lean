-- Prove2me | solution 1 for GottschalkSurjunctivity.curtis_hedlund_lyndon
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T08:30:50.312625+00:00
-- url     : https://prove2.me/submissions/7b92ca34-362f-439f-9fff-242ea5e08656

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs

namespace GottschalkSurjunctivity

/-- A continuous map from `G → A` (A finite discrete) to a discrete space depends on
finitely many coordinates. -/
theorem CHL_exists_finset {G : Type} (A : Type) [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] {B : Type} [TopologicalSpace B] [DiscreteTopology B]
    (φ : (G → A) → B) (hφ : Continuous φ) :
    ∃ S : Finset G, ∀ x y : G → A, (∀ s ∈ S, x s = y s) → φ x = φ y := by
  have key : ∀ x : G → A, ∃ I : Finset G, ∀ y : G → A, (∀ i ∈ I, y i = x i) → φ y = φ x := by
    intro x
    have ho : IsOpen (φ ⁻¹' {φ x}) := (isOpen_discrete _).preimage hφ
    obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp ho x rfl
    refine ⟨I, fun y hy => ?_⟩
    have : y ∈ (I : Set G).pi u := by
      intro i hi
      rw [hy i hi]
      exact (hu i hi).2
    exact hsub this
  choose I hI using key
  let U : (G → A) → Set (G → A) := fun x => {y | ∀ i ∈ I x, y i = x i}
  have hUo : ∀ x, IsOpen (U x) := by
    intro x
    have : U x = ((I x : Set G)).pi (fun i => {x i}) := by
      ext y; simp [U, Set.mem_pi]
    rw [this]
    exact isOpen_set_pi (I x).finite_toSet (fun _ _ => isOpen_discrete _)
  have hcov : (Set.univ : Set (G → A)) ⊆ ⋃ x, U x := by
    intro y _
    exact Set.mem_iUnion.mpr ⟨y, fun i _ => rfl⟩
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo hcov
  refine ⟨t.biUnion I, fun x y hxy => ?_⟩
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  have h1 : φ x = φ z := hI z x hxz
  have h2 : φ y = φ z := hI z y (fun i hi => by
    rw [← hxy i (Finset.mem_biUnion.mpr ⟨z, hz, hi⟩)]
    exact hxz i hi)
  rw [h1, h2]

end GottschalkSurjunctivity

open GottschalkSurjunctivity in
theorem solution (G : Type) [Group G] (A : Type) [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (τ : (G → A) → (G → A)) :
    (Continuous τ ∧ IsShiftEquivariant G τ) ↔ IsCellularAutomaton G τ := by
  constructor
  · rintro ⟨hc, he⟩
    obtain ⟨S, hS⟩ := CHL_exists_finset A (fun x => τ x 1)
      ((continuous_apply 1).comp hc)
    classical
    let S' : Finset G := insert 1 S
    have h1 : (1 : G) ∈ S' := Finset.mem_insert_self _ _
    refine ⟨S', fun u => τ (fun h => if hh : h ∈ S' then u ⟨h, hh⟩ else u ⟨1, h1⟩) 1,
      fun x g => ?_⟩
    have hg : τ x g = τ (shift G g⁻¹ x) 1 := by
      rw [he]; simp
    rw [hg]
    apply hS
    intro s hs
    have hs' : s ∈ S' := Finset.mem_insert_of_mem hs
    simp [hs', shift]
  · rintro ⟨S, μ, hμ⟩
    refine ⟨?_, ?_⟩
    · apply continuous_pi
      intro g
      have : (fun x : G → A => τ x g) = fun x => μ (fun s => x (g * (s : G))) := by
        funext x; exact hμ x g
      rw [this]
      exact continuous_of_discreteTopology.comp
        (continuous_pi fun s => continuous_apply _)
    · intro g x
      funext h
      rw [hμ]
      simp only [shift_apply]
      rw [hμ]
      simp [mul_assoc]
