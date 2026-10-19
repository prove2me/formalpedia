-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.exists_separable_invariant_subset
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:00:05.58614+00:00
-- url     : https://prove2.me/submissions/195408f8-3c53-45c0-9343-9c034fd87742

import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic

open OAI OAI.ReflexiveFixedPoints
open Set TopologicalSpace
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
/-- One generation step: add images and rational convex combinations. -/
def rfpStep {C : Set X} (F : C → C) (Q : Set X) : Set X :=
  Q ∪ (fun x : C => (F x : X)) '' ((↑) ⁻¹' Q) ∪
    {z | ∃ r : ℚ, 0 < (r : ℝ) ∧ (r : ℝ) < 1 ∧ ∃ x ∈ Q, ∃ y ∈ Q, z = (r : ℝ) • x + (1 - (r : ℝ)) • y}

def rfpGen {C : Set X} (F : C → C) (x0 : X) : ℕ → Set X
  | 0 => {x0}
  | n + 1 => rfpStep F (rfpGen F x0 n)

theorem rfpGen_mono {C : Set X} (F : C → C) (x0 : X) : Monotone (rfpGen F x0) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  intro z hz
  show z ∈ rfpStep F (rfpGen F x0 n)
  exact Or.inl (Or.inl hz)

theorem rfpGen_countable {C : Set X} (F : C → C) (x0 : X) (n : ℕ) : (rfpGen F x0 n).Countable := by
  induction n with
  | zero => exact Set.countable_singleton _
  | succ n ih =>
    show (rfpStep F (rfpGen F x0 n)).Countable
    refine (ih.union ?_).union ?_
    · exact (ih.preimage Subtype.val_injective).image _
    · have : {z | ∃ r : ℚ, 0 < (r : ℝ) ∧ (r : ℝ) < 1 ∧ ∃ x ∈ rfpGen F x0 n, ∃ y ∈ rfpGen F x0 n,
          z = (r : ℝ) • x + (1 - (r : ℝ)) • y} ⊆
          (fun p : ℚ × X × X => (p.1 : ℝ) • p.2.1 + (1 - (p.1 : ℝ)) • p.2.2) ''
            ((Set.univ : Set ℚ) ×ˢ (rfpGen F x0 n ×ˢ rfpGen F x0 n)) := by
        rintro z ⟨r, -, -, x, hx, y, hy, rfl⟩
        exact ⟨(r, x, y), ⟨trivial, hx, hy⟩, rfl⟩
      exact ((Set.countable_univ.prod (ih.prod ih)).image _).mono this

theorem rfpGen_sub {C : Set X} (hconvex : Convex ℝ C) (F : C → C) (x0 : X) (hx0 : x0 ∈ C)
    (n : ℕ) : rfpGen F x0 n ⊆ C := by
  induction n with
  | zero => simpa [rfpGen] using hx0
  | succ n ih =>
    rintro z ((hz | ⟨x, -, rfl⟩) | ⟨r, hr0, hr1, x, hx, y, hy, rfl⟩)
    · exact ih hz
    · exact (F x).2
    · exact hconvex (ih hx) (ih hy) hr0.le (by linarith) (by ring)

theorem solution {C : Set X}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hbounded : Bornology.IsBounded C)
    (hconvex : Convex ℝ C) (F : C → C) (hF : LipschitzWith 1 F) :
    ∃ S : Set X, S ⊆ C ∧ S.Nonempty ∧ IsClosed S ∧ Bornology.IsBounded S ∧
      Convex ℝ S ∧ IsSeparable S ∧ InvariantSubset C F S := by
  obtain ⟨x0, hx0⟩ := hne
  set U := ⋃ n, rfpGen F x0 n
  have hUC : U ⊆ C := Set.iUnion_subset (fun n => rfpGen_sub hconvex F x0 hx0 n)
  have hSC : closure U ⊆ C := closure_minimal hUC hclosed
  -- closure of `U` under the operations
  have hUF : ∀ x : C, (x : X) ∈ U → (F x : X) ∈ U := by
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨n + 1, Or.inl (Or.inr ⟨x, hn, rfl⟩)⟩
  have hUcomb : ∀ r : ℚ, 0 < (r : ℝ) → (r : ℝ) < 1 → ∀ x ∈ U, ∀ y ∈ U,
      (r : ℝ) • x + (1 - (r : ℝ)) • y ∈ U := by
    intro r hr0 hr1 x hx y hy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
    have hn' := rfpGen_mono F x0 (le_max_left n m) hn
    have hm' := rfpGen_mono F x0 (le_max_right n m) hm
    exact Set.mem_iUnion.mpr ⟨max n m + 1, Or.inr ⟨r, hr0, hr1, x, hn', y, hm', rfl⟩⟩
  refine ⟨closure U, hSC, ⟨x0, subset_closure (Set.mem_iUnion.mpr ⟨0, rfl⟩)⟩, isClosed_closure,
    hbounded.subset hSC, ?_, ?_, ?_⟩
  · -- convexity
    intro x hx y hy a b ha hb hab
    have hR : (Set.Icc (0 : ℝ) 1) ⊆ closure (Set.Ioo (0 : ℝ) 1 ∩ Set.range ((↑) : ℚ → ℝ)) := by
      rw [← closure_Ioo (zero_ne_one' ℝ)]
      exact closure_minimal (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo)
        isClosed_closure
    have ha' : a ∈ closure (Set.Ioo (0 : ℝ) 1 ∩ Set.range ((↑) : ℚ → ℝ)) :=
      hR ⟨ha, by linarith⟩
    have hxy : (x, y) ∈ closure (U ×ˢ U) := by
      rw [closure_prod_eq]; exact ⟨hx, hy⟩
    have hb' : b = 1 - a := by linarith
    subst hb'
    have := map_mem_closure₂ (f := fun (t : ℝ) (p : X × X) => t • p.1 + (1 - t) • p.2)
      (u := U) (by fun_prop) ha' hxy (by
        rintro t ⟨⟨ht0, ht1⟩, r, rfl⟩ p ⟨hp1, hp2⟩
        exact hUcomb r ht0 ht1 p.1 hp1 p.2 hp2)
    simpa using this
  · exact ((Set.countable_iUnion (fun n => rfpGen_countable F x0 n)).isSeparable).closure
  · -- invariance
    intro x hx
    have hcont : Continuous (fun x : C => (F x : X)) :=
      continuous_subtype_val.comp hF.continuous
    have hx' : x ∈ closure ((↑) ⁻¹' U : Set C) := by
      rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
        Set.image_preimage_eq_inter_range, Subtype.range_coe, Set.inter_eq_left.mpr hUC]
      exact hx
    exact map_mem_closure (f := fun x : C => (F x : X)) (t := U) hcont hx' (fun y hy => hUF y hy)
