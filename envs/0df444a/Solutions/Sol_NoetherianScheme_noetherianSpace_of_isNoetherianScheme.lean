-- Prove2me | solution 1 for NoetherianScheme.noetherianSpace_of_isNoetherianScheme
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:18:46.348645+00:00
-- url     : https://prove2.me/submissions/627be0c7-f2e9-49f9-a837-1f40fd2c81e2

import Mathlib
import Definitions.Def_NoetherianScheme_defs

universe u

open AlgebraicGeometry NumberField

namespace NSBridge
open NoetherianScheme

lemma exists_affine (X : Scheme.{u}) (x : X) : ∃ V ∈ X.affineOpens, x ∈ V := by
  obtain ⟨V, hV, hxV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x)
    isOpen_univ
  obtain ⟨W, hW, rfl⟩ := hV
  exact ⟨W, hW, hxV⟩

lemma locN_iff (X : Scheme.{u}) : IsLocallyNoetherianScheme X ↔ IsLocallyNoetherian X := by
  constructor
  · intro h
    choose U hU hxU hN using h
    refine isLocallyNoetherian_of_affine_cover (S := fun x => ⟨U x, hU x⟩) ?_ hN
    rw [eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩
  · intro h x
    obtain ⟨V, hV, hxV⟩ := exists_affine X x
    exact ⟨V, hV, hxV, IsLocallyNoetherian.component_noetherian ⟨V, hV⟩⟩

lemma noeth_iff (X : Scheme.{u}) : IsNoetherianScheme X ↔ IsNoetherian X := by
  constructor
  · rintro ⟨s, hs, hcov⟩
    let S : s → X.affineOpens := fun U => ⟨U.1, (hs U.1 U.2).1⟩
    have hS : (⨆ i, S i : X.Opens) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨U, hU, hxU⟩ := hcov x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU⟩, hxU⟩
    exact (isNoetherian_iff_of_finite_iSup_eq_top hS).2 fun i => (hs i.1 i.2).2
  · intro h
    classical
    choose V hV hxV using exists_affine X
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
      (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
    refine ⟨t.image V, ?_, ?_⟩
    · intro U hU
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hU
      exact ⟨hV x, IsLocallyNoetherian.component_noetherian ⟨V x, hV x⟩⟩
    · intro x
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
      exact ⟨V y, Finset.mem_image_of_mem V hy, hxy⟩

end NSBridge

open NoetherianScheme NSBridge in
theorem solution (X : Scheme.{u}) (hX : IsNoetherianScheme X) :
    TopologicalSpace.NoetherianSpace X := by
  rw [noeth_iff] at hX
  infer_instance
