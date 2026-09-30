-- Prove2me | solution 1 for LegacyAlgebra.orbitAugmentation
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T06:21:16.928847+00:00
-- url     : https://prove2.me/submissions/6b60337d-686a-4374-a748-bc9d3ec11162

import Mathlib
import Definitions.Def_legacyOrbitAugmentation
set_option autoImplicit false

theorem solution
    (k G X : Type*) [Field k] [Group G] [MulAction G X] [Fintype X] :
    legacyOrbitAugmentation k G X =
        LinearMap.ker (Finsupp.lmapDomain k k
          (Quotient.mk (MulAction.orbitRel G X))) ∧
      Module.finrank k (legacyOrbitAugmentation k G X) =
        Fintype.card X - Nat.card (MulAction.orbitRel.Quotient G X) := by
  classical
  let A := legacyOrbitAugmentation k G X
  let f := Finsupp.lmapDomain k k (Quotient.mk (MulAction.orbitRel G X))
  have hQ (g : G) (x : X) :
      A.mkQ (Finsupp.single (g • x) 1) = A.mkQ (Finsupp.single x 1) := by
    apply (Submodule.Quotient.eq A).mpr
    exact Submodule.subset_span ⟨(g, x), rfl⟩
  let q : MulAction.orbitRel.Quotient G X → ((X →₀ k) ⧸ A) :=
    Quotient.lift (fun x => A.mkQ (Finsupp.single x 1)) (by
      intro x y h
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
      rw [← hg]
      exact hQ g y)
  let L := Finsupp.linearCombination k q
  have hfactor : L.comp f = A.mkQ := by
    apply Finsupp.lhom_ext
    intro x c
    simp only [LinearMap.comp_apply, f, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, L, Finsupp.linearCombination_single]
    change c • A.mkQ (Finsupp.single x 1) = A.mkQ (Finsupp.single x c)
    rw [← map_smul]
    congr 1
    simp [Finsupp.smul_single]
  have hker : A = LinearMap.ker f := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro v ⟨⟨g, x⟩, rfl⟩
      change f (Finsupp.single (g • x) 1 - Finsupp.single x 1) = 0
      have hOrbit : Quotient.mk (MulAction.orbitRel G X) (g • x) =
          Quotient.mk (MulAction.orbitRel G X) x :=
        Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩))
      rw [map_sub]
      simp [f, hOrbit]
    · intro w hw
      change f w = 0 at hw
      have hz : A.mkQ w = 0 := by
        rw [← hfactor, LinearMap.comp_apply, hw, map_zero]
      simpa using hz
  refine ⟨hker, ?_⟩
  letI : Fintype (MulAction.orbitRel.Quotient G X) := Fintype.ofFinite _
  have hsurj : Function.Surjective f := Finsupp.mapDomain_surjective (Quotient.mk_surjective)
  have hdim := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
    Module.finrank_finsupp_self, Module.finrank_finsupp_self, ← hker] at hdim
  change Module.finrank k A = _
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (MulAction.orbitRel.Quotient G X) + Module.finrank k A = Fintype.card X at hdim
  omega
#print axioms solution
