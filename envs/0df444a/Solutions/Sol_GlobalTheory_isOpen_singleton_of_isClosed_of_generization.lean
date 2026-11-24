-- Prove2me | solution 1 for GlobalTheory.isOpen_singleton_of_isClosed_of_generization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:04:52.346488+00:00
-- url     : https://prove2.me/submissions/ed91e6c6-c37a-4aef-b011-0c08a9dc5893

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiFiniteAtAffineSpaceHomOfVectorOfCoord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X : Scheme.{0}} [IsLocallyNoetherian X] (x : X)
    (hx : IsClosed ({x} : Set X)) (h : ∀ y, y ⤳ x → y = x) : IsOpen ({x} : Set X) := by
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  have hemb := (X.affineCover.f i).isOpenEmbedding
  rw [← Set.image_singleton, ← hemb.isOpen_iff_image_isOpen]
  have hN : IsLocallyNoetherian (X.affineCover.X i) := isLocallyNoetherian_of_isOpenImmersion (X.affineCover.f i)
  have hA : IsAffine (X.affineCover.X i) := inferInstance
  have : IsNoetherian (X.affineCover.X i) := {}
  have hcl : IsClosed ({y} : Set (X.affineCover.X i)) := by
    have := hx.preimage hemb.continuous
    rwa [← Set.image_singleton, Set.preimage_image_eq _ hemb.injective] at this
  have hgen : ∀ z, z ⤳ y → z = y := fun z hz => hemb.injective (h _ (hz.map hemb.continuous))
  clear hx h hemb
  generalize X.affineCover.X i = Y at *
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Y)
  have hc : IsClosed (⋃ Z ∈ {Z ∈ irreducibleComponents Y | y ∉ Z}, Z) :=
    (hfin.subset (Set.sep_subset _ _)).isClosed_biUnion
      fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  convert hc.isOpen_compl using 1
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
  constructor
  · rintro rfl Z hZ hz
    exact hZ.2 hz
  · intro H
    have hm := irreducibleComponent_mem_irreducibleComponents z
    have hy : y ∈ irreducibleComponent z := by
      by_contra hy
      exact H _ ⟨hm, hy⟩ mem_irreducibleComponent
    have hg := (isIrreducible_irreducibleComponent (x := z)).isGenericPoint_genericPoint
      isClosed_irreducibleComponent
    have e := hgen _ (hg.specializes hy)
    rw [e] at hg
    have : z ∈ closure {y} := by
      rw [hg.def]; exact mem_irreducibleComponent
    rwa [hcl.closure_eq] at this
end GlobalTheory
