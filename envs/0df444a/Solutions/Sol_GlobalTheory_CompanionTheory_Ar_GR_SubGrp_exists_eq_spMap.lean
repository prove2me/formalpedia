-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.GR.SubGrp.exists_eq_spMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:33.942133+00:00
-- url     : https://prove2.me/submissions/0c9aa0b3-bae5-4315-876e-5435edbacb4c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFlatSubgroupScheme

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.GR GlobalTheory.CompanionTheory.Ar.GR.SubGrp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.Ar.GR.SubGrp
theorem _root_.solution {S B : Type} [CommRing S] [Algebra R S] [CommRing B] [Algebra R B]
    (x : sp (R₀ := R) S ⟶ sp (R₀ := R) B) : ∃ g : B →ₐ[R] S, x = spMap g := by
  obtain ⟨g, hg⟩ := Spec.map_surjective x.left
  have h : Spec.map g ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := hg ▸ Over.w x
  rw [← Spec.map_comp] at h
  exact ⟨⟨g.hom, RingHom.congr_fun (congrArg (·.hom) (Spec.map_injective h))⟩,
    Over.OverMorphism.ext hg.symm⟩
end GlobalTheory.CompanionTheory.Ar.GR.SubGrp
