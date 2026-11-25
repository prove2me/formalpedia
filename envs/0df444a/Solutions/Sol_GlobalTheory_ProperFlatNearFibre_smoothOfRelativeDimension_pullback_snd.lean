-- Prove2me | solution 1 for GlobalTheory.ProperFlatNearFibre.smoothOfRelativeDimension_pullback_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:02:43.777799+00:00
-- url     : https://prove2.me/submissions/92234f4c-e389-4c3c-8bad-405cc21cbecd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionAndGeometricallyConnect
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsOpensSmoothOfRelativeDimensionOfFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.ProperFlatNearFibre
namespace GlobalTheory.ProperFlatNearFibre
theorem _root_.solution {Z T S : Scheme.{0}} (s : Z ⟶ S) (t : T ⟶ S)
    (g : ℕ) (h : ∀ (z : Z) (w : T), s z = t w →
      ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s)) :
    SmoothOfRelativeDimension g (pullback.snd s t) := by
  let V : {W : Z.Opens // SmoothOfRelativeDimension g (W.ι ≫ s)} → (pullback s t).Opens :=
    fun W => pullback.fst s t ⁻¹ᵁ W.1
  have htop : iSup V = ⊤ := by
    rw [← top_le_iff]
    intro y _
    obtain ⟨W, hW, hW'⟩ := h (pullback.fst s t y) (pullback.snd s t y) (by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition])
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} g) V htop
    fun W => ?_
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension.{0} g)
    ((isPullback_morphismRestrict (pullback.fst s t) W.1).paste_vert
      (IsPullback.of_hasPullback s t)) W.2
end GlobalTheory.ProperFlatNearFibre
