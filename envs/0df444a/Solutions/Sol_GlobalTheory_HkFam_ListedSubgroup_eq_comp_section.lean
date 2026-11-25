-- Prove2me | solution 1 for GlobalTheory.HkFam.ListedSubgroup.eq_comp_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:08:16.50731+00:00
-- url     : https://prove2.me/submissions/ecd14d31-2dca-4f4a-a1e9-fde826d9e9fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_KerScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteEtaleLatticeTorsionHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSubgroupEqRangeOfLists
import Theorems.Thm_GlobalTheory_isClosedImmersion_of_section_of_isSeparated
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
open GlobalTheory GlobalTheory.HkFam GlobalTheory.HkFam.ListedSubgroup
variable {S : Scheme.{0}}
namespace GlobalTheory.HkFam.ListedSubgroup
theorem _root_.solution {X : Scheme.{0}} (f : X ⟶ S) [IsSeparated f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    {k : Type} [Field k] (z : Sp k ⟶ X) (q : Sp k) (hz : z q ∈ Set.range s) : z = (z ≫ f) ≫ s := by
  have := isClosedImmersion_of_section_of_isSeparated f s hs
  have hsurj : Surjective (pullback.fst z s) := by
    refine ⟨fun y => ?_⟩
    obtain rfl : y = q := Subsingleton.elim _ _
    have h : y ∈ Set.range (pullback.fst z s) := by
      rw [Scheme.Pullback.range_fst]
      exact hz
    exact h
  have : IsIso (pullback.fst z s) := isIso_of_isClosedImmersion_of_surjective _
  rw [← cancel_epi (pullback.fst z s)]
  simp only [pullback.condition_assoc, pullback.condition, Category.assoc, reassoc_of% hs]
end GlobalTheory.HkFam.ListedSubgroup
