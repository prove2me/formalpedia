-- Prove2me | solution 1 for GlobalTheory.ExpUniqFamily.isHolTo_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:02:11.364039+00:00
-- url     : https://prove2.me/submissions/1cc1e235-c066-4af7-9d80-d106f0a9a226

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueLinearLiftUniformisedFibresStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FamilyUnifExpUnique
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.ExpUniqFamily
namespace GlobalTheory.ExpUniqFamily
theorem _root_.solution {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {X : Scheme.{0}} (y : V × W → (Sp ℂ ⟶ X)) (h : IsHolTo (Set.univ ×ˢ Set.univ) y) (b : V) :
    IsHolTo Set.univ (fun z => y (b, z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hd : Differentiable ℂ (fun z : W => (b, z)) := by fun_prop
  refine ⟨?_, ?_⟩
  · have := h1.preimage hd.continuous
    convert this using 1
    ext z
    simp
  · exact h2.comp hd.differentiableOn (fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩)
end GlobalTheory.ExpUniqFamily
