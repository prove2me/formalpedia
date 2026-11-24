-- Prove2me | solution 1 for GlobalTheory.CubeLawCompare.bijective_app_of_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:02:50.986108+00:00
-- url     : https://prove2.me/submissions/b7158212-fefe-43ba-911c-77de07ee77cb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_RigidityTranslation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocallyTrivialOfIsoPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CubeLawCompare
namespace GlobalTheory.CubeLawCompare
theorem _root_.solution {Y T : Scheme.{0}} (p : Y ⟶ T) (V : T.Opens)
    (h : Function.Bijective (p ∣_ V).appTop.hom) : Function.Bijective (p.app V).hom := by
  have h₁ : IsIso (p ∣_ V).appTop := (ConcreteCategory.isIso_iff_bijective _).2 h
  have h₂ : IsIso (p.app (V.ι ''ᵁ ⊤)) :=
    @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _
      (by rw [eqToHom_op]; exact Y.presheaf.map_isIso (eqToHom _)) h₁ (morphismRestrict_appTop p V).symm
  have e : V.ι ''ᵁ ⊤ = V := V.ι_image_top
  rw [e] at h₂
  exact ConcreteCategory.bijective_of_isIso (p.app V)
end GlobalTheory.CubeLawCompare
