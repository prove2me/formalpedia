-- Prove2me | solution 1 for GlobalTheory.ZJ.SplitAll.fieldPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:01:44.243658+00:00
-- url     : https://prove2.me/submissions/b24bfcc9-27a1-474c-85aa-298df500ace4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyTorusExtensionOfIsGt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsSemiAbelianOfSplitAll
import Theorems.Thm_GlobalTheory_GtBaseChange_isGt_extBC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGt_of_iso


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
open GlobalTheory GlobalTheory.ZJ
namespace GlobalTheory.ZJ
namespace SplitAll
theorem _root_.solution {Z : Scheme.{0}} {G : Over Z} [GrpObj G] (h : SplitAll G) (K : Type) [Field K]
    (t : Sp K ⟶ Z) : ∃ E : SplitExt (Sp K), E.IsGt ((Over.pullback t).obj G) := by
  obtain ⟨z, r, rfl⟩ : ∃ (z : Z) (r : Sp K ⟶ Sp (Z.residueField z)), t = r ≫ Z.fromSpecResidueField z :=
    ⟨_, _, (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z t).symm⟩
  obtain ⟨E, ⟨d⟩⟩ := h z
  have : IsMonHom (pullCompIso r (Z.fromSpecResidueField z) G).symm.hom :=
    inferInstanceAs (IsMonHom (pullCompIso r (Z.fromSpecResidueField z) G).inv)
  exact ⟨_, isGt_of_iso (pullCompIso r (Z.fromSpecResidueField z) G).symm (GtBaseChange.isGt_extBC r E _ d)⟩
end SplitAll
end GlobalTheory.ZJ
