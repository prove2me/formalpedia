-- Prove2me | solution 1 for GlobalTheory.RelBasis.indepOn_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:57:43.31022+00:00
-- url     : https://prove2.me/submissions/03ddfb2c-1409-47e9-b03a-dafb1936eb43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IndepOnEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PullbackSectionsBasisOfAffineOpens
import Theorems.Thm_GlobalTheory_RelBasis_comb_res
import Theorems.Thm_GlobalTheory_RelBasis_exists_affine_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.RelBasis
variable {X Y T : Scheme.{0}} {L : LB X} {t : ℤ} {N : ℕ}
namespace GlobalTheory.RelBasis
theorem _root_.solution (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X)
    (H : ∀ W : T.Opens, IsAffineOpen W → IndepOn b p₁ p₂ W) (W : T.Opens) : IndepOn b p₁ p₂ W := by
  intro c hc
  funext k
  refine fn_ext fun x hx => ?_
  obtain ⟨V, hV, hxV, hle⟩ := exists_affine_le W x hx
  have h0 := H V hV (fun k => (T.presheaf.map (homOfLE hle).op).hom (c k)) fun y i h₁ h₂ =>
    (comb_res b p₁ p₂ hle c y i h₁).trans (hc y i (hle h₁) h₂)
  have hk : (T.presheaf.map (homOfLE hle).op).hom (c k) = 0 := congrFun h0 k
  have hxV' : (𝟙 T : T ⟶ T) x ∈ V := hxV
  rw [← gs_res (𝟙 T) x hle hxV', ← gs_res (𝟙 T) x hle hxV', hk, Pi.zero_apply, map_zero]
end GlobalTheory.RelBasis
