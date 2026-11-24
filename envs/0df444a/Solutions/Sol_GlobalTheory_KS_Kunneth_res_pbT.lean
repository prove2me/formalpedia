-- Prove2me | solution 1 for GlobalTheory.KS.Kunneth.res_pbT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:27:19.52731+00:00
-- url     : https://prove2.me/submissions/c300db03-26d9-400b-b049-4fd208285832

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDualFamilyModSubspace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCovers
import Theorems.Thm_GlobalTheory_KS_Kunneth_pbT_of_le
import Theorems.Thm_GlobalTheory_KS_Kunneth_rsT_of_le

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Kunneth
namespace GlobalTheory.KS.Kunneth
theorem _root_.solution {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ O₁ : Y.Opens} (s : Γ(Y, O₀)) {O O' : Z.Opens}
    (h : O ≤ f ⁻¹ᵁ O₀) (h' : O' ≤ O) (h₁ : O₁ ≤ O₀) (h₂ : O' ≤ f ⁻¹ᵁ O₁) :
    resG Z h' (pbT f s O) = pbT f (rsT s O₁) O' := by
  rw [pbT_of_le f s h, rsT_of_le s h₁, pbT_of_le f _ h₂]
  show (f.appLE O₀ O h ≫ Z.presheaf.map (homOfLE h').op).hom s =
    (Y.presheaf.map (homOfLE h₁).op ≫ f.appLE O₁ O' h₂).hom s
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
end GlobalTheory.KS.Kunneth
