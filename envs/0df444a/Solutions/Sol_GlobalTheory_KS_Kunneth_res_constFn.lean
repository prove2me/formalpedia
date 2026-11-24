-- Prove2me | solution 1 for GlobalTheory.KS.Kunneth.res_constFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:27:18.751158+00:00
-- url     : https://prove2.me/submissions/68ac9a64-ab7b-45fe-96a0-00d53bd84385

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDualFamilyModSubspace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCovers
import Theorems.Thm_GlobalTheory_KS_Kunneth_cstHom_apply

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
theorem _root_.solution {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) {O O' : Y.Opens} (h : O' ≤ O) (c : K) :
    resG Y h (constFn q O c) = constFn q O' c := by
  rw [← cstHom_apply, ← cstHom_apply]
  have e : cstHom q O ≫ Y.presheaf.map (homOfLE h).op = cstHom q O' := by
    unfold cstHom
    rw [Category.assoc]
    congr 1
    exact Scheme.Hom.appLE_map _ _ _
  rw [← e]
  rfl
end GlobalTheory.KS.Kunneth
