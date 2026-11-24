-- Prove2me | solution 1 for GlobalTheory.HeckeTate.form_isUnimod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:19:13.198642+00:00
-- url     : https://prove2.me/submissions/78ec888c-e117-452b-9cb7-27a2a72a0da5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HostGeneratorPowFourTraceNormModEight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsTateIsoHeckeQuotient
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_adj
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_ext


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
open GlobalTheory GlobalTheory.HeckeTate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
namespace GlobalTheory.HeckeTate
theorem _root_.solution (D : Datum H) : IsUnimod H.bar (form D) := by
  refine ⟨fun x y => ?_, D.adj, fun x y h => D.unimod.1 (LinearMap.ext fun a => DFunLike.congr_fun h a),
    fun f => ?_⟩
  · exact (LinearMap.IsAlt.neg (B := D.EF) D.alt y x).symm
  · obtain ⟨x, hx⟩ := D.unimod.2 f.toIntLinearMap
    exact ⟨x, AddMonoidHom.ext fun a => LinearMap.congr_fun hx a⟩
end GlobalTheory.HeckeTate
