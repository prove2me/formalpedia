-- Prove2me | solution 1 for GlobalTheory.VVRank.natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:04:53.752501+00:00
-- url     : https://prove2.me/submissions/d0576adc-1d75-4888-9e35-dd781b5dc84c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VVRank
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
namespace GlobalTheory.VVRank
theorem _root_.solution {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S) {m : ℕ}
    (hm : IsUnit (m : Γ(S, ⊤))) : (m : K) ≠ 0 := by
  have := (hm.map t.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
  rw [map_natCast, map_natCast] at this
  exact this.ne_zero
end GlobalTheory.VVRank
