-- Prove2me | solution 1 for GlobalTheory.ArcTransport.exists_commonField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:35:00.745996+00:00
-- url     : https://prove2.me/submissions/336a377e-994d-4d09-9170-7433d799873b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsCommonField
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ArcTransport
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ToricData GlobalTheory.HostModel
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
  (k : Type) [Field k] (bF : c.F →+* k)
namespace GlobalTheory.ArcTransport
theorem _root_.solution : ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F)
    (_ : Algebra (FractionRing (PowerSeries k)) F) (_ : Algebra (FractionRing k) F),
    ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)) := by
  let F := AlgebraicClosure (FractionRing (PowerSeries k))
  let g : k →+* F := ((algebraMap (FractionRing (PowerSeries k)) F).comp
    (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))).comp PowerSeries.C
  exact ⟨F, inferInstance, inferInstance, inferInstance,
    (IsFractionRing.lift (K := FractionRing k) g.injective).toAlgebra,
    fun x => IsFractionRing.lift_algebraMap (K := FractionRing k) g.injective x⟩
end GlobalTheory.ArcTransport
