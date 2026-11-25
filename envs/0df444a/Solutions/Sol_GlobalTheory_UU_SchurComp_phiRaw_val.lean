-- Prove2me | solution 1 for GlobalTheory.UU.SchurComp.phiRaw_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:21:43.947108+00:00
-- url     : https://prove2.me/submissions/4692c41c-c6f5-40d4-8352-23711652b0e2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpFLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ChainVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalRaw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.SchurComp
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UU.SchurComp
theorem _root_.solution {k : ℕ} {g : GtPtF D F}
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))} {s s' : Raw D F k}
    (h : PhiRaw D F k 0 g w s s') {α : D.X}
    {u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 α g.b) (DegPre.deltaε k))} (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w))
    {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J} (hJ : Good D.P.L z J) :
    sval (s' α) r z J = sval (s α) (r ≫ (DegPre.trPt D F g.b).left) z J * (val u r z J).val :=
  (congrArg (fun β => sval (s' β) r z J) (add_zero α)).symm.trans
    ((secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).1 (h α u hu hc) Z r z J hJ)
end GlobalTheory.UU.SchurComp
