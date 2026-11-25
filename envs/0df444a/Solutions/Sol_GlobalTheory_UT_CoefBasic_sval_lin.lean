-- Prove2me | solution 1 for GlobalTheory.UT.CoefBasic.sval_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:50:39.157132+00:00
-- url     : https://prove2.me/submissions/45c1331d-66d0-4fef-a1bf-f387b2c852ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFrameRatio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.CoefBasic
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UT.CoefBasic
theorem _root_.solution {k : ℕ} (b : TF (R := R) F ⟶ D.P.A) (s s' : Fam D F k) (c : F) (χ : D.X) {z : (TF (R := R) F).left} {J}
    (hJ : Good D.P.L z J) : sval ((c • s + s').s χ) (lift (𝟙 (TF (R := R) F)) b).left z J =
      cst F z c * sval (s.s χ) (lift (𝟙 (TF (R := R) F)) b).left z J +
        sval (s'.s χ) (lift (𝟙 (TF (R := R) F)) b).left z J := by
  have hm := hJ.mem (DegPre.famφ D F χ) (lift (𝟙 (TF (R := R) F)) b).left
  refine (gs_add _ z _ hm _ _).trans (congrArg₂ (· + ·) ((gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) ?_ rfl)) rfl)
  refine (gs_res _ z le_top hm _).trans ((gs_pull _ (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans ?_)
  rw [← Over.comp_left, lift_fst]; rfl
end GlobalTheory.UT.CoefBasic
