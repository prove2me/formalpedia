-- Prove2me | solution 1 for GlobalTheory.UU.sval_of_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:41:27.956798+00:00
-- url     : https://prove2.me/submissions/6b65c93e-d295-4343-86c6-4d4556a9f819

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FamFEOneOfPsiRel
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open GlobalTheory GlobalTheory.UU
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UU
theorem _root_.solution (s₀ s : Raw D F 1) (c : F) (hs : ∀ α j, (s α).f j = DegPre.constBF D F c _ * (s₀ α).f j)
    (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J} (hJ : Good D.P.L z J) :
    sval (s α) r z J =
      gs (r ≫ (fst (TF (R := R) F) D.P.A).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) *
        sval (s₀ α) r z J :=
  (congrArg (gs r z _) (hs α _)).trans ((gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·)
    ((gs_res r z le_top (hJ.mem _ r) _).trans (gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _)) rfl))
end GlobalTheory.UU
