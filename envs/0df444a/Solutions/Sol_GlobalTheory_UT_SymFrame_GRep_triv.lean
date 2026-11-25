-- Prove2me | solution 1 for GlobalTheory.UT.SymFrame.GRep.triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:34:46.590227+00:00
-- url     : https://prove2.me/submissions/6979fd9c-17d7-42c0-a5fa-163c6b28955f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
import Theorems.Thm_GlobalTheory_UT_SymFrame_normd_iff
import Theorems.Thm_GlobalTheory_UT_SymFrame_normd_unique
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_normd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.SymFrame
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {Y : Over (Spec (CommRingCat.of R))}
namespace GlobalTheory.UT.SymFrame
namespace GRep
theorem _root_.solution (hG : GlobalFnsSt) {P v} (h : GRep D.P.L D.P.A P v)
    (hP : ∀ (U : Type) [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U), P U h = 1)
    (h₁ : ∀ y J, Good D.P.L y J → v (𝟙_ _) 1 y J = 1) (T : Over _) (r : T ⟶ D.P.A) (z : T.left) (J)
    (hJ : Good D.P.L z J) : v T r z J = 1 := by
  obtain ⟨s, hs, vs⟩ := h.normd (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun U _ h => (hP U h).trans (Fintype.prod_empty _).symm) h₁
  have h1 : Normd (D := D) (LB.oneGen D.P.L) := (normd_iff _).2
    ⟨fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
      fun _ _ _ => val_one _⟩
  exact (vs T r z J hJ).symm.trans ((normd_unique hG hs h1 _ z J hJ).trans (val_one _))
end GRep
end GlobalTheory.UT.SymFrame
