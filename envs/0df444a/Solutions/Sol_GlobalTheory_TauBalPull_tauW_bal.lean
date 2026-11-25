-- Prove2me | solution 1 for GlobalTheory.TauBalPull.tauW_bal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:12:08.683105+00:00
-- url     : https://prove2.me/submissions/905ffa88-f9df-4d2f-98a9-0c9c1e0af0cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBalOfIsPullDeg
import Theorems.Thm_GlobalTheory_TauBalPull_tauW_bal_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TauBalPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TauPull
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}
namespace GlobalTheory.TauBalPull
theorem _root_.solution (ψW : PsiOn D W)
    {K : Type} [Fintype K] {φ : K → ((D.P.A ⊗ D.P.A).left ⟶ D.P.A.left)} {ε : K → ℤ}
    (u : LB.Gen (LB.LinComb D.P.L φ ε)) (a b a' b' y y' : D.X)
    (h : LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.tau a b) (LB.pullGen D.P.L _ _ u (D.pt2 y y'))) (D.tau a' b'))
    {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TW W) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val (ψW.tau a b) κ.left z J * val₂ u z J (cP D T y) (cP D T y') = val (ψW.tau a' b') κ.left z J := by
  have := (val_mul hJ _ _ _).symm.trans (val_corr hJ (tauW_bal_corr ψW ⟨_, (κ.left z).2⟩ u a b a' b' y y' h) κ.left)
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
  refine Eq.trans ?_ (val_pull hJ _ _ _).symm
  rw [← Over.comp_left, comp_lift, comp_cP, comp_cP]
  rfl
end GlobalTheory.TauBalPull
