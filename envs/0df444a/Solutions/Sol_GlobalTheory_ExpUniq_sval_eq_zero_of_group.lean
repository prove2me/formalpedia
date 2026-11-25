-- Prove2me | solution 1 for GlobalTheory.ExpUniq.sval_eq_zero_of_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:26.036091+00:00
-- url     : https://prove2.me/submissions/717c1798-9c81-4919-ae99-4028e33e2f66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfWeightSum
import Theorems.Thm_GlobalTheory_ExpUniq_sval_eq_zero_of_flat

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
noncomputable section
open GlobalTheory GlobalTheory.ExpUniq
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (c : GtCoord I D e G)
  {Y : Scheme.{0}} (p : Y ⟶ D.P.A.left) {K : Type} [Fintype K] {ε : K → ℤ}
namespace GlobalTheory.ExpUniq
theorem _root_.solution {φ : K → (Y ⟶ D.P.A.left)} (s : LB.Sec (LB.LinComb D.P.L φ ε))
    (H : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y), r ≫ p = x ≫ c.pG.left →
      ∀ z J, Good D.P.L z J → sval s r z J = 0)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (ha : (r ≫ p) ≫ D.P.A.hom = a ≫ thick R I e) (z : Z) (J) (hJ : Good D.P.L z J) : sval s r z J = 0 := by
  let b : Z ⟶ (thickObj R I e D.P.A).left := pullback.lift (r ≫ p) a ha
  have hb : b ≫ pullback.fst D.P.A.hom (thick R I e) = r ≫ p := pullback.lift_fst _ _ _
  have := c.q_flat
  have := c.q_surj
  refine sval_eq_zero_of_flat D.P.isLB s r (pullback.fst b c.q.left)
    (H _ (pullback.snd b c.q.left) _ ?_) z J hJ
  rw [Category.assoc, ← hb, ← Category.assoc, pullback.condition, Category.assoc]
  rfl
end GlobalTheory.ExpUniq
