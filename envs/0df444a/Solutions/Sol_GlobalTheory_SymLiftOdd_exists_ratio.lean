-- Prove2me | solution 1 for GlobalTheory.SymLiftOdd.exists_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:06:34.512402+00:00
-- url     : https://prove2.me/submissions/08924c01-2308-482d-94b2-fa586b8465e2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Theorems.Thm_GlobalTheory_SymLiftOdd_exists_constT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SymLiftOdd
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}
variable {T : Over S} {k : ℤ}
namespace GlobalTheory.SymLiftOdd
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → ((T ⊗ A).left ⟶ A.left)} {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : Γ(T.left, ⊤)ˣ, ∀ (m : T ⊗ A ⟶ A) (y : (T ⊗ A).left) (J), Good L y J →
      val u (lift (fst T A) m).left y J = val u' (lift (fst T A) m).left y J * gm (fst T A).left y ⊤ c := by
  obtain ⟨c, hc⟩ := exists_constT hG hA hL (fun U _ h => (Fintype.prod_sum_type _).trans (by
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel]))
    (DVR.mulGen_isGen L _ _ _ _ u (LB.invGen L _ _ u') hu (DVR.invGen_isGen _ _ _ _ hu'))
  refine ⟨c, fun m y J hJ => ?_⟩
  rw [← hc m y J hJ, val_mul hJ, val_inv, mul_comm, inv_mul_cancel_right]
end GlobalTheory.SymLiftOdd
