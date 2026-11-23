-- Prove2me | solution 1 for GlobalTheory.SymLiftOdd.exists_constT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:36.198593+00:00
-- url     : https://prove2.me/submissions/8bf07d55-1362-45aa-844c-fa86ab4f09a0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Theorems.Thm_GlobalTheory_SymLiftOdd_exists_const
import Theorems.Thm_GlobalTheory_SymLiftOdd_surj_fst

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
namespace GlobalTheory.SymLiftOdd
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S} {K : Type} [Fintype K]
    {φ : K → ((T ⊗ A).left ⟶ A.left)} {ε : K → ℤ}
    (hF : ∀ (U : Type) [CommGroup U] (h : ((T ⊗ A).left ⟶ A.left) → U), ∏ k, h (φ k) ^ ε k = 1)
    {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) :
    ∃ a : Γ(T.left, ⊤)ˣ, ∀ (m : T ⊗ A ⟶ A) (y : (T ⊗ A).left) (J), Good L y J →
      val u (lift (fst T A) m).left y J = gm (fst T A).left y ⊤ a := by
  obtain ⟨a, ha⟩ := exists_const hL (fst T A).left (lift (𝟙 T) (1 : T ⟶ A)).left
    (by rw [← Over.comp_left, lift_fst]; rfl) (surj_fst hG hA T) hF hu
  exact ⟨a, fun m y J hJ => by rw [ha _ _ y J hJ, ← Over.comp_left, lift_fst]⟩
end GlobalTheory.SymLiftOdd
