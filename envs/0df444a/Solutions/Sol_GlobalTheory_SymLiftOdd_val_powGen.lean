-- Prove2me | solution 1 for GlobalTheory.SymLiftOdd.val_powGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:17.556496+00:00
-- url     : https://prove2.me/submissions/f401f85c-4db3-4569-a55e-22c069a63ce0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Theorems.Thm_GlobalTheory_SymLiftOdd_lift_translT
import Theorems.Thm_P2M_GlobalTheory_SymLiftOdd_comp_pow__fae19791c0f2
import Theorems.Thm_GlobalTheory_SymLiftOdd_gm_powGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
theorem _root_.solution (θ : ThetaGrp A L k T) (n : ℕ) {x : T ⟶ A} (hx : θ.pt = x)
    {y : (T ⊗ A).left} {J} (hJ : Good L y J) (m : T ⊗ A ⟶ A) :
    val (powGen A L k θ n) (lift (fst T A) m).left y J =
      ∏ j ∈ Finset.range n, thetaVal θ y J ((fst T A ≫ x) ^ j * m) := by
  subst hx
  rw [Finset.prod_range]
  refine (gm_powGen θ n _ y _ (hJ.mem _ _)).trans (Finset.prod_congr rfl fun j₀ _ => ?_)
  refine (val_pull hJ (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
    (translT A (θ.pt ^ (j₀ : ℕ))).left (lift (fst T A) m).left).trans ?_
  rw [← Over.comp_left, lift_translT, comp_pow']; rfl
end GlobalTheory.SymLiftOdd
