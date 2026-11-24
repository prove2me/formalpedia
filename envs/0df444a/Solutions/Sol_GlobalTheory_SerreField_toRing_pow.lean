-- Prove2me | solution 1 for GlobalTheory.SerreField.toRing_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:45:31.804869+00:00
-- url     : https://prove2.me/submissions/3ef79f05-7606-4b8c-b853-bea5576e0d37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulPullOfCubeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsOddNeZero
import Theorems.Thm_GlobalTheory_SerreField_toRing_apply
import Theorems.Thm_GlobalTheory_SerreField_homRing_ext

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SerreField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.MulPull
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]
variable {A}
namespace GlobalTheory.SerreField
theorem _root_.solution (σ : A ≅ A) [IsMonHom σ.hom] (m : ℕ) :
    toRing σ.hom ^ m = toRing (iter σ m).hom := by
  induction m with
  | zero => exact homRing_ext (by rw [toRing_apply]; simp [iter])
  | succ m ih =>
    rw [pow_succ', ih]
    exact homRing_ext (by
      change (toRing σ.hom).1 ((toRing (iter σ m).hom).1 _) = _
      simp only [toRing_apply, iter, Iso.trans_hom, Category.assoc])
end GlobalTheory.SerreField
