-- Prove2me | solution 1 for GlobalTheory.PhiBase.exists_pull_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:59:38.233515+00:00
-- url     : https://prove2.me/submissions/ace4652e-f6ff-4bcd-823a-a5674e083d71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EqOfIsGenTransl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_DegPreAbelianPartIsIntegralAndIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsThetaPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitOfStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AbelianPartEqOfThetaOperatorEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PhiBase
namespace GlobalTheory.PhiBase
theorem _root_.solution {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (t : Y' ⟶ Y) (g : Y' ⟶ X)
    (hg : t ≫ f = g) (θ : LB.Sec (L.pull f)) : ∃ θ' : LB.Sec (L.pull g),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
        sval (L := L) (φ := fun _ : PUnit => g) (ε := fun _ => 1) θ' r z J =
          sval (L := L) (φ := fun _ : PUnit => f) (ε := fun _ => 1) θ (r ≫ t) z J := by
  subst hg
  obtain ⟨θ', h⟩ := exists_sec hL (φ' := fun _ : PUnit => t ≫ f) (ε' := fun _ => 1)
    (fun U _ h => by simp [Fintype.prod_sum_type])
    (pullMulSec (L := L) (φ := fun _ : PUnit => f) (ε := fun _ => 1) θ t (LB.oneGen L (Y := Y'))
      (fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm))
  refine ⟨θ', fun Z r z J hJ => ?_⟩
  refine (h Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans ?_)
  rw [val_one, Units.val_one, _root_.mul_one]
end GlobalTheory.PhiBase
