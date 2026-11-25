-- Prove2me | solution 1 for GlobalTheory.ConstFam.exists_gen_through
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:27:06.383798+00:00
-- url     : https://prove2.me/submissions/d6b94cfd-a5b5-492e-b64f-bad700d268c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_genSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_trans


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {X X' Y Y' Z : Scheme.{0}}
variable {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
variable {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
namespace GlobalTheory.ConstFam
theorem _root_.solution (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J J', Good L z J → Good L' z J' →
        val t (r ≫ h) z J = (∏ k, wVal w z J J' (r ≫ φ' k) ^ ε k) * val a r z J' := by
  obtain ⟨s, hs⟩ := exists_secThrough hw hL hL' hψ (Geo.Tor.genSec t ht)
  have hu : ∀ j, IsUnit (s.f j) := fun j => Y'.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J', hJ', e⟩ := sval_trans hL' s y j hy
    obtain ⟨J, hJ⟩ := exists_good' hL y
    have e' := hs.sval hψ (𝟙 _) hJ hJ'
    rw [sval_genSec t ht _ y hJ] at e'
    rw [← (Units.inv_mul_eq_iff_eq_mul _).2 e', ← Units.val_mul, ← Units.val_mul] at e
    exact (congrArg IsUnit ((gs_eq (𝟙 Y') y (LB.wchart L' φ' j) hy _).symm.trans e)).mpr (Units.isUnit _)
  refine ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j), fun Z r z J J' hJ hJ' => Units.ext ?_⟩
  refine (sval_genSec t ht _ z hJ).symm.trans ((hs.sval hψ r hJ hJ').trans ?_)
  rw [Units.val_mul]
  exact congrArg _ (gs_unit r z _ (hJ'.mem φ' r) (hu _).unit)
end GlobalTheory.ConstFam
