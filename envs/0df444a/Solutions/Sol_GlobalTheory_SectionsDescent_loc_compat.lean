-- Prove2me | solution 1 for GlobalTheory.SectionsDescent.loc_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:39:00.284138+00:00
-- url     : https://prove2.me/submissions/693bfd80-7ffd-43c7-acd5-a9e081a02308

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
import Theorems.Thm_GlobalTheory_SectionsDescent_rs_rs
import Theorems.Thm_GlobalTheory_SectionsDescent_app_rs
import Theorems.Thm_GlobalTheory_SectionsDescent_sec_compat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.SectionsDescent
open GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F] {Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of K)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom (algebraMap K F))))
namespace GlobalTheory.SectionsDescent
theorem _root_.solution {M : LB Y} (t : (M.pull p).Sec) (i j : M.ι) {W : Y.Opens} (hi : W ≤ M.U i)
    (hj : W ≤ M.U j) :
    rs (pre_mono p hi) (loc t i) =
      (p.app W).hom (rs (le_inf hi hj) (M.g i j : Γ(Y, M.U i ⊓ M.U j))) * rs (pre_mono p hj) (loc t j) := by
  unfold loc
  rw [rs_rs, rs_rs, sec_compat t (fun _ => i) (fun _ => j) ((pre_mono p hi).trans (pre_le_chart M p fun _ => i))
    ((pre_mono p hj).trans (pre_le_chart M p fun _ => j)), app_rs]
  congr 1
  have e : ((M.pull p).g (fun _ => i) (fun _ => j) : Γ(Y', (M.pull p).U (fun _ => i) ⊓ (M.pull p).U fun _ => j)) =
      rs (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) (fun _ => i) PUnit.unit))
        (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) (fun _ => j) PUnit.unit)))
        ((p.app (M.U i ⊓ M.U j)).hom (M.g i j : Γ(Y, M.U i ⊓ M.U j))) := by
    have key : ∀ {G : Type} [CommGroup G] (u : G), ∏ _k : PUnit.{1}, u ^ (1 : ℤ) = u := fun u => by simp
    exact congrArg Units.val (key _)
  rw [e]
  exact rs_rs _ _ _
end GlobalTheory.SectionsDescent
