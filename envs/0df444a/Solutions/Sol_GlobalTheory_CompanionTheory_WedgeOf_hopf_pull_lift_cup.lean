-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.hopf_pull_lift_cup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:45:48.557179+00:00
-- url     : https://prove2.me/submissions/7a6bf40a-4c01-47c5-b7df-bf6b5eb726d8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CupVanishingAntisymmetricCross
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_cup_add_cup_swap
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_cup
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_cup
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_crossB_apply
import Theorems.Thm_GlobalTheory_Cris_IsMor_pullCohomologyTwo_cup
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
namespace GlobalTheory.CompanionTheory.WedgeOf
theorem _root_.solution {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) {D : Type} [Category.{0} D] (G : D ⥤ CommAlgCat.{0} R)
    (π : CoefMap (RingHom.id R) (box F) G) (m : CoefMap (RingHom.id R) F G)
    (hm : ∀ c, m.pull1 c = π.pull1 ((boxL F).pull1 c + (boxR F).pull1 c))
    (t : H1 F ⊗[R] H1 F) :
    m.pull2 (TensorProduct.lift (cup F) t) =
      π.pull2 ((boxL F).pull2 (TensorProduct.lift (cup F) t) +
        (boxR F).pull2 (TensorProduct.lift (cup F) t) +
        TensorProduct.lift (crossB F) (t - TensorProduct.comm R _ _ t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.lift.tmul, CoefMap.pullCohomologyTwo_cup m a b, hm a, hm b, ← CoefMap.pullCohomologyTwo_cup π _ _]
    refine congrArg (fun x => π.pull2 x) ?_
    rw [CoefMap.pullCohomologyTwo_cup (boxL F) a b, CoefMap.pullCohomologyTwo_cup (boxR F) a b, TensorProduct.comm_tmul, map_sub,
      TensorProduct.lift.tmul, TensorProduct.lift.tmul, crossB_apply, crossB_apply]
    simp only [map_add, LinearMap.add_apply]
    have h := cup_add_cup_swap (box F) ((boxL F).pull1 b) ((boxR F).pull1 a)
    have h3 : cup (box F) ((boxR F).pull1 a) ((boxL F).pull1 b) =
        -cup (box F) ((boxL F).pull1 b) ((boxR F).pull1 a) :=
      eq_neg_iff_add_eq_zero.2 (by rw [add_comm]; exact h)
    rw [h3]
    abel
  | add x y hx hy =>
    simp only [map_add, map_sub, hx, hy]
    abel
end GlobalTheory.CompanionTheory.WedgeOf
