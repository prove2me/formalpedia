-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.LiftO.rTensor_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:25:57.351091+00:00
-- url     : https://prove2.me/submissions/b5d96e9c-0b33-4c64-9bb1-23612dcdba8c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.LiftO
variable {R : Type} [CommRing R] {C E : Type} [Category.{0} C] [Category.{0} E]
  {F : C ⥤ CommAlgCat.{0} R} {G : E ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.Hodge.LiftO
theorem _root_.solution (m : CoefMap (RingHom.id R) F G) (t : Z1 F ⊗[R] Glob1 F) :
    (H1.mk G).rTensor (Glob1 G) (TensorProduct.map m.pullbackOneCocycle (pullGlob1 m) t) =
      TensorProduct.map m.pull1 (pullGlob1 m) ((H1.mk F).rTensor (Glob1 F) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f ω => rfl
  | add x y hx hy => simp only [map_add, hx, hy]
end GlobalTheory.CompanionTheory.Hodge.LiftO
