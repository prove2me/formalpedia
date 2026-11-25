-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotLoc.tensor_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:22:11.411412+00:00
-- url     : https://prove2.me/submissions/3089cb0d-5984-4ba2-9915-0fe51fdfbf4c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLoc
namespace GlobalTheory.CompanionTheory.CotLoc
theorem _root_.solution {R R' W N : Type} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup W]
    [Module R W] [AddCommGroup N] [Module R' N] {f g : (R' ⊗[R] W) →ₗ[R'] N}
    (h : ∀ w, f (1 ⊗ₜ w) = g (1 ⊗ₜ w)) : f = g := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r w =>
    have : r ⊗ₜ[R] w = r • ((1 : R') ⊗ₜ[R] w) := by simp [TensorProduct.smul_tmul']
    rw [this, map_smul, map_smul, h]
  | add x y hx hy => simp [hx, hy]
end GlobalTheory.CompanionTheory.CotLoc
