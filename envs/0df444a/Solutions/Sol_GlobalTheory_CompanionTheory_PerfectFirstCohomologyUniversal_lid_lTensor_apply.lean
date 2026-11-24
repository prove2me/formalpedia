-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal.lid_lTensor_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:29:10.976973+00:00
-- url     : https://prove2.me/submissions/b9ec44e9-d193-47d9-bf8a-986f92196b4d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuasiIsomorphismDegreeOneKernel
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal
namespace GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal
theorem _root_.solution {R X Y : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y) (u : R ⊗[R] X) :
    TensorProduct.lid R Y (f.lTensor R u) = f (TensorProduct.lid R X u) := by
  induction u with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp only [map_add, ha, hb]
end GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal
