-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfExt.bc_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:24:49.530956+00:00
-- url     : https://prove2.me/submissions/cc382c7d-7bc5-4ac6-9bde-4d4112a72ecd

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_D2Apply
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfExt
namespace GlobalTheory.CompanionTheory.PerfExt
theorem _root_.solution {R R' N Q : Type} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup N] [Module R N]
    [AddCommGroup Q] [Module R' Q] (g h : R' ⊗[R] N →ₗ[R'] Q) (H : ∀ n, g (1 ⊗ₜ n) = h (1 ⊗ₜ n)) : g = h := by
  refine LinearMap.ext fun t ↦ ?_
  induction t with
  | zero => simp
  | tmul r n =>
    have e : r ⊗ₜ[R] n = r • ((1 : R') ⊗ₜ[R] n) := by simp [TensorProduct.smul_tmul']
    rw [e, map_smul, map_smul, H]
  | add a b ha hb => simp only [map_add, ha, hb]
end GlobalTheory.CompanionTheory.PerfExt
