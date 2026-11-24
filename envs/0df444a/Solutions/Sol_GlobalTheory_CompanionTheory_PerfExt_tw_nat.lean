-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfExt.tw_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:40:08.467571+00:00
-- url     : https://prove2.me/submissions/66384714-f02f-4a43-a898-8bf47089c384

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_D2Apply
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfExt_tw_tmul
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
variable (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']
variable {R R'}
variable {N N₂ Q Q₂ M : Type} [AddCommGroup N] [Module R N] [AddCommGroup N₂] [Module R N₂]
  [AddCommGroup Q] [Module R' Q] [AddCommGroup Q₂] [Module R' Q₂]
  [AddCommGroup M] [Module R' M] [Module R M] [IsScalarTower R R' M]
namespace GlobalTheory.CompanionTheory.PerfExt
theorem _root_.solution (E : R' ⊗[R] N ≃ₗ[R'] Q) (E₂ : R' ⊗[R] N₂ ≃ₗ[R'] Q₂) (g : N →ₗ[R] N₂) (h : Q →ₗ[R'] Q₂)
    (H : ∀ n, h (E (1 ⊗ₜ n)) = E₂ (1 ⊗ₜ g n)) (t : M ⊗[R] N) :
    tw M E₂ (g.lTensor M t) = h.lTensor M (tw M E t) := by
  induction t with
  | zero => simp
  | tmul x n => simp [tw_tmul, H]
  | add a b ha hb => simp only [map_add, ha, hb]
end GlobalTheory.CompanionTheory.PerfExt
