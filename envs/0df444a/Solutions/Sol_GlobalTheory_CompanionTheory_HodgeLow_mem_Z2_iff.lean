-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeLow.mem_Z2_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:37:08.709344+00:00
-- url     : https://prove2.me/submissions/e87211ca-bf61-4b45-8a26-0bfa13ab1e7d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PullbackZeroCochainsAlgebraMap
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeLow_d2_apply
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeLow
variable {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.HodgeLow
theorem _root_.solution (z : C2 F) : z ∈ Z2 F ↔ d2 F z = 0 := by
  refine ⟨fun h ↦ ?_, fun h T T' T'' T''' φ ψ χ ↦ ?_⟩
  · funext T T' T'' T''' φ ψ χ
    rw [d2_apply]
    have := h φ ψ χ
    simp only [Pi.zero_apply]
    linear_combination -this
  · have : d2 F z T T' T'' T''' φ ψ χ = 0 := by rw [h]; rfl
    rw [d2_apply] at this
    linear_combination -this
end GlobalTheory.CompanionTheory.HodgeLow
