-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfRetract.cyclesMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:28:50.03181+00:00
-- url     : https://prove2.me/submissions/57f2a7db-c046-4b15-82a4-a88b7a24d26e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HomotopyProjectorComplexBounded
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfRetract
variable {R : Type} [CommRing R] {E : ℕ → Type} [∀ n, AddCommGroup (E n)] [∀ n, Module R (E n)]
namespace GlobalTheory.CompanionTheory.PerfRetract
theorem _root_.solution (d : ∀ n, E n →ₗ[R] E (n + 1))
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (inc : ∀ n, C.X n →ₗ[R] E n)
    (r : ∀ n, E n →ₗ[R] C.X n) (hri : ∀ p, r p ∘ₗ inc p = LinearMap.id)
    (hinc : ∀ p, inc (p + 1) ∘ₗ (C.d p (p + 1)).hom = d p ∘ₗ inc p)
    (hr : ∀ p, r (p + 1) ∘ₗ d p = (C.d p (p + 1)).hom ∘ₗ r p) (j : ℕ) :
    Function.Surjective (cyclesMap d C r hr j) := by
  intro y
  have h1 := LinearMap.congr_fun (hinc j) y.1
  simp only [LinearMap.comp_apply] at h1
  refine ⟨⟨inc j y.1, ?_⟩, Subtype.ext ?_⟩
  · rw [LinearMap.mem_ker, ← h1, LinearMap.mem_ker.1 y.2, map_zero]
  · exact LinearMap.congr_fun (hri j) y.1
end GlobalTheory.CompanionTheory.PerfRetract
