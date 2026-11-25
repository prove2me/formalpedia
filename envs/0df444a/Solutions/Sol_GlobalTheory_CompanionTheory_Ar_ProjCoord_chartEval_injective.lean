-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.ProjCoord.chartEval_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:34:05.544491+00:00
-- url     : https://prove2.me/submissions/b825c427-74a8-4b89-a1a7-6025d70b3b76

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_chartEval_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.ProjCoord
open MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {o κ Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
namespace GlobalTheory.CompanionTheory.Ar.ProjCoord
theorem _root_.solution (x : κ → Ω) (c : κ) (hc : x c ≠ 0)
    (hinj : ∀ (n : ℕ) (g : MvPolynomial κ o), g.IsHomogeneous n → aeval x g = 0 → g = 0) :
    Function.Injective (chartEval (o := o) x c hc) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (X_mem (o := o) c) z
  rw [chartEval_mk, div_eq_zero_iff, or_iff_left (pow_ne_zero _ hc)] at hz
  obtain rfl := hinj _ a ha hz
  ext
  simp [Localization.mk_zero]
end GlobalTheory.CompanionTheory.Ar.ProjCoord
