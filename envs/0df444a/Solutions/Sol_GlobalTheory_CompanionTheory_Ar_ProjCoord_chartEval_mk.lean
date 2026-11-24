-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.ProjCoord.chartEval_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:16:02.424335+00:00
-- url     : https://prove2.me/submissions/1e7fae93-a0bd-4a47-b2bd-83f48e0e7d00

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_awayEval_mk

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
theorem _root_.solution (x : κ → Ω) (c : κ) (hc : x c ≠ 0) (n : ℕ) (a : MvPolynomial κ o)
    (ha : a ∈ homogeneousSubmodule κ o (n • 1)) :
    chartEval x c hc (Away.mk _ (X_mem c) n a ha) = aeval x a / x c ^ n := by
  unfold chartEval
  rw [awayEval_mk]
  simp
end GlobalTheory.CompanionTheory.Ar.ProjCoord
