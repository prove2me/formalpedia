-- Prove2me | solution 1 for GlobalTheory.PeriodicCousin.fderiv_dbar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:24:22.792313+00:00
-- url     : https://prove2.me/submissions/ad24d956-c89e-432f-a63c-215ad4300b3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DbarSolveComplexTorusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodicCechCocycleSmoothCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicPeriodicCocycleCoboundary
import Theorems.Thm_GlobalTheory_PeriodicCousin_contDiffAt_fderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real Topology
open GlobalTheory GlobalTheory.PeriodicCousin
variable {g : ℕ}
namespace GlobalTheory.PeriodicCousin
theorem _root_.solution {a : Fin g} {f : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (h : ContDiffAt ℝ ∞ f z) (v : Fin g → ℂ) :
    fderiv ℝ (dbar a f) z v = fderiv ℝ (fderiv ℝ f) z v (Pi.single a 1 : Fin g → ℂ) +
      I * fderiv ℝ (fderiv ℝ f) z v (I • (Pi.single a 1 : Fin g → ℂ)) := by
  have h1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((contDiffAt_fderiv h).differentiableAt (by simp)).hasFDerivAt
  have h2 := fun u : Fin g → ℂ =>
    (ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt.comp z h1
  have h3 := (h2 (Pi.single a 1)).add ((h2 (I • (Pi.single a 1 : Fin g → ℂ))).const_mul I)
  have h4 : fderiv ℝ (dbar a f) z = _ := h3.fderiv
  rw [h4]
  simp
end GlobalTheory.PeriodicCousin
