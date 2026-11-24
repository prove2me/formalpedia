-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.hasFDerivAt_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:26:25.491825+00:00
-- url     : https://prove2.me/submissions/2499866c-fc48-4030-9da1-7d8d3775aad2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableExpNegSumAbs
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_lin_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution {ι : Type} [Fintype ι] (w : ℂ) (t : ι → ℝ) (z : ι → ℂ) :
    HasFDerivAt (fun z : ι → ℂ => w * ker z t) ((w * ker z t) • lin t) z := by
  have h1 : HasFDerivAt (fun z : ι → ℂ => lin t z) (lin t) z := (lin t).hasFDerivAt
  have h2 := (h1.cexp).const_mul w
  have e : (fun z : ι → ℂ => w * ker z t) = fun z => w * Complex.exp (lin t z) := by
    funext z; simp only [ker, lin_apply]
  have e2 : (w * ker z t) • lin t = w • Complex.exp (lin t z) • lin t := by
    rw [smul_smul, ker, lin_apply]
  rw [e, e2]
  exact h2
end GlobalTheory.CompanionTheory.EisTube
