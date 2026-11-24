-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.re_le_of_dist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:26:12.645845+00:00
-- url     : https://prove2.me/submissions/76dc0af9-a333-4739-9042-a2b603b703be

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableExpNegSumAbs

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
theorem _root_.solution {ι : Type} [Fintype ι] {z z₀ : ι → ℂ} (hz : dist z z₀ < 1) (i : ι) :
    |(z i).re| ≤ (∑ j, |(z₀ j).re|) + 1 := by
  have h1 : ‖z i - z₀ i‖ ≤ ‖z - z₀‖ := norm_le_pi_norm (z - z₀) i
  have h2 : ‖z - z₀‖ < 1 := by rwa [← dist_eq_norm]
  have h3 : |(z i - z₀ i).re| ≤ ‖z i - z₀ i‖ := Complex.abs_re_le_norm _
  have h4 : |(z₀ i).re| ≤ ∑ j, |(z₀ j).re| :=
    Finset.single_le_sum (f := fun j => |(z₀ j).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h5 : |(z i).re| ≤ |(z i - z₀ i).re| + |(z₀ i).re| := by
    have : (z i).re = (z i - z₀ i).re + (z₀ i).re := by simp
    rw [this]
    simpa using abs_add_le (z i - z₀ i).re (z₀ i).re
  linarith
end GlobalTheory.CompanionTheory.EisTube
