-- Prove2me | solution 1 for GroundTheory.Global.summable_absNorm_rpow_neg_of_not_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:15.897268+00:00
-- url     : https://prove2.me/submissions/16f246de-5339-49aa-b6a0-48e959bc894c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Theorems.Thm_GroundTheory_Global_rationalPrimeUnder_prime
import Theorems.Thm_GroundTheory_Global_sq_rationalPrimeUnder_le_absNorm
import Theorems.Thm_GroundTheory_Global_summable_of_le_rationalPrimeUnder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set
noncomputable section
variable {K L : Type*} [Field L] [NumberField L]
namespace GroundTheory.Global
theorem _root_.solution {s : ℝ} (hs : 1 / 2 < s) :
    Summable fun w : {w : HeightOneSpectrum (𝓞 L) // ¬ (Ideal.absNorm w.asIdeal).Prime} =>
      (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s) := by
  refine (summable_subtype_iff_indicator
    (s := {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime})
    (f := fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))).mpr ?_
  refine summable_of_le_rationalPrimeUnder _ (h := fun n : ℕ => (n : ℝ) ^ (-(2 * s)))
    (fun _ => Set.indicator_nonneg (fun _ _ => by positivity) _) (fun _ => by positivity)
    (Real.summable_nat_rpow.mpr (by linarith)) (fun w => ?_)
  by_cases hw : w ∈ {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime}
  · rw [Set.indicator_of_mem hw]
    have hp : (0 : ℝ) < rationalPrimeUnder w := by exact_mod_cast (rationalPrimeUnder_prime w).pos
    have hle : ((rationalPrimeUnder w : ℕ) : ℝ) ^ (2 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := by
      rw [Real.rpow_two]
      exact_mod_cast sq_rationalPrimeUnder_le_absNorm hw
    calc (Ideal.absNorm w.asIdeal : ℝ) ^ (-s)
        ≤ (((rationalPrimeUnder w : ℕ) : ℝ) ^ (2 : ℝ)) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
      _ = ((rationalPrimeUnder w : ℕ) : ℝ) ^ (-(2 * s)) := by
          rw [← Real.rpow_mul hp.le]; ring_nf
  · rw [Set.indicator_of_notMem hw]
    positivity
end GroundTheory.Global
