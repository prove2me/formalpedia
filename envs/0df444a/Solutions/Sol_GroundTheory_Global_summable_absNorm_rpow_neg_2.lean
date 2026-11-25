-- Prove2me | solution 2 for GroundTheory.Global.summable_absNorm_rpow_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:34:23.623374+00:00
-- url     : https://prove2.me/submissions/f9ac91f6-5256-4a19-811d-fbc901863820

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Theorems.Thm_GroundTheory_Global_rationalPrimeUnder_prime
import Theorems.Thm_GroundTheory_Global_rationalPrimeUnder_le_absNorm
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
theorem _root_.solution {s : ℝ} (hs : 1 < s) :
    Summable fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s) := by
  refine summable_of_le_rationalPrimeUnder _ (h := fun n : ℕ => (n : ℝ) ^ (-s))
    (fun _ => by positivity) (fun _ => by positivity)
    (Real.summable_nat_rpow.mpr (by linarith)) (fun w => ?_)
  exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (rationalPrimeUnder_prime w).pos)
    (by exact_mod_cast rationalPrimeUnder_le_absNorm w) (by linarith)
end GroundTheory.Global
