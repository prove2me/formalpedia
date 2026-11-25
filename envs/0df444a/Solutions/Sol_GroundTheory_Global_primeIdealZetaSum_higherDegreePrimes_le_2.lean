-- Prove2me | solution 2 for GroundTheory.Global.primeIdealZetaSum_higherDegreePrimes_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:58:34.403798+00:00
-- url     : https://prove2.me/submissions/6f243fba-df8f-4a14-bfb7-546a726488b5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Theorems.Thm_GroundTheory_Global_one_le_absNorm
import Theorems.Thm_GroundTheory_Global_higherDegreePrimes_subset
import Theorems.Thm_GroundTheory_Global_summable_indicator_not_prime
import Theorems.Thm_GroundTheory_Global_summable_higherDegreePrimes

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
variable (K L) [Field K] [NumberField K] [Algebra K L]
variable {K L}
variable (K L)
namespace GroundTheory.Global
theorem _root_.solution :
    ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → (higherDegreePrimes K L).primeIdealZetaSum s ≤ C := by
  refine ⟨∑' w, {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime}.indicator
    (fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 : ℝ))) w,
    fun s hs => ?_⟩
  have h1 := summable_indicator_not_prime (L := L) (s := 1) (by norm_num)
  have hs' := (summable_subtype_iff_indicator (s := higherDegreePrimes K L)
    (f := fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))).mp
    (summable_higherDegreePrimes K L (by linarith))
  rw [Set.primeIdealZetaSum_def, tsum_subtype (higherDegreePrimes K L)
    (fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))]
  refine Summable.tsum_le_tsum (fun w => ?_) hs' h1
  by_cases hw : w ∈ higherDegreePrimes K L
  · rw [indicator_of_mem hw, indicator_of_mem (higherDegreePrimes_subset hw)]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast one_le_absNorm w) (by linarith)
  · rw [indicator_of_notMem hw]
    exact indicator_nonneg (fun _ _ => by positivity) w
end GroundTheory.Global
