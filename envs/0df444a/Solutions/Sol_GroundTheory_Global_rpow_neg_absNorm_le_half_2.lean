-- Prove2me | solution 2 for GroundTheory.Global.rpow_neg_absNorm_le_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:59:47.992504+00:00
-- url     : https://prove2.me/submissions/c3786d06-7abe-4a32-aa95-13c264237f65

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Theorems.Thm_GroundTheory_Global_two_le_absNorm_of_prime

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
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Global
theorem _root_.solution {p : Ideal (𝓞 K)} (hp : Prime p) {s : ℝ} (hs : 1 ≤ s) :
    (absNorm p : ℝ) ^ (-s) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ absNorm p := by exact_mod_cast two_le_absNorm_of_prime hp
  calc (absNorm p : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by linarith)
    _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
end GroundTheory.Global
