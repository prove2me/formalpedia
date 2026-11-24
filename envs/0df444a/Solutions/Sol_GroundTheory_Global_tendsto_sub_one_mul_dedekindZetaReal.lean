-- Prove2me | solution 1 for GroundTheory.Global.tendsto_sub_one_mul_dedekindZetaReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:30.79584+00:00
-- url     : https://prove2.me/submissions/5e4a0012-7e76-4cb0-87ce-d4b26de52fb3

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Theorems.Thm_GroundTheory_Global_dedekindZeta_ofReal

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
namespace GroundTheory.Global
theorem _root_.solution :
    Tendsto (fun s : ℝ => (s - 1) * dedekindZetaReal K s) (𝓝[>] 1)
      (𝓝 (dedekindZeta_residue K)) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  rw [Complex.ofReal_re] at h
  refine h.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
  have hs0 : s ≠ 0 := by simp only [mem_Ioi] at hs; linarith
  simp only [Function.comp_apply]
  rw [dedekindZeta_ofReal K hs0, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_mul, Complex.ofReal_re]
end GroundTheory.Global
