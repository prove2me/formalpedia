-- Prove2me | solution 1 for GroundTheory.Global.sum_rpow_neg_le_dedekindZetaReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:57.994815+00:00
-- url     : https://prove2.me/submissions/63b8d687-fe2d-4086-89b3-4e2ccb864e8a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Theorems.Thm_GroundTheory_Global_dedekindZetaTerm_nonneg
import Theorems.Thm_GroundTheory_Global_sum_range_dedekindZetaTerm

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
theorem _root_.solution (T : Finset (Ideal (𝓞 K))) {s : ℝ}
    (hζ : Summable (dedekindZetaTerm K s)) :
    ∑ I ∈ T, (absNorm I : ℝ) ^ (-s) ≤ dedekindZetaReal K s := by
  classical
  set N := T.sup (fun I => absNorm I) + 1
  have hsub : T ⊆ (finite_absNorm_lt K N).toFinset := by
    intro I hI
    rw [Set.Finite.mem_toFinset, mem_ofPred_eq]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun I => absNorm I) hI)
  calc ∑ I ∈ T, (absNorm I : ℝ) ^ (-s)
      ≤ ∑ I ∈ (finite_absNorm_lt K N).toFinset, (absNorm I : ℝ) ^ (-s) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ n ∈ Finset.range N, dedekindZetaTerm K s n := (sum_range_dedekindZetaTerm K s N).symm
    _ ≤ dedekindZetaReal K s :=
        hζ.sum_le_tsum _ (fun n _ => dedekindZetaTerm_nonneg K s n)
end GroundTheory.Global
