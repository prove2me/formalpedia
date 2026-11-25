-- Prove2me | solution 1 for GroundTheory.Global.absNorm_eq_prod_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:02.959953+00:00
-- url     : https://prove2.me/submissions/7c23e5a9-6e8c-4af8-bbaa-4e68c86771fe

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole

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
theorem _root_.solution {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (P : Finset (Ideal (𝓞 K)))
    (hP : (UniqueFactorizationMonoid.normalizedFactors I).toFinset ⊆ P) :
    absNorm I = ∏ p ∈ P, absNorm p ^ (UniqueFactorizationMonoid.normalizedFactors I).count p := by
  classical
  have hprod : (UniqueFactorizationMonoid.normalizedFactors I).prod = I :=
    associated_iff_eq.mp (UniqueFactorizationMonoid.prod_normalizedFactors hI)
  conv_lhs => rw [← hprod]
  rw [map_multiset_prod, Finset.prod_multiset_map_count]
  refine Finset.prod_subset hP fun p _ hp => ?_
  rw [Multiset.count_eq_zero.mpr (fun h => hp (Multiset.mem_toFinset.mpr h)), pow_zero]
end GroundTheory.Global
