-- Prove2me | solution 1 for GroundTheory.Global.sum_range_dedekindZetaTerm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:36.117206+00:00
-- url     : https://prove2.me/submissions/f91ee2bf-5d33-4221-9c98-c4dde02c1f15

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
namespace GroundTheory.Global
theorem _root_.solution (s : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, dedekindZetaTerm K s n =
      ∑ I ∈ (finite_absNorm_lt K N).toFinset, (absNorm I : ℝ) ^ (-s) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun I : Ideal (𝓞 K) => absNorm I)
    (t := Finset.range N) (fun I hI => by simpa using hI)]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.sum_congr rfl (fun I hI => by rw [(Finset.mem_filter.mp hI).2]),
    Finset.sum_const, nsmul_eq_mul, dedekindZetaTerm]
  congr 2
  have hfin := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n
  have : ((finite_absNorm_lt K N).toFinset.filter fun I => absNorm I = n) = hfin.toFinset := by
    ext I
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, mem_ofPred_eq]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ Finset.mem_range.mp hn, h⟩
  rw [this, ← Nat.card_eq_card_finite_toFinset]
  rfl
end GroundTheory.Global
