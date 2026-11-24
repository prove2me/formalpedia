-- Prove2me | solution 1 for GlobalTheory.exists_under_eq_of_mem_associatedPrimes_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:48:54.963+00:00
-- url     : https://prove2.me/submissions/14eb4ded-6d5c-46ca-93f5-17c4e1e6eb13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AssociatedPrimeLocalizationDvr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A A' M : Type*} [CommRing A]
    [CommRing A'] [Algebra A A'] [AddCommGroup M] [Module A M] [Module A' M]
    [IsScalarTower A A' M] (hs : Function.Surjective (algebraMap A A')) {q : Ideal A}
    (hq : q ∈ associatedPrimes A M) : ∃ q' ∈ associatedPrimes A' M, q'.under A = q := by
  obtain ⟨hp, v, hv⟩ := hq
  set q' : Ideal A' := ((⊥ : Submodule A' M).colon {v}).radical with hq'
  have hunder : q'.under A = q := by
    ext a
    rw [Ideal.under_def, Ideal.mem_comap, hv]
    simp only [hq', Ideal.mem_radical_iff, Submodule.mem_colon_singleton, Submodule.mem_bot,
      ← map_pow, algebraMap_smul]
  have hmap : q.map (algebraMap A A') = q' := by
    rw [← hunder]
    exact Ideal.map_comap_of_surjective _ hs q'
  have hker : RingHom.ker (algebraMap A A') ≤ q := fun a ha ↦ by
    rw [hv]
    refine Ideal.le_radical ?_
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← algebraMap_smul A',
      RingHom.mem_ker.1 ha, zero_smul]
  have hprime : q'.IsPrime := hmap ▸ Ideal.map_isPrime_of_surjective hs hker
  exact ⟨q', ⟨hprime, v, rfl⟩, hunder⟩
end GlobalTheory
