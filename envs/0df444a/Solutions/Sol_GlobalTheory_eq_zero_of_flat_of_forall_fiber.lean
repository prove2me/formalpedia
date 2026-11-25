-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_flat_of_forall_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:16:23.507355+00:00
-- url     : https://prove2.me/submissions/bd7bec38-642d-4ae5-92bf-21e015fba62a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Theorems.Thm_GlobalTheory_localizedModule_mk_one_eq_zero_iff
import Theorems.Thm_GlobalTheory_eq_zero_of_forall_associatedPrimes_exists_smul_eq_zero
import Theorems.Thm_GlobalTheory_associatedPrimes_subset_of_flat
import Theorems.Thm_GlobalTheory_mem_associatedPrimes_iff_of_flat
import Theorems.Thm_GlobalTheory_mem_associatedPrimes_iff_generic_of_flat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M]
variable [Module B M] [IsScalarTower A B M] [Module.Flat A M]
variable [Module.Flat A B]
namespace GlobalTheory
theorem _root_.solution [IsNoetherianRing A] [IsNoetherianRing B]
    {L : Type*} [AddCommGroup L] [Module B L] [Module.Flat B L]
    (hfib : ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A A →
      NoZeroDivisors (p.asIdeal.Fiber B)) {x : L}
    (hx : ∀ q : PrimeSpectrum B, q.asIdeal.under A ∈ associatedPrimes A A →
      ∃ q' : PrimeSpectrum B, q'.asIdeal.under A = q.asIdeal.under A ∧
        (LocalizedModule.mk x 1 : LocalizedModule q'.asIdeal.primeCompl L) = 0) : x = 0 := by
  refine eq_zero_of_forall_associatedPrimes_exists_smul_eq_zero (A := B) fun q hq ↦ ?_
  have hqB := associatedPrimes_subset_of_flat hq
  haveI := hqB.isPrime
  have hp := ((mem_associatedPrimes_iff_of_flat (A := A) q).1 hqB).1
  haveI := hfib ⟨q.under A, inferInstance⟩ hp
  obtain ⟨q', h1, h2⟩ := hx ⟨q, inferInstance⟩ hp
  obtain ⟨s, hs, h⟩ := (localizedModule_mk_one_eq_zero_iff q'.asIdeal x).1 h2
  exact ⟨s, fun hsq ↦ hs (((mem_associatedPrimes_iff_generic_of_flat (A := A) q).1 hqB).2
    q'.asIdeal q'.2 h1 hsq), h⟩
end GlobalTheory
