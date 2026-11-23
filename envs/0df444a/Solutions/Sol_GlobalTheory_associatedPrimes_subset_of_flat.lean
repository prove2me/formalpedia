-- Prove2me | solution 1 for GlobalTheory.associatedPrimes_subset_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:46.025038+00:00
-- url     : https://prove2.me/submissions/60f9211f-1115-454f-b83e-99bda9eedc27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul

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
namespace GlobalTheory
theorem _root_.solution [IsNoetherianRing A] [Module.Flat A M] :
    associatedPrimes A M ⊆ associatedPrimes A A := by
  intro p hp
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hp ⊢
  obtain ⟨hp, x, hx⟩ := hp
  have hmem : ∀ a, a ∈ p ↔ a • x = 0 := fun a ↦ by simp [hx, Submodule.mem_colon_singleton]
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free
    (f := p.subtype) (x := LinearMap.toSpanSingleton A M x)
    (by ext ⟨a, ha⟩; simpa using (hmem a).1 ha)
  have hx' : x = y (a 1) := by simpa using congr($hy 1)
  have hk : ∀ r ∈ p, ∀ j, r * a 1 j = 0 := fun r hr j ↦ by
    have : a r = 0 := by simpa using congr($ha ⟨r, hr⟩)
    have h2 : r • a 1 = 0 := by rw [← map_smul, smul_eq_mul, mul_one, this]
    simpa using congr($h2 j)
  refine ⟨hp, ?_⟩
  by_contra hne
  have : ∀ j, ∃ s ∉ p, s * a 1 j = 0 := fun j ↦ by
    by_contra hcon
    push Not at hcon
    refine hne ⟨a 1 j, ?_⟩
    ext r
    simp only [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]
    exact ⟨fun hr ↦ hk r hr j, fun hr ↦ by_contra fun h ↦ hcon r h hr⟩
  choose s hs hs' using this
  have hprod : (∏ j, s j) ∉ p := p.primeCompl.prod_mem fun j _ ↦ hs j
  refine hprod ((hmem _).2 ?_)
  have : (∏ j, s j) • a 1 = 0 := by
    ext j
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem s (Finset.mem_univ j)
    rw [Finsupp.smul_apply, smul_eq_mul, hc, mul_comm (s j), mul_assoc, hs', mul_zero,
      Finsupp.zero_apply]
  rw [hx', ← map_smul, this, map_zero]
end GlobalTheory
