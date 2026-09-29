-- Prove2me | solution 1 for IsLocalRing.mem_range_algebraMap_of_flat_of_isLocalHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b16899d0-07f8-535c-8adc-09836e20a6a1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_mem_range_algebraMap_of_flat_of_isLocalHom

set_option autoImplicit false

universe u v u' v'

theorem solution
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsDomain R] [IsDomain S]
    (f : R →+* S) (hf : f.Flat) [IsLocalHom f]
    (K : Type u') (L : Type v') [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    (hcomm : ∀ r : R, algebraMap R L r = algebraMap S L (f r))
    (x : K) (hx : algebraMap K L x ∈ (algebraMap S L).range) :
    x ∈ (algebraMap R K).range := by
  algebraize [f]
  haveI hff : Module.FaithfullyFlat R S :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _ inferInstance ‹_›
  have hinj : Function.Injective (algebraMap R S) :=
    (RingHom.faithfullyFlat_algebraMap_iff.mpr hff).injective
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨s, hs⟩ := hx

  have hKL : ∀ r : R, algebraMap K L (algebraMap R K r) = algebraMap S L (algebraMap R S r) := by
    intro r
    rw [← IsScalarTower.algebraMap_apply R K L r, hcomm r]
    rfl
  have hfb0 : algebraMap R S b ≠ 0 := fun h => hb0 (hinj (by rw [h, map_zero]))

  have hdiv : algebraMap R S a = s * algebraMap R S b := by
    have h1 : algebraMap S L s =
        algebraMap S L (algebraMap R S a) / algebraMap S L (algebraMap R S b) := by
      rw [hs, map_div₀, hKL, hKL]
    have h2 : algebraMap S L (algebraMap R S b) ≠ 0 := fun h =>
      hfb0 ((IsFractionRing.to_map_eq_zero_iff (K := L)).mp h)
    apply IsFractionRing.injective S L
    rw [map_mul, h1, div_mul_cancel₀ _ h2]

  have hmem : a ∈ Ideal.comap (algebraMap R S) ((Ideal.span {b}).map (algebraMap R S)) := by
    rw [Ideal.mem_comap, Ideal.map_span, Set.image_singleton, hdiv]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat] at hmem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨r, ?_⟩
  have hbK : algebraMap R K b ≠ 0 := fun h => hb0 ((IsFractionRing.to_map_eq_zero_iff (K := K)).mp h)
  rw [eq_div_iff hbK, ← map_mul, hr]

#print axioms solution

end S_IsLocalRing_mem_range_algebraMap_of_flat_of_isLocalHom
end P2MW
export P2MW.S_IsLocalRing_mem_range_algebraMap_of_flat_of_isLocalHom (solution)
