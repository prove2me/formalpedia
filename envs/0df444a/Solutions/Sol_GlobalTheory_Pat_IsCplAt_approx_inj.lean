-- Prove2me | solution 1 for GlobalTheory.Pat.IsCplAt.approx_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:19:54.929543+00:00
-- url     : https://prove2.me/submissions/9ab13dc3-b49b-4300-b36a-522b8d649b50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCplAtApprox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat
open GlobalTheory GlobalTheory.Pat
namespace GlobalTheory.Pat
namespace IsCplAt
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] [IsLocalRing S] {q : Ideal R}
    [hq : q.IsPrime] {φ : R →+* S} (h : IsCplAt q φ) (k : ℕ) (a : R)
    (ha : φ a ∈ maximalIdeal S ^ k) : ∃ b ∉ q, b * a ∈ q ^ k := by
  let L := Localization.AtPrime q
  have hu : ∀ y : q.primeCompl, IsUnit (φ y) := by
    intro y
    by_contra hy
    have : (y : R) ∈ (maximalIdeal S).comap φ := (mem_maximalIdeal _).2 hy
    rw [h.comap_eq] at this
    exact y.2 this
  letI : Algebra R S := φ.toAlgebra
  let ψ : L →+* S := IsLocalization.lift (M := q.primeCompl) hu
  letI : Algebra L S := ψ.toAlgebra
  have hψ : ∀ r, ψ (algebraMap R L r) = φ r := fun r => IsLocalization.lift_eq hu r
  haveI : IsScalarTower R L S := IsScalarTower.of_algebraMap_eq fun r => (hψ r).symm
  have hfl : Module.Flat R S := h.flat
  haveI : Module.Flat L S := (Module.flat_iff_of_isLocalization L q.primeCompl S).2 hfl
  have hcomp : (algebraMap L S).comp (algebraMap R L) = φ := RingHom.ext hψ
  haveI : IsLocalHom (algebraMap L S) := by
    apply ((local_hom_TFAE (algebraMap L S)).out 0 2).2
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hcomp, h.max_eq]
  haveI : Module.FaithfullyFlat L S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have key := Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) ((q ^ k).map (algebraMap R L))
  rw [Ideal.map_map, hcomp, Ideal.map_pow φ, ← h.max_eq] at key
  have ha' : algebraMap R L a ∈ (q ^ k).map (algebraMap R L) := by
    rw [← key, Ideal.mem_comap]
    exact (hψ a).symm ▸ ha
  obtain ⟨m, hm, hma⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl L _ a).1 ha'
  exact ⟨m, hm, hma⟩
end IsCplAt
end GlobalTheory.Pat
