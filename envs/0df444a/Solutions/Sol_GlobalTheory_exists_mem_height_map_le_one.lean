-- Prove2me | solution 1 for GlobalTheory.exists_mem_height_map_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:05.357749+00:00
-- url     : https://prove2.me/submissions/efc1a16c-8160-494d-ab4b-b4ad57136641

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Theorems.Thm_GlobalTheory_height_le_one_of_forall_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m : Ideal A) [m.IsPrime] {U : Set (PrimeSpectrum A)} (hU : IsOpen U)
    (h : ∃ p ∈ U, p.asIdeal ≤ m) :
    ∃ q ∈ U, q.asIdeal ≤ m ∧ (m.map (Ideal.Quotient.mk q.asIdeal)).height ≤ 1 := by
  obtain ⟨p₀, hp₀, hp₀m⟩ := h
  obtain ⟨I, ⟨q, ⟨hqU, hqm⟩, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian A A)
    (PrimeSpectrum.asIdeal '' {p | p ∈ U ∧ p.asIdeal ≤ m}) ⟨_, p₀, ⟨hp₀, hp₀m⟩, rfl⟩
  refine ⟨q, hqU, hqm, ?_⟩
  obtain ⟨_, ⟨f, rfl⟩, hfq, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqU hU
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have : (m.map (Ideal.Quotient.mk q.asIdeal)).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by simpa using hqm)
  refine height_le_one_of_forall_mem _ (f := Ideal.Quotient.mk q.asIdeal f)
    (fun e => hfq (Ideal.Quotient.eq_zero_iff_mem.mp e)) fun p hp hp0 hpm => ?_
  by_contra hfp
  let p' : PrimeSpectrum A := ⟨p.comap (Ideal.Quotient.mk q.asIdeal), inferInstance⟩
  have hle : q.asIdeal ≤ p'.asIdeal := fun x hx => by
    change Ideal.Quotient.mk q.asIdeal x ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact p.zero_mem
  have hp'm : p'.asIdeal ≤ m := by
    refine (Ideal.comap_mono hpm).trans ?_
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_le le_rfl hqm
  refine hmax p'.asIdeal ⟨p', ⟨hfU hfp, hp'm⟩, rfl⟩ (lt_of_le_of_ne hle fun e => hp0 ?_)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨x, rfl⟩ := hsurj x
  have : x ∈ q.asIdeal := e ▸ hx
  simpa using Ideal.Quotient.eq_zero_iff_mem.mpr this
end GlobalTheory
