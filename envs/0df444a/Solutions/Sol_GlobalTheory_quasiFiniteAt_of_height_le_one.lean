-- Prove2me | solution 1 for GlobalTheory.quasiFiniteAt_of_height_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:25.842383+00:00
-- url     : https://prove2.me/submissions/1f4609fe-c82f-4886-b6e2-e373cd369e07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Theorems.Thm_GlobalTheory_exists_notMem_forall_mem_minimalPrimes

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
theorem _root_.solution {O B : Type*} [CommRing O] [IsNoetherianRing O]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B]
    (m : Ideal B) [hm : m.IsMaximal] (h1 : m.height ≤ 1) (π : O) (hπ : algebraMap O B π ≠ 0)
    (hπm : algebraMap O B π ∈ m) : Algebra.QuasiFiniteAt O m := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing O B
  obtain ⟨s, hsm, hs⟩ := exists_notMem_forall_mem_minimalPrimes
    (Ideal.span {algebraMap O B π}) m (fun P hP hle => by
      have hPp : P.IsPrime := hP.1.1
      have hfP : algebraMap O B π ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hP.1.2
      have hP0 : ⊥ < P := bot_lt_iff_ne_bot.mpr fun e => hπ (by simpa [e] using hfP)
      by_contra hne
      have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hP0
      have h3 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
      have h4 : (⊥ : Ideal B).height + 1 + 1 ≤ 1 := (add_le_add h2 le_rfl).trans (h3.trans h1)
      simp at h4
      exact absurd h4 (by decide))
  refine Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber (R := O) ⟨m, inferInstance⟩ ?_
  refine isOpen_induced_iff.mpr ⟨PrimeSpectrum.basicOpen s, (PrimeSpectrum.basicOpen s).isOpen, ?_⟩
  ext ⟨q, hq⟩
  simp only [Set.mem_preimage, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
    Set.mem_singleton_iff]
  constructor
  · intro hsq
    have hπq : algebraMap O B π ∈ q.asIdeal := by
      have : π ∈ (PrimeSpectrum.comap (algebraMap O B) q).asIdeal := by
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hq
        rw [hq]
        exact hπm
      exact this
    obtain ⟨P, hP, hPq⟩ := Ideal.exists_minimalPrimes_le (J := q.asIdeal)
      ((Ideal.span_singleton_le_iff_mem _).mpr hπq)
    have hPm : P = m := by
      by_contra hne
      exact hsq (hPq (hs P hP hne))
    subst hPm
    exact Subtype.ext <| PrimeSpectrum.ext (hm.eq_of_le q.isPrime.ne_top hPq).symm
  · intro e
    obtain rfl : q = ⟨m, inferInstance⟩ := congrArg Subtype.val e
    exact hsm
end GlobalTheory
