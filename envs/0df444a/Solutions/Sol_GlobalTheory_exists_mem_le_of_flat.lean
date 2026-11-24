-- Prove2me | solution 1 for GlobalTheory.exists_mem_le_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:44:41.747816+00:00
-- url     : https://prove2.me/submissions/9a6c301e-c10f-42cd-96a6-125aa403f532

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
theorem _root_.solution {O A : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [IsNoetherianRing A] [Algebra O A] [Module.Flat O A]
    (m : Ideal A) [m.IsPrime] {U : Set (PrimeSpectrum A)} (hU : IsOpen U)
    (hd : ∀ p : PrimeSpectrum A, p.asIdeal.comap (algebraMap O A) ≠ maximalIdeal O →
      p ∈ closure U) :
    ∃ p ∈ U, p.asIdeal ≤ m ∧ p.asIdeal.comap (algebraMap O A) ≠ maximalIdeal O := by
  obtain ⟨P, hPm, hP, hPO⟩ := Ideal.exists_ideal_le_liesOver_of_le (R := O) (p := ⊥)
    (q := m.under O) m bot_le
  obtain ⟨p, hp, hpP⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := P) bot_le
  have hpp : p.IsPrime := hp.1.1
  have hpO : p.comap (algebraMap O A) ≠ maximalIdeal O := fun e => by
    have : p.comap (algebraMap O A) ≤ ⊥ := (Ideal.comap_mono hpP).trans hPO.over.ge
    exact IsDiscreteValuationRing.not_a_field O (e ▸ le_bot_iff.mp this)
  refine ⟨⟨p, hpp⟩, ?_, hpP.trans hPm, hpO⟩
  obtain ⟨s, hsp, hs⟩ := exists_notMem_forall_mem_minimalPrimes ⊥ p
    fun Q hQ hle => le_antisymm hle (hp.2 hQ.1 hle)
  obtain ⟨x, hxs, hxU⟩ := mem_closure_iff.mp (hd ⟨p, hpp⟩ hpO) _
    (PrimeSpectrum.basicOpen s).isOpen hsp
  obtain ⟨Q, hQ, hQx⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := x.asIdeal) bot_le
  have hQp : Q = p := by
    by_contra hne
    exact hxs (hQx (hs Q hQ hne))
  subst hQp
  exact ((PrimeSpectrum.le_iff_specializes ⟨Q, hpp⟩ x).mp hQx).mem_open hU hxU
end GlobalTheory
