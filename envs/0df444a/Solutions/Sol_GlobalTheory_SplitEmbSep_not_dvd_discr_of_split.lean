-- Prove2me | solution 1 for GlobalTheory.SplitEmbSep.not_dvd_discr_of_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:32:07.422971+00:00
-- url     : https://prove2.me/submissions/720e4445-7e76-4ffa-bcda-200997b9f734

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsNormSubEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.SplitEmbSep
open NumberField
namespace GlobalTheory.SplitEmbSep
namespace _root_.GlobalTheory.SplitEmbSep
theorem _root_.solution {g : ℕ} (hg : g.Prime) (E : Type*) [Field E]
    [NumberField E]
    (h : (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E) :
    ¬ (g : ℤ) ∣ discr E := by
  have hgp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  set p : Ideal ℤ := Ideal.span {(g : ℤ)} with hp_def
  have hp0 : p ≠ ⊥ := by simpa [hp_def] using hgp.ne_zero
  haveI hpprime : p.IsPrime := (Ideal.span_singleton_prime hgp.ne_zero).mpr hgp
  haveI hpmax : p.IsMaximal := hpprime.isMaximal hp0
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) ℚ E hp0
  have hcard : (IsDedekindDomain.primesOverFinset p (𝓞 E)).card = Module.finrank ℚ E := by
    rw [← h, ← IsDedekindDomain.coe_primesOverFinset hp0, Set.ncard_coe_finset]
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) p ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))]
    exact hp0
  have hge : ∀ P ∈ IsDedekindDomain.primesOverFinset p (𝓞 E),
      1 ≤ p.ramificationIdx' P * p.inertiaDeg' P := by
    intro P hP
    have hP' : P ∈ p.primesOver (𝓞 E) := by
      rw [← IsDedekindDomain.coe_primesOverFinset hp0]
      exact hP
    haveI := hP'.1
    haveI := hP'.2
    have he : p.ramificationIdx' P ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx'_ne_zero hmap hP'.1
        (Ideal.map_le_iff_le_comap.mpr (le_of_eq (Ideal.over_def P p)))
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero he (Ideal.inertiaDeg'_pos p P).ne')
  have hone := (Finset.sum_eq_sum_iff_of_le hge).mp (by
    rw [← Finset.card_eq_sum_ones, hcard, hsum])
  rw [NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hgp]
  intro P hPprime hgP
  have hunder : p = P.under ℤ := by
    have hle : p ≤ P.under ℤ := by
      rw [hp_def, Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_comap.mpr (by simpa using hgP)
    exact hpmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
  haveI : P.LiesOver p := ⟨hunder⟩
  have hPF : P ∈ IsDedekindDomain.primesOverFinset p (𝓞 E) := by
    rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset hp0]
    exact ⟨hPprime, this⟩
  have he := Nat.eq_one_of_mul_eq_one_right (hone P hPF).symm
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
    ← Ideal.ramificationIdx'_eq_ramificationIdx p P hp0]
  exact he
end _root_.GlobalTheory.SplitEmbSep
end GlobalTheory.SplitEmbSep
