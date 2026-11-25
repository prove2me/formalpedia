-- Prove2me | solution 1 for GlobalTheory.LocalGenerators.local_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:21.455454+00:00
-- url     : https://prove2.me/submissions/a777abb3-4905-48ae-be06-bc04adb0e26c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LocalGenerators
namespace GlobalTheory.LocalGenerators
theorem _root_.solution {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : IsDedekindDomain.HeightOneSpectrum R) (J : Ideal R) (hJ : J ≠ ⊥) :
    ∃ d ∈ J, d ≠ (0 : R) ∧ ∃ s ∉ P.asIdeal, ∀ y ∈ J, ∃ o : R, s * y = o * d := by
  have hP : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
  have hlt : ¬ J ≤ J * P.asIdeal := by
    intro h
    have heq : J * P.asIdeal = J * ⊤ := by
      rw [Ideal.mul_top]; exact le_antisymm Ideal.mul_le_left h
    exact hP (mul_left_cancel₀ hJ heq)
  obtain ⟨d, hdJ, hdn⟩ := SetLike.not_le_iff_exists.mp hlt
  have hd0 : d ≠ 0 := by
    rintro rfl; exact hdn (Submodule.zero_mem _)
  have hdvd : J ∣ Ideal.span {d} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem J).mpr hdJ)
  obtain ⟨K, hK⟩ := hdvd
  have hKP : ¬ K ≤ P.asIdeal := by
    intro h
    apply hdn
    have : Ideal.span {d} ≤ J * P.asIdeal := hK ▸ Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self d)
  obtain ⟨s, hsK, hsP⟩ := SetLike.not_le_iff_exists.mp hKP
  refine ⟨d, hdJ, hd0, s, hsP, ?_⟩
  intro y hy
  have hm : s * y ∈ Ideal.span {d} := by
    rw [hK, mul_comm s y]; exact Ideal.mul_mem_mul hy hsK
  obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.mp hm
  exact ⟨o, ho.symm⟩
end GlobalTheory.LocalGenerators
