-- Prove2me | solution 1 for GlobalTheory.CMModel.exists_prime_natCast_mem_pow_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:04:00.606582+00:00
-- url     : https://prove2.me/submissions/55fba51e-8c31-466d-aeff-ce0ad09fdcbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimeNatCastMemPowOfRingHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMModel
namespace GlobalTheory.CMModel
theorem _root_.solution :
    ∀ (F H : Type) [Field F] [NumberField F] [Field H] [NumberField H] (f : F →+* H) (w : HeightOneSpectrum (𝓞 F)) (p n : ℕ), (p : 𝓞 F) ∈ w.asIdeal ^ n → ∃ P : Ideal (𝓞 H), P.IsPrime ∧ P ≠ ⊥ ∧ (p : 𝓞 H) ∈ P ^ n := by
  intro F H _ _ _ _ f w p n hp
  letI : Algebra F H := f.toAlgebra
  haveI := w.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 H) w.asIdeal
  refine ⟨P, hPm.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot P, ?_⟩
  have hle : w.asIdeal.map (algebraMap (𝓞 F) (𝓞 H)) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq hP.over
  have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 H)) hp
  rw [Ideal.map_pow, map_natCast] at h1
  exact Ideal.pow_right_mono hle n h1
end GlobalTheory.CMModel
