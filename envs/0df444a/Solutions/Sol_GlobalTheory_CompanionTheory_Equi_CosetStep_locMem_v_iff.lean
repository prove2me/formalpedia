-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.CosetStep.locMem_v_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:45:09.1398+00:00
-- url     : https://prove2.me/submissions/05b4f2eb-8cee-4438-bc7c-3f8b175b114d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetCongruenceRefinement
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_exists_pow_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_val_le_of_mem_pow
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_mem_pow_of_val_le
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_val_eq_one_of_not_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.CosetStep
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.Equi.CosetStep
theorem _root_.solution {I : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)} (hI : ¬ I ≤ v.asIdeal) (k : ℕ)
    (t : F) : LocMem (I * v.asIdeal ^ k) v t ↔ v.valuation F t ≤ WithZero.exp (-(k : ℤ)) := by
  constructor
  · rintro ⟨s, hs, y, hy, h⟩
    have h1 := val_le_of_mem_pow v ((Ideal.mul_le_right : I * v.asIdeal ^ k ≤ v.asIdeal ^ k) hy)
    have h2 := val_eq_one_of_not_mem v hs
    have h3 : v.valuation F (algebraMap (𝓞 F) F s * t) = v.valuation F (algebraMap (𝓞 F) F y) := by
      exact congrArg (v.valuation F) h
    rw [map_mul, h2, one_mul] at h3
    rw [h3]
    exact h1
  · intro ht
    obtain ⟨s0, hs0I, hs0v⟩ := SetLike.not_le_iff_exists.mp hI
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) t
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbF : algebraMap (𝓞 F) F b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hspan : Ideal.span {b} ≠ ⊥ := by
      rwa [Ne, Ideal.span_singleton_eq_bot]
    obtain ⟨m, B, hbB, hBv⟩ := exists_pow_mul v hspan
    obtain ⟨c, hcB, hcv⟩ := SetLike.not_le_iff_exists.mp hBv
    have hbm : b ∈ v.asIdeal ^ m := by
      have hb' : b ∈ Ideal.span {b} := Ideal.subset_span rfl
      rw [hbB] at hb'
      exact (Ideal.mul_le_left : v.asIdeal ^ m * B ≤ v.asIdeal ^ m) hb'
    have hk1 : WithZero.exp (-(k : ℤ)) ≤ 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    have hvala : v.valuation F (algebraMap (𝓞 F) F a) ≤ WithZero.exp (-(m : ℤ)) := by
      have e : algebraMap (𝓞 F) F a =
          (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) * algebraMap (𝓞 F) F b := by
        field_simp
      rw [e, map_mul]
      calc _ ≤ 1 * WithZero.exp (-(m : ℤ)) := mul_le_mul' (ht.trans hk1) (val_le_of_mem_pow v hbm)
        _ = _ := one_mul _
    have ham : a ∈ v.asIdeal ^ m := mem_pow_of_val_le v hvala
    have hac : a * c ∈ Ideal.span {b} := by
      rw [hbB]
      exact Ideal.mul_mem_mul ham hcB
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hac
    have hrF : algebraMap (𝓞 F) F c * (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) =
        algebraMap (𝓞 F) F r := by
      have := congrArg (algebraMap (𝓞 F) F) hr
      rw [map_mul, map_mul] at this
      field_simp
      linear_combination -this
    have hvr : v.valuation F (algebraMap (𝓞 F) F r) ≤ WithZero.exp (-(k : ℤ)) := by
      rw [← hrF, map_mul, val_eq_one_of_not_mem v hcv, one_mul]
      exact ht
    have hrk : r ∈ v.asIdeal ^ k := mem_pow_of_val_le v hvr
    refine ⟨s0 * c, fun hm => (v.isPrime.mem_or_mem hm).elim hs0v hcv, s0 * r,
      Ideal.mul_mem_mul hs0I hrk, ?_⟩
    have e1 : ((s0 * c : 𝓞 F) : F) = algebraMap (𝓞 F) F s0 * algebraMap (𝓞 F) F c := by
      rw [← map_mul]
    have e2 : ((s0 * r : 𝓞 F) : F) = algebraMap (𝓞 F) F s0 * algebraMap (𝓞 F) F r := by
      rw [← map_mul]
    rw [e1, e2, ← hrF]
    ring
end GlobalTheory.CompanionTheory.Equi.CosetStep
