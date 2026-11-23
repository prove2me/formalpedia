-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.CosetStep.exists_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:45.872599+00:00
-- url     : https://prove2.me/submissions/cf9f11b4-ebf6-4a2b-b1fb-64bc1349f94d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetCongruenceRefinement

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {D : Ideal (𝓞 F)} (hD : D ≠ ⊥) :
    ∃ (m : ℕ) (B : Ideal (𝓞 F)), D = v.asIdeal ^ m * B ∧ ¬ B ≤ v.asIdeal := by
  have hv : v.asIdeal ≠ ⊤ := v.isPrime.ne_top
  have hex : ∃ m : ℕ, ¬ D ≤ v.asIdeal ^ (m + 1) := by
    by_contra h
    push_neg at h
    apply hD
    have h' : D ≤ ⨅ i : ℕ, v.asIdeal ^ i := by
      refine le_iInf fun i => ?_
      cases i with
      | zero => simp
      | succ i => exact h i
    rw [Ideal.iInf_pow_eq_bot_of_isDomain _ hv] at h'
    exact le_bot_iff.mp h'
  obtain ⟨m, hm, hle⟩ : ∃ m : ℕ, ¬ D ≤ v.asIdeal ^ (m + 1) ∧ D ≤ v.asIdeal ^ m := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · simp [h0]
    · have h1 := Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)
      push_neg at h1
      have e : Nat.find hex - 1 + 1 = Nat.find hex := by omega
      rwa [e] at h1
  obtain ⟨B, hB⟩ := Ideal.dvd_iff_le.mpr hle
  refine ⟨m, B, hB, fun hBv => hm ?_⟩
  rw [hB, pow_succ]
  exact Ideal.mul_mono_right hBv
end GlobalTheory.CompanionTheory.Equi.CosetStep
