-- Prove2me | solution 1 for GlobalTheory.QFam.QAllSubring.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:21.061556+00:00
-- url     : https://prove2.me/submissions/5d2e0440-40e5-42c3-a832-6318d8226016

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionCoeffsInSubringRingClosed
import Theorems.Thm_GlobalTheory_QFam_hasQ_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam GlobalTheory.QFam.QAllSubring
variable {R : Subring ℂ} {N : ℕ}
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
variable {R : Subring ℂ} {N : ℕ}
namespace GlobalTheory.QFam.QAllSubring
namespace _root_.GlobalTheory.QFam.QAllSubring
theorem _root_.solution {f g : ℍ → ℂ} (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f)
    (hg : _root_.GlobalTheory.QFam.QAll (· ∈ R) N g) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ * g τ := by
  obtain ⟨a, ha, haR⟩ := hf
  obtain ⟨b, hb, hbR⟩ := hg
  refine ⟨fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2, ?_,
    fun n => R.sum_mem fun kl _ => R.mul_mem (haR kl.1) (hbR kl.2)⟩
  rw [_root_.GlobalTheory.QFam.hasQ_iff] at ha hb ⊢
  intro τ
  set q := Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N)
  have hsa : Summable fun n => ‖a n * q ^ n‖ := summable_norm_iff.mpr (ha τ).summable
  have hsb : Summable fun n => ‖b n * q ^ n‖ := summable_norm_iff.mpr (hb τ).summable
  have hterm : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      a kl.1 * q ^ kl.1 * (b kl.2 * q ^ kl.2) =
      (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2) * q ^ n := by
    intro n
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hkl, pow_add]
    ring
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hsa hsb
  have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsa hsb
  rw [(ha τ).tsum_eq, (hb τ).tsum_eq] at heq
  rw [heq]
  simp only [hterm] at hs ⊢
  exact (summable_norm_iff.mp hs).hasSum
end _root_.GlobalTheory.QFam.QAllSubring
end GlobalTheory.QFam.QAllSubring
