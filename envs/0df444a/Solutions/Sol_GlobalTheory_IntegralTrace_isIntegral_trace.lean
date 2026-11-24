-- Prove2me | solution 1 for GlobalTheory.IntegralTrace.isIntegral_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:08:36.247878+00:00
-- url     : https://prove2.me/submissions/5c93989d-2534-4995-bc89-576b52899798

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMonicAevalEqZero
import Theorems.Thm_GlobalTheory_IntegralTrace_exists_monic_aeval_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.IntegralTrace
open Polynomial
namespace GlobalTheory.IntegralTrace
theorem _root_.solution {E : Type u_1} [inst : Field E] [NumberField E] (_φ : E →+* ℂ) {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.FG L)
    (hspan : Submodule.span E (↑L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, Matrix.mulVec M x ∈ L) :
    IsIntegral ℤ (Matrix.trace M) := by
  obtain ⟨p, hp, hp0⟩ := exists_monic_aeval_eq_zero L hL hspan M hM
  let K := AlgebraicClosure E
  let N : Matrix (Fin n) (Fin n) K := (algebraMap E K).mapMatrix M
  have hN : aeval N (p.map (algebraMap (NumberField.RingOfIntegers E) K)) = 0 := by
    have h1 := Polynomial.aeval_algHom_apply ((Algebra.ofId E K).mapMatrix (m := Fin n)) M
      (p.map (algebraMap (NumberField.RingOfIntegers E) E))
    rw [hp0, map_zero] at h1
    rw [IsScalarTower.algebraMap_eq (NumberField.RingOfIntegers E) E K, ← Polynomial.map_map,
      aeval_map_algebraMap]
    exact h1
  rw [← isIntegral_algebraMap_iff (algebraMap E K).injective]
  have htr : algebraMap E K M.trace = N.trace := by
    simp [N, Matrix.trace]
  rw [htr, Matrix.trace_eq_sum_roots_charpoly]
  apply IsIntegral.multiset_sum
  intro z hz
  have hz1 : z ∈ spectrum K N := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
    exact (Polynomial.mem_roots N.charpoly_monic.ne_zero).mp hz
  have hz2 := spectrum.subset_polynomial_aeval N
    (p.map (algebraMap (NumberField.RingOfIntegers E) K)) ⟨z, hz1, rfl⟩
  rw [hN] at hz2
  have hz3 : eval z (p.map (algebraMap (NumberField.RingOfIntegers E) K)) = 0 := by
    by_contra h
    rw [spectrum.mem_iff] at hz2
    apply hz2
    rw [sub_zero]
    exact (IsUnit.mk0 _ h).map _
  have hz4 : IsIntegral (NumberField.RingOfIntegers E) z := ⟨p, hp, by rwa [eval_map] at hz3⟩
  exact isIntegral_trans z hz4
end GlobalTheory.IntegralTrace
