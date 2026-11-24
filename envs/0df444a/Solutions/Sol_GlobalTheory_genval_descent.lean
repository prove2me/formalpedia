-- Prove2me | solution 1 for GlobalTheory.genval_descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:59:09.929159+00:00
-- url     : https://prove2.me/submissions/619fda5c-a590-4f8b-bf0e-b592e8bc11b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAlgClosedTranscendentalSpecialisingEverywh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (ιV : K →+* V) (sV v : V) (a : K) (hsa : sV - ιV a ∈ maximalIdeal V) (hne : sV - ιV a ≠ 0) :
    ∀ n : ℕ, ∀ p : Polynomial (Polynomial K), p.leadingCoeff.natDegree = n → p ≠ 0 →
      p.eval₂ (eval₂RingHom ιV sV) v = 0 →
      ∃ q : Polynomial K, q ≠ 0 ∧ q.eval₂ ((residue V).comp ιV) (residue V v) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hn hp hpv
  by_cases hq : p.map (evalRingHom a) = 0
  · have hdvd : C (X - C a) ∣ p := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      rw [dvd_iff_isRoot]
      have := congrArg (fun q => q.coeff i) hq
      simpa [coeff_map] using this
    obtain ⟨p', rfl⟩ := hdvd
    have hp' : p' ≠ 0 := by rintro rfl; simp at hp
    have hXa : (X - C a : Polynomial K) ≠ 0 := X_sub_C_ne_zero a
    refine ih p'.leadingCoeff.natDegree ?_ p' rfl hp' ?_
    · rw [← hn, leadingCoeff_mul, leadingCoeff_C,
        natDegree_mul hXa (leadingCoeff_ne_zero.mpr hp'), natDegree_X_sub_C]
      omega
    · rw [eval₂_mul, eval₂_C] at hpv
      have h2 : (eval₂RingHom ιV sV) (X - C a) = sV - ιV a := by simp
      rw [h2] at hpv
      exact (mul_eq_zero.mp hpv).resolve_left hne
  · refine ⟨_, hq, ?_⟩
    have h1 : (residue V).comp (eval₂RingHom ιV sV) =
        ((residue V).comp ιV).comp (evalRingHom a) := by
      apply Polynomial.ringHom_ext
      · intro c; simp
      · have : residue V sV = residue V (ιV a) := by
          rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hsa
        simpa using this
    rw [eval₂_map, ← h1, ← hom_eval₂, hpv, map_zero]
end GlobalTheory
