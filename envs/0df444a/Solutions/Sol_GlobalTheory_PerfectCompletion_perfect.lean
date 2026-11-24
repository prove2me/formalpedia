-- Prove2me | solution 1 for GlobalTheory.PerfectCompletion.perfect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:37:40.286072+00:00
-- url     : https://prove2.me/submissions/947bbae4-74a7-4f7e-a6b3-0849c95df028

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionPrincipalPerfect
import Theorems.Thm_GlobalTheory_PerfectCompletion_eval_eq_zero_iff
import Theorems.Thm_GlobalTheory_PerfectCompletion_complete
import Theorems.Thm_GlobalTheory_PerfectCompletion_dense
import Theorems.Thm_GlobalTheory_PerfectCompletion_dvd_iff
import Theorems.Thm_GlobalTheory_PerfectCompletion_sModEq_iff
import Theorems.Thm_GlobalTheory_PerfectCompletion_pow_root
import Theorems.Thm_GlobalTheory_PerfectCompletion_dvd_of_pow_dvd_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PerfectCompletion
namespace GlobalTheory.PerfectCompletion
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (V : Type) [CommRing V] [CharP V l]
    [PerfectRing V l] (x : V), ((l : ℕ) : AdicCompletion (Ideal.span {x}) V) = 0 ∧
      Function.Bijective fun y : AdicCompletion (Ideal.span {x}) V => y ^ l := by
  intro l hl V _ _ _ x
  set C := AdicCompletion (Ideal.span {x}) V
  set X := algebraMap V C x with hX
  have h0 : ((l : ℕ) : C) = 0 := by
    rw [← map_natCast (algebraMap V C), CharP.cast_eq_zero, map_zero]
  refine ⟨h0, ?_⟩
  rcases subsingleton_or_nontrivial C with hC | hC
  · exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨y, Subsingleton.elim _ _⟩⟩
  haveI : CharP C l := (CharP.charP_iff_prime_eq_zero hl.out).mpr h0
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hle : ∀ n : ℕ, n ≤ l * n := fun n => Nat.le_mul_of_pos_left n hl.out.pos
  refine ⟨fun y z hyz => ?_, fun y => ?_⟩
  ·
    have hw : (y - z) ^ l = 0 := by
      simp only at hyz
      rw [sub_pow_char, hyz, sub_self]
    rw [← sub_eq_zero]
    set w := y - z
    refine AdicCompletion.ext fun n => ?_
    rw [← AdicCompletion.eval_apply, ← AdicCompletion.eval_apply, map_zero, eval_eq_zero_iff]
    obtain ⟨s, t, hst⟩ := dense x w (l * n)
    have h1 : X ^ (l * n) ∣ algebraMap V C (s ^ l) := by
      have e : algebraMap V C (s ^ l) = -((X ^ (l * n)) ^ l * t ^ l) := by
        rw [map_pow, eq_neg_iff_add_eq_zero, ← mul_pow, ← add_pow_char, ← hst, hw]
      rw [e, dvd_neg]
      exact dvd_mul_of_dvd_left (dvd_pow_self _ hl0) _
    rw [dvd_iff] at h1
    have h2 := dvd_of_pow_dvd_pow l x s n h1
    rw [hst]
    refine dvd_add ?_ (dvd_mul_of_dvd_left (pow_dvd_pow X (hle n)) _)
    rw [dvd_iff]
    exact h2
  ·
    choose s t hst using fun n => dense x y (l * n)
    set b : ℕ → V := fun n => (frobeniusEquiv V l).symm (s n) with hb
    have hbs : ∀ n, b n ^ l = s n := fun n => pow_root l (s n)
    have hcau : ∀ {m n : ℕ}, m ≤ n →
        algebraMap V C (b m) ≡ algebraMap V C (b n) [SMOD (Ideal.span {X} ^ m • ⊤ : Submodule C C)] := by
      intro m n hmn
      rw [sModEq_iff, ← map_sub, dvd_iff]
      refine dvd_of_pow_dvd_pow l x _ m ?_
      rw [sub_pow_char, hbs, hbs, ← dvd_iff, map_sub]
      have e : algebraMap V C (s m) - algebraMap V C (s n) = X ^ (l * n) * t n - X ^ (l * m) * t m := by
        have := hst m; have := hst n; linear_combination hst n - hst m
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_left (pow_dvd_pow X (Nat.mul_le_mul_left l hmn)) _)
        (dvd_mul_right _ _)
    obtain ⟨L, hL⟩ := (complete x).toIsPrecomplete.prec hcau
    refine ⟨L, ?_⟩
    simp only
    rw [← sub_eq_zero]
    refine (complete x).toIsHausdorff.haus _ fun n => ?_
    rw [sModEq_iff, sub_zero]
    obtain ⟨u, hu⟩ := (sModEq_iff _ _ _ _).1 (hL n)
    have e : L ^ l - y = -((X ^ n) ^ l * u ^ l) - X ^ (l * n) * t n := by
      have hL' : L = algebraMap V C (b n) - X ^ n * u := by rw [← hu]; ring
      rw [hL', sub_pow_char, ← map_pow, hbs, mul_pow]
      linear_combination -(hst n)
    rw [e]
    exact dvd_sub (dvd_neg.2 (dvd_mul_of_dvd_left (dvd_pow_self _ hl0) _))
      (dvd_mul_of_dvd_left (pow_dvd_pow X (hle n)) _)
end GlobalTheory.PerfectCompletion
