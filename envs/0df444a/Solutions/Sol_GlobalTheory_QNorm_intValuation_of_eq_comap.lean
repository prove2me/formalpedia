-- Prove2me | solution 1 for GlobalTheory.QNorm.intValuation_of_eq_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:43:43.015189+00:00
-- url     : https://prove2.me/submissions/63f9393f-d416-4420-a57f-8d3a360074c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain
open scoped WithZero
namespace GlobalTheory.QNorm
namespace _root_.GlobalTheory.QNorm
theorem _root_.solution {R : Type} [CommRing R] [IsDedekindDomain R]
    (e : R ≃+* R) (w w' : HeightOneSpectrum R) (h : w'.asIdeal = w.asIdeal.comap e) (x : R) :
    w'.intValuation x = w.intValuation (e x) := by
  have hmem : ∀ n : ℕ, x ∈ w'.asIdeal ^ n ↔ e x ∈ w.asIdeal ^ n := by
    intro n
    rw [h, ← Ideal.map_symm, ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap]
  have hle : ∀ n : ℕ, w'.intValuation x ≤ WithZero.exp (-(n : ℤ)) ↔
      w.intValuation (e x) ≤ WithZero.exp (-(n : ℤ)) := fun n => by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem,
      HeightOneSpectrum.intValuation_le_pow_iff_mem, hmem]
  by_cases hx : x = 0
  · subst hx
    simp
  · have hex : e x ≠ 0 := fun h0 => hx (e.injective (h0.trans (map_zero e).symm))
    rw [HeightOneSpectrum.intValuation_if_neg _ hx, HeightOneSpectrum.intValuation_if_neg _ hex]
      at hle ⊢
    set a := (Associates.mk w'.asIdeal).count (Associates.mk (Ideal.span {x})).factors
    set b := (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {e x})).factors
    have h1 := (hle a).1 le_rfl
    have h2 := (hle b).2 le_rfl
    simp only [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le] at h1 h2
    rw [le_antisymm h1 h2]
end _root_.GlobalTheory.QNorm
end GlobalTheory.QNorm
