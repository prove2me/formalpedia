-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicJacobi_unit_multiple_of_principal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:40:06.716494+00:00
-- url     : https://prove2.me/submissions/6f649e29-33b8-4c89-a20e-e673702191e6

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_mem_prime
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_mul_conj
import Theorems.Thm_OAI_ActualEisensteinCubic_norm_int_eq_mul_conjO
section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
namespace ShortDraftFiniteGaussFourier
open scoped Classical
open AddChar MulChar
variable {F : Type*} [Field F] [Fintype F]
end ShortDraftFiniteGaussFourier
namespace PoissonChildCRT
open scoped Classical
variable (n : ℕ) (χ : MulChar (ZMod n) ℂ)
end PoissonChildCRT
namespace PoissonFirstLocal
open scoped Classical
end PoissonFirstLocal
open Finset Complex
namespace ActualCubicChar
variable {R F : Type*} [CommRing R] [IsDomain R] [Field F]
variable [Fintype F]
end ActualCubicChar
namespace ActualEisensteinCubic
section
open NumberField
end
private theorem generator_mul_conj_eq_sign_card (P : Ideal O) [P.IsMaximal]
    (p : O) (hP : P = Ideal.span {p}) :
    p * conjO p = (Nat.card (O ⧸ P) : O) ∨
      p * conjO p = -(Nat.card (O ⧸ P) : O) := by
  have habs : (Algebra.norm ℤ p).natAbs = Nat.card (O ⧸ P) := by
    calc
      (Algebra.norm ℤ p).natAbs = Ideal.absNorm (Ideal.span {p}) :=
        (Ideal.absNorm_span_singleton p).symm
      _ = Ideal.absNorm P := by rw [← hP]
      _ = Nat.card (O ⧸ P) := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hsq : (Algebra.norm ℤ p) * (Algebra.norm ℤ p) =
      (Nat.card (O ⧸ P) : ℤ) * (Nat.card (O ⧸ P) : ℤ) := by
    apply (Int.natAbs_eq_iff_mul_self_eq).mp
    simpa using habs
  have hzero : (Algebra.norm ℤ p - (Nat.card (O ⧸ P) : ℤ)) *
      (Algebra.norm ℤ p + (Nat.card (O ⧸ P) : ℤ)) = 0 := by
    nlinarith [hsq]
  rcases mul_eq_zero.mp hzero with hpos | hneg
  · left
    have heq : Algebra.norm ℤ p = (Nat.card (O ⧸ P) : ℤ) := sub_eq_zero.mp hpos
    simp [← norm_int_eq_mul_conjO p, heq]
  · right
    have heq : Algebra.norm ℤ p = -(Nat.card (O ⧸ P) : ℤ) := add_eq_zero_iff_eq_neg.mp hneg
    simp [← norm_int_eq_mul_conjO p, heq]
end ActualEisensteinCubic
end
end OAI
end

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p}) :
    ∃ u : Oˣ, jacobiSum (cubicChar P hgood) (cubicChar P hgood) = p * u := by
  classical
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  have hdiv : p ∣ J := (Ideal.mem_span_singleton).mp (hP ▸ cubicJacobi_mem_prime P hgood)
  obtain ⟨v, hv⟩ := hdiv
  have hqne : (Nat.card (O ⧸ P) : O) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hnorm := generator_mul_conj_eq_sign_card P p hP
  have hpne : p * conjO p ≠ 0 := by
    rcases hnorm with h | h
    · rw [h]; exact hqne
    · rw [h]; exact neg_ne_zero.mpr hqne
  have hprod : (p * conjO p) * (v * conjO v) = (Nat.card (O ⧸ P) : O) := by
    calc
      (p * conjO p) * (v * conjO v) = (p * v) * conjO (p * v) := by
        rw [map_mul]; ring
      _ = J * conjO J := by rw [hv]
      _ = (Nat.card (O ⧸ P) : O) := cubicJacobi_mul_conj P hgood
  have hvnorm : v * conjO v = 1 ∨ v * conjO v = -1 := by
    rcases hnorm with hpos | hneg
    · left
      apply mul_left_cancel₀ hpne
      calc
        (p * conjO p) * (v * conjO v) = (Nat.card (O ⧸ P) : O) := hprod
        _ = (p * conjO p) * 1 := by rw [hpos]; ring
    · right
      apply mul_left_cancel₀ hpne
      calc
        (p * conjO p) * (v * conjO v) = (Nat.card (O ⧸ P) : O) := hprod
        _ = (p * conjO p) * -1 := by rw [hneg]; ring
  have hvunit : IsUnit v := by
    rcases hvnorm with h | h
    · exact IsUnit.of_mul_eq_one (conjO v) h
    · apply IsUnit.of_mul_eq_one (-conjO v)
      rw [mul_neg, h]
      ring
  refine ⟨hvunit.unit, ?_⟩
  simpa only [hvunit.unit_spec] using hv
end OAI.ActualEisensteinCubic
