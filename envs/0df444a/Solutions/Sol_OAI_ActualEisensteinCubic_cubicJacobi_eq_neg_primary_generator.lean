-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicJacobi_eq_neg_primary_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:07:32.942076+00:00
-- url     : https://prove2.me/submissions/96317cbf-2ca4-4047-85ee-09622bb7ce06

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_primary
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_unit_multiple
import Theorems.Thm_OAI_ActualEisensteinCubic_lambda_not_dvd_two

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
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hnorm : p * conjO p = (Nat.card (O ⧸ P) : O))
    (hprimary : lambda ^ 2 ∣ p - 1) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) = -p := by
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  obtain ⟨u, hJu⟩ := cubicJacobi_unit_multiple P hgood p hP hnorm
  change J = p * (u : O) at hJu
  obtain ⟨z, _, hJ⟩ := cubicJacobi_primary P hgood
  have hJmod : lambda ^ 2 ∣ J + 1 := by
    refine ⟨z, ?_⟩
    dsimp [J]
    rw [hJ]
    ring
  have hucong : lambda ^ 2 ∣ (u : O) + 1 := by
    have heq : (u : O) + 1 = (J + 1) - (p - 1) * (u : O) := by
      rw [hJu]
      ring
    rw [heq]
    exact dvd_sub hJmod (dvd_mul_of_dvd_left hprimary _)
  have hunit : u = 1 ∨ u = -1 := by
    apply IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) u
    refine ⟨(-1 : ℤ), ?_⟩
    simpa only [lambda, omega, Int.cast_neg, Int.cast_one, sub_neg_eq_add] using hucong
  rcases hunit with h1 | hneg
  · have htwo : lambda ^ 2 ∣ (2 : O) := by
      simpa [h1, one_add_one_eq_two] using hucong
    exact False.elim (lambda_not_dvd_two ((dvd_pow_self lambda (by decide)).trans htwo))
  · rw [hneg] at hJu
    simpa only [Units.val_neg, Units.val_one, mul_neg, mul_one] using hJu
end OAI.ActualEisensteinCubic
