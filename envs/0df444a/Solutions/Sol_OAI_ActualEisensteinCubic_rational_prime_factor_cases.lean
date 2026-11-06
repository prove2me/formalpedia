-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.rational_prime_factor_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:50:08.922043+00:00
-- url     : https://prove2.me/submissions/6b7f2686-24f6-4f5e-af7a-a98874177f9f

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Theorems.Thm_OAI_ActualEisensteinCubic_rational_qNat
import Theorems.Thm_OAI_ActualEisensteinCubic_rational_qNat_eq_one_iff
import Theorems.Thm_OAI_ActualEisensteinCubic_qNat_eq_absNorm_span
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftLatticeCount_qNat_mul
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open OAI.ActualEisensteinCubic
open ShortDraftLatticeCount
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (r : ℕ) (hr : r.Prime) :
    (Ideal.span {(r : O)} : Ideal O).IsMaximal ∨
    ∃ a b : O, a ≠ 0 ∧ b ≠ 0 ∧ (r : O) = a * b ∧
      qNat a = r ∧ qNat b = r ∧
      (Ideal.span {a} : Ideal O).IsMaximal ∧
      (Ideal.span {b} : Ideal O).IsMaximal := by
  have hru : ¬ IsUnit (r : O) := by
    rw [← rational_qNat_eq_one_iff, rational_qNat r hr.ne_zero]
    have htwo := hr.two_le
    nlinarith
  rcases irreducible_or_factor hru with hirr | ⟨a, b, hna, hnb, hab⟩
  · left
    exact PrincipalIdealRing.isMaximal_of_irreducible hirr
  · right
    have hqa1 : qNat a ≠ 1 := by
      intro h
      exact hna ((rational_qNat_eq_one_iff a).mp h)
    have hqb1 : qNat b ≠ 1 := by
      intro h
      exact hnb ((rational_qNat_eq_one_iff b).mp h)
    have hqprod : qNat a * qNat b = r ^ 2 := by
      rw [← qNat_mul, ← hab, rational_qNat r hr.ne_zero]
    obtain ⟨hqa, hqb⟩ := (hr.mul_eq_prime_sq_iff hqa1 hqb1).mp hqprod
    have ha0 : a ≠ 0 := by
      intro h
      have hqa0 : qNat a = 0 := by simp [h, qNat_eq_absNorm_span]
      rw [hqa] at hqa0
      exact hr.ne_zero hqa0
    have hb0 : b ≠ 0 := by
      intro h
      have hqb0 : qNat b = 0 := by simp [h, qNat_eq_absNorm_span]
      rw [hqb] at hqb0
      exact hr.ne_zero hqb0
    have hpa : Prime a := by
      apply Ideal.prime_of_irreducible_absNorm_span ha0
      rw [← qNat_eq_absNorm_span, hqa]
      exact hr.prime.irreducible
    have hpb : Prime b := by
      apply Ideal.prime_of_irreducible_absNorm_span hb0
      rw [← qNat_eq_absNorm_span, hqb]
      exact hr.prime.irreducible
    exact ⟨a, b, ha0, hb0, hab, hqa, hqb,
      PrincipalIdealRing.isMaximal_of_irreducible hpa.irreducible,
      PrincipalIdealRing.isMaximal_of_irreducible hpb.irreducible⟩
end OAI.ActualEisensteinCubic
