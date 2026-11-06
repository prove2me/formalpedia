-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.rational_prime_ideal_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:51:48.735651+00:00
-- url     : https://prove2.me/submissions/789713f4-eacf-4a23-bb4d-f91db24d2ae2

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Theorems.Thm_OAI_ActualEisensteinCubic_rational_qNat
import Theorems.Thm_OAI_ActualEisensteinCubic_rational_prime_factor_cases
import Theorems.Thm_OAI_ActualEisensteinCubic_maximal_ideal_eq_span_of_mem

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
    ∃ a b : O, a ≠ 0 ∧ b ≠ 0 ∧
      r ≤ qNat a ∧ r ≤ qNat b ∧
      ∀ (Q : Ideal O), Q.IsMaximal → (r : O) ∈ Q →
        Q = Ideal.span {a} ∨ Q = Ideal.span {b} := by
  rcases rational_prime_factor_cases r hr with hmax |
      ⟨a, b, ha0, hb0, hab, hqa, hqb, hma, hmb⟩
  · have hr0 : (r : O) ≠ 0 := by exact_mod_cast hr.ne_zero
    have hq : qNat (r : O) = r ^ 2 := rational_qNat r hr.ne_zero
    have hrle : r ≤ r ^ 2 := by nlinarith [hr.two_le]
    refine ⟨(r : O), (r : O), hr0, hr0, ?_, ?_, ?_⟩
    · rw [hq]; exact hrle
    · rw [hq]; exact hrle
    · intro Q hQ hrQ
      exact Or.inl (maximal_ideal_eq_span_of_mem Q hQ (r : O) hmax hrQ)
  · refine ⟨a, b, ha0, hb0, ?_, ?_, ?_⟩
    · rw [hqa]
    · rw [hqb]
    · intro Q hQ hrQ
      rw [hab] at hrQ
      rcases hQ.isPrime.mem_or_mem hrQ with haQ | hbQ
      · exact Or.inl (maximal_ideal_eq_span_of_mem Q hQ a hma haQ)
      · exact Or.inr (maximal_ideal_eq_span_of_mem Q hQ b hmb hbQ)
end OAI.ActualEisensteinCubic
