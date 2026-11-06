-- Prove2me | solution 1 for OAI.FiniteRingSieve.complete_character_plancherel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:04:25.14291+00:00
-- url     : https://prove2.me/submissions/99f81396-1e3c-486a-972d-308c2a7297a0

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FiniteRingSieve_unit_char_orthogonal

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.FiniteRingSieve
variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
attribute [local instance] OAI.FiniteRingSieve.logProfilesFintypeMulChar
attribute [local instance] logProfilesFintypeMulChar
namespace OAI.FiniteRingSieve
theorem _root_.solution (a : Rˣ → ℂ) :
    (∑ χ : MulChar R ℂ, ‖∑ u : Rˣ, a u * χ (u : R)‖ ^ 2) =
      (Fintype.card Rˣ : ℝ) * ∑ u : Rˣ, ‖a u‖ ^ 2 := by
  classical
  have hnorm (χ : MulChar R ℂ) :
      (↑(‖∑ u : Rˣ, a u * χ (u : R)‖ ^ 2) : ℂ) =
        (∑ u : Rˣ, star (a u) * star (χ (u : R))) *
          (∑ v : Rˣ, a v * χ (v : R)) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul, starRingEnd_apply]
  apply Complex.ofReal_inj.mp
  rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sum]
  simp_rw [hnorm]
  calc
    (∑ χ : MulChar R ℂ,
        (∑ u : Rˣ, star (a u) * star (χ (u : R))) *
          (∑ v : Rˣ, a v * χ (v : R))) =
      ∑ u : Rˣ, ∑ v : Rˣ,
        (star (a u) * a v) *
          ∑ χ : MulChar R ℂ, star (χ (u : R)) * χ (v : R) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1
        funext u
        rw [Finset.sum_comm]
        congr 1
        funext v
        calc
          (∑ χ : MulChar R ℂ,
              star (a u) * star (χ (u : R)) * (a v * χ (v : R))) =
            ∑ χ : MulChar R ℂ,
              (star (a u) * a v) * (star (χ (u : R)) * χ (v : R)) := by
              apply Finset.sum_congr rfl
              intro χ _
              ring
          _ = _ := by rfl
    _ = (Fintype.card Rˣ : ℂ) * ∑ u : Rˣ, (↑(‖a u‖ ^ 2) : ℂ) := by
        simp_rw [unit_char_orthogonal]
        simp_rw [mul_ite]
        simp only [mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        simp [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, Finset.mul_sum,
          mul_comm, mul_left_comm]
end OAI.FiniteRingSieve
