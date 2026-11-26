-- Prove2me | solution 1 for Malliavin.ito_isometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:19.531852+00:00
-- url     : https://prove2.me/submissions/535abffc-bfaf-41d3-bad6-f62eaa11acd2

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_Malliavin_IteratedIntegral
import Theorems.Thm_Malliavin_integral_cov_partition

set_option autoImplicit false
open Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
variable {W : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hW : IsWienerCov W) {n : ℕ} (P : Partition n) (a b : Fin n → ℝ) :
    ∫ x, stepIntegral W P a x * stepIntegral W P b x
      = ∑ i : Fin n, a i * b i * ((P.t i.succ : ℝ) - (P.t i.castSucc : ℝ)) := by
  have hΔint : ∀ i j : Fin n,
      Integrable fun x : Ω => (W (P.t i.succ) x - W (P.t i.castSucc) x) *
        (W (P.t j.succ) x - W (P.t j.castSucc) x) := by
    intro i j
    have hfun : (fun x => (W (P.t i.succ) x - W (P.t i.castSucc) x) *
        (W (P.t j.succ) x - W (P.t j.castSucc) x))
        = fun x => (W (P.t i.succ) x * W (P.t j.succ) x
              - W (P.t i.succ) x * W (P.t j.castSucc) x)
            - (W (P.t i.castSucc) x * W (P.t j.succ) x
              - W (P.t i.castSucc) x * W (P.t j.castSucc) x) :=
      funext fun x => by ring
    rw [hfun]
    exact Integrable.sub ((hW.integrable_prod _ _).sub (hW.integrable_prod _ _))
      ((hW.integrable_prod _ _).sub (hW.integrable_prod _ _))
  have hint : ∀ i j : Fin n,
      Integrable fun x : Ω => (a i * b j) * ((W (P.t i.succ) x - W (P.t i.castSucc) x) *
        (W (P.t j.succ) x - W (P.t j.castSucc) x)) :=
    fun i j => (hΔint i j).const_mul _
  have hdouble : ∀ f : Fin n → Fin n → Ω → ℝ, (∀ i j, Integrable (f i j)) →
      ∫ x, ∑ i, ∑ j, f i j x = ∑ i, ∑ j, ∫ x, f i j x := by
    intro f hf
    rw [integral_finsetSum Finset.univ
      (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hf i j))]
    exact Finset.sum_congr rfl fun i _ =>
      integral_finsetSum Finset.univ (fun j _ => hf i j)
  have hexpandf : (fun x => stepIntegral W P a x * stepIntegral W P b x)
      = fun x => ∑ i : Fin n, ∑ j : Fin n,
          (a i * b j) * ((W (P.t i.succ) x - W (P.t i.castSucc) x) *
            (W (P.t j.succ) x - W (P.t j.castSucc) x)) := by
    funext x
    change (∑ i : Fin n, a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)) *
         (∑ j : Fin n, b j * (W (P.t j.succ) x - W (P.t j.castSucc) x))
       = ∑ i : Fin n, ∑ j : Fin n,
          (a i * b j) * ((W (P.t i.succ) x - W (P.t i.castSucc) x) *
            (W (P.t j.succ) x - W (P.t j.castSucc) x))
    calc (∑ i : Fin n, a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)) *
         (∑ j : Fin n, b j * (W (P.t j.succ) x - W (P.t j.castSucc) x))
        = ∑ i : Fin n, (a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)) *
            (∑ j : Fin n, b j * (W (P.t j.succ) x - W (P.t j.castSucc) x)) :=
          Finset.sum_mul _ _ _
      _ = ∑ i : Fin n, ∑ j : Fin n,
            (a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)) *
            (b j * (W (P.t j.succ) x - W (P.t j.castSucc) x)) :=
          Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
      _ = ∑ i : Fin n, ∑ j : Fin n,
            (a i * b j) * ((W (P.t i.succ) x - W (P.t i.castSucc) x) *
              (W (P.t j.succ) x - W (P.t j.castSucc) x)) :=
          Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => by ring
  have hsplit : ∫ x, stepIntegral W P a x * stepIntegral W P b x
      = ∑ i : Fin n, ∑ j : Fin n,
          ∫ x, (a i * b j) * ((W (P.t i.succ) x - W (P.t i.castSucc) x) *
            (W (P.t j.succ) x - W (P.t j.castSucc) x)) := by
    rw [hexpandf]
    exact hdouble _ hint
  have hconst : ∀ i j : Fin n,
      ∫ x, (a i * b j) * ((W (P.t i.succ) x - W (P.t i.castSucc) x) *
        (W (P.t j.succ) x - W (P.t j.castSucc) x))
        = a i * b j *
            (if i = j then (P.t i.succ : ℝ) - (P.t i.castSucc : ℝ) else 0) := by
    intro i j
    have key : ∫ x, (a i * b j) * ((W (P.t i.succ) x - W (P.t i.castSucc) x) *
        (W (P.t j.succ) x - W (P.t j.castSucc) x))
        = a i * b j * ∫ x, (W (P.t i.succ) x - W (P.t i.castSucc) x) *
          (W (P.t j.succ) x - W (P.t j.castSucc) x) :=
      integral_const_mul _ _
    rw [key, integral_cov_partition hW P]
  calc ∫ x, stepIntegral W P a x * stepIntegral W P b x
      = ∑ i : Fin n, ∑ j : Fin n,
          ∫ x, (a i * b j) * ((W (P.t i.succ) x - W (P.t i.castSucc) x) *
            (W (P.t j.succ) x - W (P.t j.castSucc) x)) := hsplit
    _ = ∑ i : Fin n, ∑ j : Fin n,
          a i * b j *
            (if i = j then (P.t i.succ : ℝ) - (P.t i.castSucc : ℝ) else 0) :=
        Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => hconst i j
    _ = ∑ i : Fin n, a i * b i * ((P.t i.succ : ℝ) - (P.t i.castSucc : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i _
        have h0 : ∀ j : Fin n, j ≠ i →
            a i * b j *
              (if i = j then (P.t i.succ : ℝ) - (P.t i.castSucc : ℝ) else 0) = 0 := by
          intro j hj
          rw [if_neg (Ne.symm hj), mul_zero]
        have hsingle := Finset.sum_eq_single i (fun j _ hj => h0 j hj)
          (fun hni => absurd (Finset.mem_univ i) hni)
        rw [hsingle, if_pos rfl]
end Malliavin
