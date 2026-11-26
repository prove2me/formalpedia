-- Prove2me | solution 1 for Malliavin.integral_stepIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:18.559807+00:00
-- url     : https://prove2.me/submissions/0e22863a-0149-44a6-9242-fc134fb68ec6

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_Malliavin_IteratedIntegral

set_option autoImplicit false
open Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
variable {W : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hW : IsWienerCov W) {n : ℕ} (P : Partition n)
    (a : Fin n → ℝ) :
    ∫ x, stepIntegral W P a x = 0 := by
  have hint2 : ∀ i : Fin n,
      Integrable fun x => W (P.t i.succ) x - W (P.t i.castSucc) x :=
    fun i => (hW.integrable_W _).sub (hW.integrable_W _)
  have hsub : ∀ i : Fin n,
      ∫ x, W (P.t i.succ) x - W (P.t i.castSucc) x = 0 := by
    intro i
    have hs : Integrable fun x => W (P.t i.succ) x := hW.integrable_W _
    have hc : Integrable fun x => W (P.t i.castSucc) x := hW.integrable_W _
    have key : ∫ x, W (P.t i.succ) x - W (P.t i.castSucc) x
        = (∫ x, W (P.t i.succ) x) - (∫ x, W (P.t i.castSucc) x) :=
      integral_sub hs hc
    rw [key, hW.mean_zero, hW.mean_zero, sub_self]
  have hint : ∀ i : Fin n,
      Integrable fun x => a i * (W (P.t i.succ) x - W (P.t i.castSucc) x) :=
    fun i => (hint2 i).const_mul _
  have hf : (fun x => stepIntegral W P a x)
      = fun x => ∑ i : Fin n, a i * (W (P.t i.succ) x - W (P.t i.castSucc) x) :=
    funext fun _ => rfl
  have hsplit : ∫ x, stepIntegral W P a x
      = ∑ i : Fin n, ∫ x, a i * (W (P.t i.succ) x - W (P.t i.castSucc) x) := by
    rw [hf]
    exact integral_finsetSum Finset.univ (fun i _ => hint i)
  rw [hsplit]
  exact Finset.sum_eq_zero fun i _ => by
    have hcm : ∫ x, a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)
        = a i * (∫ x, W (P.t i.succ) x - W (P.t i.castSucc) x) :=
      integral_const_mul _ _
    rw [hcm, hsub i, mul_zero]
end Malliavin
