-- Prove2me | solution 1 for OAI.KervaireStrong.StrongTendsto.exp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:09:45.742649+00:00
-- url     : https://prove2.me/submissions/33ce7785-fcdf-4b33-8a02-ceb2ba81aa3e

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits

open OAI OAI.KervaireStrong
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {ι : Type*} {l : Filter ι}
open Nat

theorem solution [CompleteSpace H] {T : ι → Operator H} {S : Operator H}
    (h : StrongTendsto T l S) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i, ‖T i‖ ≤ C) :
    StrongTendsto (fun i => NormedSpace.exp (T i)) l (NormedSpace.exp S) := by
  intro ξ
  have hexp : ∀ A : Operator H, NormedSpace.exp A ξ = ∑' n : ℕ, ((n ! : ℂ)⁻¹) • (A ^ n) ξ := by
    intro A
    rw [congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℂ)) A]
    have hs : Summable (fun n : ℕ => ((n ! : ℂ)⁻¹) • A ^ n) :=
      (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) A).of_norm
    have := (ContinuousLinearMap.apply ℂ H ξ).map_tsum hs
    simpa using this
  have hpow : ∀ n : ℕ, Tendsto (fun i => (T i ^ n) ξ) l (𝓝 ((S ^ n) ξ)) := by
    intro n
    induction n with
    | zero => simpa using tendsto_const_nhds
    | succ n ih =>
      simp only [_root_.pow_succ', ContinuousLinearMap.mul_apply]
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h1 := (tendsto_iff_norm_sub_tendsto_zero.1 ih).const_mul C
      have h2 := tendsto_iff_norm_sub_tendsto_zero.1 (h ((S ^ n) ξ))
      rw [mul_zero] at h1
      refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) (by simpa only [add_zero] using h1.add h2)
      calc ‖T i ((T i ^ n) ξ) - S ((S ^ n) ξ)‖
          = ‖T i ((T i ^ n) ξ - (S ^ n) ξ) + (T i ((S ^ n) ξ) - S ((S ^ n) ξ))‖ := by
            rw [map_sub]; congr 1; abel
        _ ≤ ‖T i ((T i ^ n) ξ - (S ^ n) ξ)‖ + ‖T i ((S ^ n) ξ) - S ((S ^ n) ξ)‖ := norm_add_le _ _
        _ ≤ C * ‖(T i ^ n) ξ - (S ^ n) ξ‖ + ‖T i ((S ^ n) ξ) - S ((S ^ n) ξ)‖ := by
            gcongr
            exact ((T i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _))
  have hpowb : ∀ i (n : ℕ), ‖(T i ^ n) ξ‖ ≤ C ^ n * ‖ξ‖ := by
    intro i n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [_root_.pow_succ', ContinuousLinearMap.mul_apply, _root_.pow_succ', mul_assoc]
      exact ((T i).le_opNorm _).trans (mul_le_mul (hb i) ih (norm_nonneg _) hC)
  simp_rw [hexp]
  refine tendsto_tsum_of_dominated_convergence (bound := fun n : ℕ => C ^ n / n ! * ‖ξ‖)
    ((Real.summable_pow_div_factorial C).mul_right _) (fun n => (hpow n).const_smul _)
    (Filter.Eventually.of_forall (fun i n => ?_))
  rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_mul_inv]
  calc (n ! : ℝ)⁻¹ * ‖(T i ^ n) ξ‖ ≤ (n ! : ℝ)⁻¹ * (C ^ n * ‖ξ‖) :=
        mul_le_mul_of_nonneg_left (hpowb i n) (by positivity)
    _ = C ^ n * (n ! : ℝ)⁻¹ * ‖ξ‖ := by ring

