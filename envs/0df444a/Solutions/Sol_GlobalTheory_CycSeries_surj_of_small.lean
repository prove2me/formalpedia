-- Prove2me | solution 1 for GlobalTheory.CycSeries.surj_of_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:41:07.719228+00:00
-- url     : https://prove2.me/submissions/1a2514d9-800e-4e39-a193-78ef87dd0bfa

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeTer
import Theorems.Thm_GlobalTheory_CycSeries_mulVec_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycSeries
variable {C : Type} [NormedField C]
namespace GlobalTheory.CycSeries
theorem _root_.solution [CompleteSpace C] {r : ℕ} (X : AddSubgroup C) (hX : IsClosed (X : Set C))
    (hX1 : ∀ x ∈ X, ‖x‖ ≤ 1) (g : C ≃+* C) (hg : Continuous g) (hgX : ∀ x ∈ X, g x ∈ X)
    (p q : C) (hq1 : ‖q‖ < 1) (hgq : g q = q) (hqX : ∀ x ∈ X, q * x ∈ X) (S : C → C)
    (hS : ∀ x ∈ X, S x ∈ X ∧ g (S x) - S x = p * x)
    (B : Matrix (Fin r) (Fin r) C)
    (hBX : ∀ a b, ∀ x ∈ X, B a b * x ∈ X) (w : Fin r → C) (hw : ∀ a, w a ∈ X) :
    ∃ y : Fin r → C, (∀ a, y a ∈ X) ∧
      ∀ a, g (y a) - y a + p * q * B.mulVec (fun b => g (y b)) a = p * w a := by
  let T : (Fin r → C) → (Fin r → C) := fun v a => -B.mulVec (fun b => g (S (v b))) a
  let v : ℕ → Fin r → C := fun n => T^[n] w
  have hvs : ∀ n, v (n + 1) = T (v n) := fun n => Function.iterate_succ_apply' T n w
  have hv : ∀ n a, v n a ∈ X := by
    intro n
    induction n with
    | zero => exact hw
    | succ n ih =>
      intro a
      rw [hvs]
      exact X.neg_mem (mulVec_mem X B hBX _ (fun b => hgX _ (hS _ (ih b)).1) a)
  have hqn : ∀ n : ℕ, ∀ x ∈ X, q ^ n * x ∈ X := by
    intro n x hx
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [pow_succ', mul_assoc]; exact hqX _ ih
  have hbd : ∀ n : ℕ, ∀ x ∈ X, ‖q ^ n * x‖ ≤ ‖q‖ ^ n := fun n x hx => by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (hX1 x hx)
  have hsum : ∀ a, Summable fun n => q ^ n * S (v n a) := fun a =>
    Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg q) hq1)
      fun n => hbd n _ (hS _ (hv n a)).1
  let y : Fin r → C := fun a => ∑' n, q ^ n * S (v n a)
  let Y : ℕ → Fin r → C := fun N a => ∑ n ∈ Finset.range N, q ^ n * S (v n a)
  have hY : ∀ a, Filter.Tendsto (fun N => Y N a) Filter.atTop (nhds (y a)) := fun a =>
    (hsum a).hasSum.tendsto_sum_nat
  refine ⟨y, fun a => hX.mem_of_tendsto (hY a) (Filter.Eventually.of_forall fun N =>
    X.sum_mem fun n _ => hqn n _ (hS _ (hv n a)).1), fun a => ?_⟩
  have hN : ∀ N, g (Y N a) - Y N a + p * q * B.mulVec (fun b => g (Y N b)) a
      = p * w a - p * (q ^ N * v N a) := by
    intro N
    induction N with
    | zero => simp [Y, v, Matrix.mulVec, dotProduct]
    | succ N ih =>
      have e : ∀ b, Y (N + 1) b = Y N b + q ^ N * S (v N b) := fun b => Finset.sum_range_succ _ _
      have e2 : (fun b => g (Y (N + 1) b))
          = (fun b => g (Y N b)) + q ^ N • fun b => g (S (v N b)) := by
        funext b; rw [e, map_add, map_mul, map_pow, hgq]; rfl
      rw [e2, e, map_add, map_mul, map_pow, hgq, Matrix.mulVec_add, Matrix.mulVec_smul, hvs]
      simp only [T, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination ih + q ^ N * (hS _ (hv N a)).2
  have t1 : Filter.Tendsto (fun N => g (Y N a) - Y N a + p * q * B.mulVec (fun b => g (Y N b)) a)
      Filter.atTop (nhds (g (y a) - y a + p * q * B.mulVec (fun b => g (y b)) a)) := by
    refine (((hg.tendsto _).comp (hY a)).sub (hY a)).add (Filter.Tendsto.const_mul _ ?_)
    simp only [Matrix.mulVec, dotProduct]
    exact tendsto_finset_sum _ fun b _ => ((hg.tendsto _).comp (hY b)).const_mul _
  have t0 : Filter.Tendsto (fun N => q ^ N * v N a) Filter.atTop (nhds 0) :=
    squeeze_zero_norm (fun N => hbd N _ (hv N a))
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq1)
  have t2 : Filter.Tendsto (fun N => p * w a - p * (q ^ N * v N a)) Filter.atTop
      (nhds (p * w a - p * 0)) := tendsto_const_nhds.sub (t0.const_mul p)
  rw [mul_zero, sub_zero] at t2
  simp only [hN] at t1
  exact tendsto_nhds_unique t1 t2
end GlobalTheory.CycSeries
