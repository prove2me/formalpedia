-- Prove2me | solution 1 for GlobalTheory.CycPerturb.surj_of_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:28:28.650368+00:00
-- url     : https://prove2.me/submissions/78c0b29c-a1bc-4951-aa50-8334b860652a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerGeneratorMatrixPerturbation
import Theorems.Thm_GlobalTheory_CycPerturb_mulVec_mem
import Theorems.Thm_GlobalTheory_Cyc_IsCyc_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycPerturb
variable {C : Type} [NormedField C] [IsUltrametricDist C]
namespace GlobalTheory.CycPerturb
theorem _root_.solution [CompleteSpace C] {r : ℕ} (X : AddSubgroup C) (hX : IsClosed (X : Set C))
    (hX1 : ∀ x ∈ X, ‖x‖ ≤ 1) (g : C ≃+* C) (hg : ∀ x, ‖g x‖ = ‖x‖) (hgX : ∀ x ∈ X, g x ∈ X)
    (p : C) (π : C) (hπ : ‖π‖ < 1) (hgπ : g π = π) (hπX : ∀ x ∈ X, π * x ∈ X)
    (S : C → C) (hS : ∀ x ∈ X, S x ∈ X ∧ g (S x) - S x = p * x)
    (B : Matrix (Fin r) (Fin r) C) (hBX : ∀ a b, ∀ x ∈ X, B a b * x ∈ X)
    (w : Fin r → C) (hw : ∀ a, w a ∈ X) :
    ∃ y : Fin r → C, (∀ a, y a ∈ X) ∧
      ∀ a, g (y a) - y a + p * (π • B).mulVec (fun b => g (y b)) a = p * w a := by
  let T : (Fin r → C) → (Fin r → C) := fun v => B.mulVec (fun b => g (S (v b)))
  let u : ℕ → Fin r → C := fun k => T^[k] w
  have hu0 : u 0 = w := rfl
  have hus : ∀ k, u (k + 1) = B.mulVec (fun b => g (S (u k b))) := fun k =>
    Function.iterate_succ_apply' T k w
  have huX : ∀ k a, u k a ∈ X := by
    intro k
    induction k with
    | zero => exact hw
    | succ k ih => rw [hus]; exact mulVec_mem X B hBX _ (fun b => hgX _ (hS _ (ih b)).1)
  have hpow : ∀ (k : ℕ), ∀ x ∈ X, (-π) ^ k * x ∈ X := by
    intro k x hx
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have : (-π) ^ (k + 1) * x = -(π * ((-π) ^ k * x)) := by ring
      rw [this]; exact X.neg_mem (hπX _ ih)
  have hbd : ∀ (k : ℕ), ∀ x ∈ X, ‖(-π) ^ k * x‖ ≤ ‖π‖ ^ k := by
    intro k x hx
    rw [norm_mul, norm_pow, norm_neg]
    exact mul_le_of_le_one_right (by positivity) (hX1 _ hx)
  have hsum : ∀ a, Summable fun k : ℕ => (-π) ^ k * S (u k a) := fun a =>
    Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg π) hπ)
      fun k => hbd k _ (hS _ (huX k a)).1
  let P : ℕ → Fin r → C := fun n a => ∑ k ∈ Finset.range n, (-π) ^ k * S (u k a)
  let y : Fin r → C := fun a => ∑' k : ℕ, (-π) ^ k * S (u k a)
  have hP : ∀ a, Filter.Tendsto (fun n => P n a) Filter.atTop (nhds (y a)) := fun a =>
    (hsum a).hasSum.tendsto_sum_nat
  have hgc : Continuous g := (AddMonoidHomClass.isometry_of_norm g hg).continuous
  have hL : ∀ n a, g (P n a) - P n a + p * ∑ b, π * B a b * g (P n b)
      = p * w a - p * ((-π) ^ n * u n a) := by
    intro n
    induction n with
    | zero => intro a; simp [P, hu0]
    | succ n ih =>
      intro a
      have e : ∀ b, P (n + 1) b = P n b + (-π) ^ n * S (u n b) := fun b => Finset.sum_range_succ _ _
      have h1 := (hS _ (huX n a)).2
      have h2 : u (n + 1) a = ∑ b, B a b * g (S (u n b)) := by rw [hus]; rfl
      have h3 : ∑ b, π * B a b * g (P (n + 1) b)
          = ∑ b, π * B a b * g (P n b) + π * (-π) ^ n * u (n + 1) a := by
        rw [h2, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [e, map_add, map_mul, map_pow, map_neg, hgπ]; ring
      rw [h3, e, map_add, map_mul, map_pow, map_neg, hgπ]
      linear_combination ih a + (-π) ^ n * h1
  refine ⟨y, fun a => hX.mem_of_tendsto (hP a) (Filter.Eventually.of_forall fun n =>
    X.sum_mem fun k _ => hpow k _ (hS _ (huX k a)).1), fun a => ?_⟩
  have t1 : Filter.Tendsto (fun n => g (P n a) - P n a + p * ∑ b, π * B a b * g (P n b))
      Filter.atTop (nhds (g (y a) - y a + p * ∑ b, π * B a b * g (y b))) :=
    (((hgc.tendsto _).comp (hP a)).sub (hP a)).add
      ((tendsto_finset_sum _ fun b _ => ((hgc.tendsto _).comp (hP b)).const_mul _).const_mul p)
  have t0 : Filter.Tendsto (fun n : ℕ => (-π) ^ n * u n a) Filter.atTop (nhds 0) :=
    squeeze_zero_norm (fun n => hbd n _ (huX n a))
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg π) hπ)
  have t2 : Filter.Tendsto (fun n : ℕ => p * w a - p * ((-π) ^ n * u n a)) Filter.atTop
      (nhds (p * w a - p * 0)) := (t0.const_mul p).const_sub _
  simp only [hL] at t1
  have := tendsto_nhds_unique t1 t2
  rw [mul_zero, sub_zero] at this
  rw [← this]
  rfl
end GlobalTheory.CycPerturb
