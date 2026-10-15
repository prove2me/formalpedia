-- Prove2me | solution 1 for OAI.QAC.parity_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:39:30.337962+00:00
-- url     : https://prove2.me/submissions/e6b86889-f9dd-4f15-91c9-b8fd2f8c6037

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Parity.lean:L43-L76
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.QAC.parity_lower_bound.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_QAC_parity_lower_bound) verbatim and is proved by it.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_DepthZero
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Localization
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Toffoli
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Physical
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Computational
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Ancilla
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ParityTrace
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Measurement
import Theorems.Thm_OAI_QAC_Count_backward_finite
import Theorems.Thm_OAI_QAC_Count_low_propagation_bound
import Theorems.Thm_OAI_QAC_Count_pattern_mul
import Theorems.Thm_OAI_QAC_Count_polynomial_transition
import Theorems.Thm_OAI_QAC_IsCircuit_star_mem
import Theorems.Thm_OAI_QAC_eventually_backward_cost
import Theorems.Thm_OAI_QAC_eventually_power_log_le
import Theorems.Thm_OAI_QAC_finite_scale_induction
import Theorems.Thm_OAI_QAC_high_entry_bound
import Theorems.Thm_OAI_QAC_parity_advantage_from_entries
import Theorems.Thm_OAI_QAC_polynomial_approximation
import Theorems.Thm_OAI_QAC_rankOne_projection
import Theorems.Thm_OAI_QAC_small_support_layer_bound
import Theorems.Thm_OAI_QAC_toffoli_reflection

-- ---- from OAI.InformationTheory.QuantumCircuit.ProductProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma tensorMatrix_mul {N : ℕ} (a b : Fin N → QubitOperator) :
    tensorMatrix a * tensorMatrix b = tensorMatrix (fun i => a i * b i) := by
  classical
  ext x y
  simp only [Matrix.mul_apply, tensorMatrix]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i z => a i (x i) z * b i z (y i))).symm

lemma tensorMatrix_zero_of_zero {N : ℕ} (a : Fin N → QubitOperator)
    (i : Fin N) (hi : a i = 0) : tensorMatrix a = 0 := by
  classical
  ext x y
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi]

lemma tensorMatrix_projection {N : ℕ} (a : Fin N → QubitOperator)
    (ha : ∀ i, IsStarProjection (a i)) : IsStarProjection (tensorMatrix a) := by
  rw [isStarProjection_iff']
  constructor
  · rw [tensorMatrix_mul]
    congr 1
    funext i
    exact (ha i).isIdempotentElem.eq
  · rw [tensorMatrix_star]
    congr 1
    funext i
    exact (ha i).isSelfAdjoint.star_eq

lemma tensorMatrix_unitary {N : ℕ} (a : Fin N → QubitOperator)
    (ha : ∀ i, a i ∈ unitary QubitOperator) : tensorMatrix a ∈ unitary (Operator N) := by
  rw [Unitary.mem_iff]
  simp only [tensorMatrix_star, tensorMatrix_mul]
  constructor <;> convert tensorMatrix_one (N := N) using 1 <;>
    congr 1 <;> funext i
  · exact (Unitary.mem_iff.mp (ha i)).1
  · exact (Unitary.mem_iff.mp (ha i)).2

lemma Count.zero_projection {N : ℕ} (M : Count N) : IsStarProjection M.zero := by
  apply tensorMatrix_projection
  intro i
  split_ifs with hi
  · exact rankOne_projection (M.normalized i hi)
  · exact IsStarProjection.one _

lemma Count.pattern_projection {N : ℕ} (M : Count N) (F : Finset (Fin N)) :
    IsStarProjection (M.pattern F) := by
  apply tensorMatrix_projection
  intro i
  split_ifs with hi hF
  · exact (rankOne_projection (M.normalized i hi)).one_sub
  · exact rankOne_projection (M.normalized i hi)
  · exact IsStarProjection.one _

lemma projection_sum {A ι : Type*} [Ring A] [StarRing A] (s : Finset ι) (p : ι → A)
    (hp : ∀ i ∈ s, IsStarProjection (p i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → p i * p j = 0) :
    IsStarProjection (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    apply (hp i (Finset.mem_insert_self _ _)).add
    · apply ih
      · exact fun j hj => hp j (Finset.mem_insert_of_mem hj)
      · exact fun j hj k hk h => horth j (Finset.mem_insert_of_mem hj)
          k (Finset.mem_insert_of_mem hk) h
    · rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      apply horth i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
      intro h
      exact hi (h ▸ hj)

lemma Count.high_eq_sum_filter {N : ℕ} (M : Count N) (r : ℝ) :
    M.high r = ∑ F ∈ M.support.powerset.filter (fun F => r ≤ (F.card : ℝ)), M.pattern F := by
  classical
  simp only [Count.high, Finset.sum_filter]

lemma Count.high_projection {N : ℕ} (M : Count N) (r : ℝ) : IsStarProjection (M.high r) := by
  classical
  rw [M.high_eq_sum_filter]
  apply projection_sum
  · exact fun F _ => M.pattern_projection F
  · intro F hF G hG hFG
    rw [M.pattern_mul (Finset.mem_powerset.mp (Finset.mem_filter.mp hF).1)
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hG).1), ite_eq_right hFG]

lemma Count.high_eq_zero {N : ℕ} (M : Count N) {r : ℝ} (hr : (N : ℝ) < r) : M.high r = 0 := by
  classical
  unfold Count.high
  apply Finset.sum_eq_zero
  intro F hF
  rw [ite_eq_right]
  have hFN : F.card ≤ N := by simpa using Finset.card_le_univ F
  have hFR : (F.card : ℝ) ≤ N := by exact_mod_cast hFN
  linarith

section SpectralAlgebra

variable {A ι : Type*} [CStarAlgebra A]

lemma orthogonal_sum_mul (s : Finset ι) (p : ι → A)
    (hp : ∀ i ∈ s, IsStarProjection (p i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → p i * p j = 0) (c d : ι → ℝ) :
    (∑ i ∈ s, c i • p i) * (∑ i ∈ s, d i • p i) = ∑ i ∈ s, (c i * d i) • p i := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · rw [smul_mul_smul_comm, (hp i hi).isIdempotentElem.eq]
  · intro j hj hji
    rw [smul_mul_smul_comm, horth i hi j hj (Ne.symm hji), smul_zero]
  · intro h
    exact (h hi).elim

lemma orthogonal_sum_star (s : Finset ι) (p : ι → A)
    (hp : ∀ i ∈ s, IsStarProjection (p i)) (c : ι → ℝ) :
    star (∑ i ∈ s, c i • p i) = ∑ i ∈ s, c i • p i := by
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [star_smul, star_trivial, (hp i hi).isSelfAdjoint.star_eq]

variable [PartialOrder A] [StarOrderedRing A]

lemma orthogonal_sum_norm_le (s : Finset ι) (p : ι → A)
    (hp : ∀ i ∈ s, IsStarProjection (p i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → p i * p j = 0)
    (hsum : ∑ i ∈ s, p i = 1) (c : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ i ∈ s, |c i| ≤ C) : ‖∑ i ∈ s, c i • p i‖ ≤ C := by
  have hsq : star (∑ i ∈ s, c i • p i) * (∑ i ∈ s, c i • p i) =
      ∑ i ∈ s, (c i)^2 • p i := by
    rw [orthogonal_sum_star s p hp c, orthogonal_sum_mul s p hp horth]
    simp only [pow_two]
  have hle : (∑ i ∈ s, (c i)^2 • p i) ≤ algebraMap ℝ A (C^2) := by
    calc
      _ ≤ ∑ i ∈ s, C^2 • p i := by
        apply Finset.sum_le_sum
        intro i hi
        apply smul_le_smul_of_nonneg_right _ (hp i hi).nonneg
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).2 (hc i hi)
      _ = _ := by rw [← Finset.smul_sum, hsum, Algebra.algebraMap_eq_smul_one]
  have hnorm := (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg C)
    (star_mul_self_nonneg (∑ i ∈ s, c i • p i))).2 (hsq ▸ hle)
  rw [CStarRing.norm_star_mul_self] at hnorm
  nlinarith only [hnorm, norm_nonneg (∑ i ∈ s, c i • p i), hC]

end SpectralAlgebra

open scoped MatrixOrder in
lemma Count.spectral_norm_le {N : ℕ} (M : Count N) (f : ℕ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ k ≤ N, |f k| ≤ C) :
    ‖∑ F ∈ M.support.powerset, f F.card • M.pattern F‖ ≤ C := by
  refine orthogonal_sum_norm_le M.support.powerset M.pattern
    (fun F _ => M.pattern_projection F) ?_ M.sum_pattern _ hC ?_
  · intro F hF G hG hFG
    rw [M.pattern_mul (Finset.mem_powerset.mp hF) (Finset.mem_powerset.mp hG), ite_eq_right hFG]
  · intro F _
    apply hf
    simpa using Finset.card_le_univ F

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Circuit ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma rankOne_mulVec (U : QubitOperator) (v : Bit → ℂ) :
    rankOne (U *ᵥ v) = U * rankOne v * star U := by
  change Matrix.vecMulVec (U *ᵥ v) (star (U *ᵥ v)) =
    U * Matrix.vecMulVec v (star v) * star U
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]
  rfl

lemma Count.rotate_zero {N : ℕ} (M : Count N) (L : LocalLayer N) :
    (M.rotate L).zero = localMatrix L * M.zero * star (localMatrix L) := by
  classical
  dsimp only [Count.zero, Count.rotate, localMatrix]
  rw [tensorMatrix_star, tensorMatrix_mul, tensorMatrix_mul]
  congr 1
  funext i
  by_cases hi : i ∈ M.support
  · simp only [ite_eq_left hi]
    exact rankOne_mulVec _ _
  · simp only [ite_eq_right hi, mul_one, Unitary.mul_star_self_of_mem (L i).property]

lemma localMatrix_unitary {N : ℕ} (L : LocalLayer N) : localMatrix L ∈ unitary (Operator N) :=
  tensorMatrix_unitary _ (fun i => (L i).property)

lemma localMatrix_mul {N : ℕ} (L K : LocalLayer N) :
    localMatrix L * localMatrix K = localMatrix (fun i => L i * K i) := by
  exact tensorMatrix_mul _ _

lemma localMatrix_star {N : ℕ} (L : LocalLayer N) :
    star (localMatrix L) = localMatrix (fun i => star (L i)) := by
  exact tensorMatrix_star _

lemma reflection_unitary {N : ℕ} (M : Count N) :
    (1 : Operator N) - (2 : ℂ) • M.zero ∈ unitary (Operator N) := by
  have h := M.zero_projection.two_mul_sub_one_mem_unitary
  have hneg : -(2 * M.zero - 1) ∈ unitary (Operator N) := by
    simpa only [Unitary.mem_iff, star_neg, neg_mul_neg] using h
  simpa only [two_smul, two_mul, neg_sub] using hneg

lemma reflectionMatrix_unitary {N : ℕ} (R : ReflectionLayer N) :
    reflectionMatrix R ∈ unitary (Operator N) := by
  apply (unitary (Operator N)).list_prod_mem
  intro U hU
  obtain ⟨M, _, rfl⟩ := List.mem_map.mp hU
  exact reflection_unitary M

lemma IsCircuit.mem_unitary {N d : ℕ} {U : Operator N} (hU : IsCircuit d U) :
    U ∈ unitary (Operator N) := by
  induction d generalizing U with
  | zero => obtain ⟨L, rfl⟩ := hU; exact localMatrix_unitary L
  | succ d ih =>
    obtain ⟨V, R, L, hV, rfl⟩ := hU
    exact (unitary (Operator N)).mul_mem
      ((unitary (Operator N)).mul_mem (ih hV) (reflectionMatrix_unitary R)) (localMatrix_unitary L)

lemma IsCircuit.mul_local {N d : ℕ} {U : Operator N} (hU : IsCircuit d U)
    (L : LocalLayer N) : IsCircuit d (U * localMatrix L) := by
  cases d with
  | zero =>
    obtain ⟨K, rfl⟩ := hU
    exact ⟨fun i => K i * L i, localMatrix_mul K L⟩
  | succ d =>
    obtain ⟨V, R, K, hV, rfl⟩ := hU
    exact ⟨V, R, (fun i => K i * L i), hV, by rw [mul_assoc, localMatrix_mul]⟩

lemma IsCircuit.mul {N d e : ℕ} {U V : Operator N}
    (hU : IsCircuit d U) (hV : IsCircuit e V) : IsCircuit (d + e) (U * V) := by
  induction e generalizing V with
  | zero =>
    obtain ⟨L, rfl⟩ := hV
    exact hU.mul_local L
  | succ e ih =>
    obtain ⟨W, R, L, hW, rfl⟩ := hV
    exact ⟨U * W, R, L, ih hW, by simp only [mul_assoc]⟩

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Count ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma tensorMatrix_smul {N : ℕ} (c : Fin N → ℝ) (a : Fin N → QubitOperator) :
    tensorMatrix (fun i => c i • a i) = (∏ i, c i) • tensorMatrix a := by
  ext x y
  simp only [tensorMatrix, Matrix.smul_apply, Complex.real_smul, Finset.prod_mul_distrib,
    Complex.ofReal_prod]

open scoped MatrixOrder in
lemma tensorMatrix_nonneg {N : ℕ} (a : Fin N → QubitOperator) (ha : ∀ i, 0 ≤ a i) :
    0 ≤ tensorMatrix a := by
  choose b hb using fun i => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (ha i)
  have h : tensorMatrix a = star (tensorMatrix b) * tensorMatrix b := by
    rw [tensorMatrix_star, tensorMatrix_mul]
    congr 1
    funext i
    exact hb i
  rw [h]
  exact star_mul_self_nonneg _

open scoped MatrixOrder in
lemma tensorMatrix_le_one {N : ℕ} (a : Fin N → QubitOperator)
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) : tensorMatrix a ≤ 1 := by
  classical
  have hsum := tensorMatrix_sum_patterns (Finset.univ : Finset (Fin N))
    (fun i => 1 - a i) a (fun _ => 1)
  simp only [Finset.mem_univ, ite_true, sub_add_cancel, tensorMatrix_one] at hsum
  rw [← hsum]
  have hmem : (∅ : Finset (Fin N)) ∈ Finset.univ.powerset := Finset.mem_powerset.mpr (Finset.empty_subset _)
  have h := Finset.single_le_sum (fun F (_ : F ∈ (Finset.univ : Finset (Fin N)).powerset) =>
    tensorMatrix_nonneg (fun i => if i ∈ F then 1 - a i else a i)
      (fun i => by split_ifs; exact sub_nonneg.mpr (ha1 i); exact ha i)) hmem
  simpa only [Finset.notMem_empty, ite_false] using h

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Spectral ----
-- Lean 4.34 name of List.sum_le_card_nsmul (same statement) in Mathlib 0df444a.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma Count.low_eq_sum {N : ℕ} (M : Count N) (r : ℝ) :
    M.low r = ∑ F ∈ M.support.powerset.filter (fun F => (F.card : ℝ) < r), M.pattern F := by
  classical
  rw [Count.low, ← M.sum_pattern]
  unfold Count.high
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro F _
  by_cases h : r ≤ (F.card : ℝ)
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

lemma Count.generator_mul_pattern {N : ℕ} (M : Count N) (i : Fin N) (hi : i ∈ M.support)
    (F : Finset (Fin N)) :
    tensorMatrix (fun j => if j = i then 1-rankOne (M.vector i) else 1) * M.pattern F =
      if i ∈ F then M.pattern F else 0 := by
  classical
  rw [Count.pattern, tensorMatrix_mul]
  by_cases hiF : i ∈ F
  · rw [ite_eq_left hiF]
    congr 1
    funext j
    by_cases hji : j = i
    · subst j
      simp only [ite_eq_left hi, ite_eq_left hiF]
      exact (rankOne_projection (M.normalized i hi)).one_sub.isIdempotentElem.eq
    · simp only [ite_eq_right hji, one_mul]
  · rw [ite_eq_right hiF]
    apply tensorMatrix_zero_of_zero _ i
    simp only [ite_eq_left hi, ite_eq_right hiF]
    exact (rankOne_projection (M.normalized i hi)).one_sub_mul_self

lemma Count.operator_mul_pattern {N : ℕ} (M : Count N) (F : Finset (Fin N)) (hF : F ⊆ M.support) :
    M.operator * M.pattern F = (F.card : ℝ) • M.pattern F := by
  classical
  rw [Count.operator, Finset.sum_mul]
  calc
    _ = ∑ i ∈ M.support, if i ∈ F then M.pattern F else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact M.generator_mul_pattern i hi F
    _ = _ := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hF, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]

lemma Count.operator_spectral {N : ℕ} (M : Count N) :
    M.operator = M.spectral (fun k => k) := by
  classical
  calc
    _ = M.operator * (∑ F ∈ M.support.powerset, M.pattern F) := by rw [M.sum_pattern,mul_one]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F hF
      exact M.operator_mul_pattern F (Finset.mem_powerset.mp hF)

lemma Count.spectral_mul {N : ℕ} (M : Count N) (f g : ℕ → ℝ) :
    M.spectral f * M.spectral g = M.spectral (fun k => f k * g k) := by
  classical
  exact orthogonal_sum_mul _ _ (fun F _ => M.pattern_projection F)
    (fun F hF G hG hFG => by
      rw [M.pattern_mul (Finset.mem_powerset.mp hF) (Finset.mem_powerset.mp hG),ite_eq_right hFG]) _ _

lemma Count.operator_pow_spectral {N : ℕ} (M : Count N) (k : ℕ) :
    M.operator^k = M.spectral (fun j => (j:ℝ)^k) := by
  induction k with
  | zero => simp [Count.spectral]
  | succ k ih => rw [pow_succ,ih,M.operator_spectral,M.spectral_mul]; simp only [pow_succ]

lemma Count.operator_norm_le {N : ℕ} (M : Count N) : ‖M.operator‖ ≤ N := by
  rw [M.operator_spectral]
  exact M.spectral_norm_le _ (by positivity) (fun k hk => by simpa using (show (k:ℝ) ≤ N by exact_mod_cast hk))

lemma Count.polynomial_eq_sum {N : ℕ} (M : Count N) (p : Polynomial ℝ) :
    M.polynomial p = ∑ k ∈ p.support, p.coeff k • M.operator^k := by
  classical
  unfold Count.polynomial Count.spectral
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.smul_sum]
  change p.coeff k • M.spectral (fun j => (j:ℝ)^k) = _
  rw [← M.operator_pow_spectral]

lemma Count.zero_spectral {N : ℕ} (M : Count N) :
    M.zero = M.spectral (fun k => if k = 0 then 1 else 0) := by
  classical
  unfold Count.spectral
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro F _ hF
    simp only [Finset.card_eq_zero, ite_eq_right hF, zero_smul]
  · simp

lemma Count.low_spectral {N : ℕ} (M : Count N) (r : ℝ) :
    M.low r = M.spectral (fun k => if (k:ℝ) < r then 1 else 0) := by
  classical
  rw [M.low_eq_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro F _
  split_ifs with h <;> simp only [h, ite_true, ite_false, one_smul, zero_smul]

lemma Count.spectral_sub {N : ℕ} (M : Count N) (f g : ℕ → ℝ) :
    M.spectral f - M.spectral g = M.spectral (fun k => f k - g k) := by
  simp only [Count.spectral, sub_smul, Finset.sum_sub_distrib]

lemma Count.polynomial_error_low {N : ℕ} (M : Count N) (p : Polynomial ℝ)
    {r δ : ℝ} (hδ : 0 ≤ δ) (hp0 : p.eval 0 = 1)
    (hp : ∀ k : ℕ, 1 ≤ k → (k:ℝ) < r → |p.eval (k:ℝ)| ≤ δ) :
    ‖(M.zero - M.polynomial p) * M.low r‖ ≤ δ := by
  rw [M.zero_spectral, Count.polynomial, M.spectral_sub, M.low_spectral, M.spectral_mul]
  apply M.spectral_norm_le (fun k => ((if k = 0 then 1 else 0) - p.eval (k:ℝ)) *
    (if (k:ℝ) < r then 1 else 0)) hδ
  intro k _
  by_cases hk : k = 0
  · subst k; simpa [hp0] using hδ
  · by_cases hkr : (k:ℝ) < r
    · simpa [hk,hkr] using hp k (by omega) hkr
    · simpa [hkr] using hδ

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Transition ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

section NormAlgebra
variable {A : Type*} [CStarAlgebra A]

end NormAlgebra

section ThreeFactors
variable {A : Type*} [CStarAlgebra A]

end ThreeFactors

section Conjugation
variable {A : Type*} [CStarAlgebra A]

lemma conjugate_mul {U : A} (hU : U ∈ unitary A) (B C : A) :
    conjugate U (B*C) = conjugate U B * conjugate U C := by
  simp only [conjugate,mul_assoc,← mul_assoc (star U) U,Unitary.star_mul_self_of_mem hU,one_mul]

lemma conjugate_sub (U B C : A) : conjugate U (B-C) = conjugate U B - conjugate U C := by
  simp only [conjugate,mul_sub,sub_mul]

lemma conjugate_one {U : A} (hU : U ∈ unitary A) : conjugate U 1 = 1 := by
  simp only [conjugate,mul_one,Unitary.mul_star_self_of_mem hU]

lemma conjugate_smul (U B : A) (r : ℝ) : conjugate U (r • B) = r • conjugate U B := by
  simp only [conjugate,mul_smul_comm,smul_mul_assoc]

end Conjugation

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Reflection ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma reflectionMatrix_eq {N : ℕ} (R : ReflectionLayer N) : reflectionMatrix R = reflectList R.gates := by
  unfold reflectionMatrix reflectList
  congr 1

section BilinearBudget
variable {A : Type*} [CStarAlgebra A]

end BilinearBudget

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Backward ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma Count.polynomial_norm_le {N : ℕ} (D : Count N) (p : Polynomial ℝ) :
    ‖D.polynomial p‖ ≤ weight N p := by
  classical
  rw [D.polynomial_eq_sum]
  apply (norm_sum_le _ _).trans
  change (∑ k ∈ p.support, ‖p.coeff k • D.operator^k‖) ≤ ∑ k ∈ p.support, |p.coeff k| *(N:ℝ)^k
  apply Finset.sum_le_sum
  intro k _
  rw [norm_smul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) D.operator_norm_le _)

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Asymptotics ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Filter Asymptotics

namespace QAC

/-- Strict exponent gaps absorb every fixed multiplicative constant. -/
lemma eventually_power_le {s t : ℝ} (hst : s < t) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ s ≤ (N : ℝ) ^ t := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (t - s)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.2 hst)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop C, eventually_ge_atTop 1] with N hN h1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    C * (N : ℝ) ^ s ≤ (N : ℝ) ^ (t - s) * (N : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ t := by rw [← Real.rpow_add hN0]; congr 1; ring

lemma ceil_rpow_bounds {N : ℕ} {a : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a) :
    (N : ℝ) ^ a ≤ (⌈(N : ℝ) ^ a⌉₊ : ℝ) ∧
    (⌈(N : ℝ) ^ a⌉₊ : ℝ) ≤ 2 * (N : ℝ) ^ a := by
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp1 : 1 ≤ (N : ℝ) ^ a := Real.one_le_rpow h1 ha
  constructor
  · exact Nat.le_ceil _
  · have h := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg N) a)
    linarith

lemma eventually_two_powers_le {a b t : ℝ} (ha : a < t) (hb : b < t) :
    ∀ᶠ N : ℕ in atTop, (N:ℝ)^a + (N:ℝ)^b ≤ (N:ℝ)^t := by
  filter_upwards [eventually_power_le ha 2,eventually_power_le hb 2] with N haN hbN
  linarith

/-- Every fixed coefficient and prefactor is absorbed by the strict power gaps. -/
lemma eventually_exp_power_gap {s u v : ℝ} (hs : s < v) (hu : u < v) (hv : 0 < v)
    (C ε D K : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, C * Real.exp (K*(N:ℝ)^u - (N:ℝ)^v) ≤
      ε * Real.exp (-(D*(N:ℝ)^s)) := by
  filter_upwards [eventually_power_le hv (3*Real.log (C/ε)),
    eventually_power_le hu (3*K),eventually_power_le hs (3*D)] with N h0 h1 h2
  simp only [Real.rpow_zero,mul_one] at h0
  calc
    _ = ε * Real.exp (Real.log (C/ε) + K*(N:ℝ)^u - (N:ℝ)^v) := by
      rw [show Real.log (C/ε) + K*(N:ℝ)^u - (N:ℝ)^v =
        Real.log (C/ε) + (K*(N:ℝ)^u - (N:ℝ)^v) by ring, Real.exp_add,
        Real.exp_log (div_pos hC hε)]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [h0,h1,h2])) hε.le

lemma ceil_power_log_bound {N : ℕ} {a : ℝ} (hN : 2 ≤ N) (ha : 0 ≤ a) :
    ((⌈(N:ℝ)^a⌉₊:ℝ)+1)*Real.log (N+1) ≤ 6*(N:ℝ)^a*Real.log N := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hp : 1 ≤ (N:ℝ)^a := Real.one_le_rpow hN1 ha
  have hc := (ceil_rpow_bounds (show 1 ≤ N by omega) ha).2
  have hl : Real.log (N+1) ≤ 2*Real.log N := by
    calc
      _ ≤ Real.log ((N:ℝ)^2) := Real.log_le_log (by positivity) (by nlinarith only [hN2])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hlog : 0 ≤ Real.log (N+1) := Real.log_nonneg (by linarith only [hN1])
  calc
    _ ≤ (3*(N:ℝ)^a)*Real.log (N+1) := mul_le_mul_of_nonneg_right (by linarith) hlog
    _ ≤ (3*(N:ℝ)^a)*(2*Real.log N) := mul_le_mul_of_nonneg_left hl (by positivity)
    _ = _ := by ring

lemma eventually_pattern_cost {a s v : ℝ} (ha : 0 ≤ a) (hav : a < v) (hsv : s < v) :
    ∀ᶠ N : ℕ in atTop,
      (N+1:ℝ)^(⌈(N:ℝ)^a⌉₊+1) * Real.exp (-((N:ℝ)^v)) ≤ Real.exp (-((N:ℝ)^s)) := by
  filter_upwards [eventually_power_log_le hav 12,eventually_power_le hsv 2,
    eventually_ge_atTop 2] with N hcost htarget hN
  have hc := ceil_power_log_bound hN ha
  have hp : (N+1:ℝ)^(⌈(N:ℝ)^a⌉₊+1) =
      Real.exp (((⌈(N:ℝ)^a⌉₊:ℝ)+1)*Real.log (N+1)) := by
    rw [show (⌈(N:ℝ)^a⌉₊:ℝ)+1 = ((⌈(N:ℝ)^a⌉₊+1:ℕ):ℝ) by push_cast; rfl,
      Real.exp_nat_mul,Real.exp_log (by positivity)]
  rw [hp,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith only [hc,hcost,htarget]

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.DepthZero ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma rankOne_sandwich (v w : Bit → ℂ) :
    rankOne v * rankOne w * rankOne v =
      Complex.normSq (star w ⬝ᵥ v) • rankOne v := by
  ext i j
  simp only [rankOne, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
    Complex.real_smul, ← Complex.mul_conj, dotProduct, Pi.star_apply,
    Fin.sum_univ_two, map_add, map_mul, Complex.conj_conj, Complex.star_def]
  ring

open scoped MatrixOrder in
lemma rankOne_markov_le (v w : Bit → ℂ)
    (hv : ∑ b, Complex.normSq (v b) = 1)
    (hw : ∑ b, Complex.normSq (w b) = 1) :
    rankOne v * rankOne w * ((2:ℝ) • (1 - rankOne v) + rankOne v) * rankOne w * rankOne v ≤ 1 := by
  let P := rankOne v
  let Q := rankOne w
  let c : ℝ := Complex.normSq (star w ⬝ᵥ v)
  have hP := rankOne_projection hv
  have hQ := rankOne_projection hw
  have hPQ : P * Q * P = c • P := rankOne_sandwich v w
  have hid : P * Q * ((2:ℝ) • (1 - P) + P) * Q * P = (2*c-c^2) • P := by
    have h1 : P * Q * Q * P = c • P := by rw [mul_assoc P Q Q, hQ.isIdempotentElem.eq, hPQ]
    have h2 : P * Q * P * Q * P = c^2 • P := by
      rw [hPQ, smul_mul_assoc, smul_mul_assoc, hPQ, smul_smul, pow_two]
    calc
      _ = (2:ℝ) • (P * Q * Q * P) - P * Q * P * Q * P := by
        simp only [two_smul, mul_add, add_mul, mul_sub, sub_mul, mul_one]
        abel
      _ = _ := by rw [h1, h2, smul_smul, ← sub_smul]
  change P * Q * ((2:ℝ) • (1 - P) + P) * Q * P ≤ 1
  rw [hid]
  apply sub_nonneg.mp
  have heq : 1 - (2*c-c^2) • P = (1-P) + (1-c)^2 • P := by
    have hc : (1-c)^2 = 1-(2*c-c^2) := by ring
    simp only [hc, sub_smul, one_smul]
    abel
  rw [heq]
  exact add_nonneg hP.one_sub.nonneg (smul_nonneg (sq_nonneg _) hP.nonneg)

lemma tensorMatrix_pattern_scale {N : ℕ} (M : Count N) (F : Finset (Fin N))
    (hF : F ⊆ M.support) (z : ℝ) :
    tensorMatrix (fun i => if i ∈ M.support then
      (if i ∈ F then z • (1 - rankOne (M.vector i)) else rankOne (M.vector i)) else 1) =
      z ^ F.card • M.pattern F := by
  classical
  have heq : (fun i => if i ∈ M.support then
      (if i ∈ F then z • (1 - rankOne (M.vector i)) else rankOne (M.vector i)) else 1) =
      (fun i => (if i ∈ F then z else 1) •
        (if i ∈ M.support then (if i ∈ F then 1 - rankOne (M.vector i) else rankOne (M.vector i)) else 1)) := by
    funext i
    by_cases hiF : i ∈ F
    · simp [hiF, hF hiF]
    · simp [hiF]
  rw [heq, tensorMatrix_smul]
  congr 1
  simp

/-- The generating function of the mismatch spectral partition. -/
lemma Count.spectral_power_tensor {N : ℕ} (M : Count N) (z : ℝ) :
    (∑ F ∈ M.support.powerset, z ^ F.card • M.pattern F) =
      tensorMatrix (fun i => if i ∈ M.support then
        z • (1 - rankOne (M.vector i)) + rankOne (M.vector i) else 1) := by
  classical
  rw [← tensorMatrix_sum_patterns M.support]
  apply Finset.sum_congr rfl
  intro F hF
  exact (tensorMatrix_pattern_scale M F (Finset.mem_powerset.mp hF) z).symm

open scoped MatrixOrder in
lemma Count.high_le_generating {N : ℕ} (M : Count N) (r : ℝ) :
    M.high r ≤ (2 : ℝ) ^ (-r) •
      (∑ F ∈ M.support.powerset, (2 : ℝ)^F.card • M.pattern F) := by
  classical
  rw [Finset.smul_sum]
  unfold Count.high
  apply Finset.sum_le_sum
  intro F _
  rw [smul_smul]
  by_cases hr : r ≤ F.card
  · rw [ite_eq_left hr]
    nth_rw 1 [← one_smul ℝ (M.pattern F)]
    apply smul_le_smul_of_nonneg_right _ (M.pattern_projection F).nonneg
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    exact Real.one_le_rpow (by norm_num) (by linarith)
  · rw [ite_eq_right hr]
    exact smul_nonneg (by positivity) (M.pattern_projection F).nonneg

lemma Count.site_projection {N : ℕ} (M : Count N) (i : Fin N) : IsStarProjection (M.site i) := by
  classical
  dsimp [Count.site]
  split_ifs with hi
  · exact rankOne_projection (M.normalized i hi)
  · exact IsStarProjection.one _

open scoped MatrixOrder in
lemma projection_markov_nonneg {A : Type*} [Ring A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [Algebra ℝ A] [IsOrderedModule ℝ A]
    (P Q : A) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    0 ≤ P * Q * ((2:ℝ) • (1-P)+P) * Q * P := by
  have hn : 0 ≤ (2:ℝ) • (1-P)+P :=
    add_nonneg (smul_nonneg (by norm_num) hP.one_sub.nonneg) hP.nonneg
  simpa only [star_mul, hQ.isSelfAdjoint.star_eq, hP.isSelfAdjoint.star_eq, mul_assoc] using
    star_right_conjugate_nonneg hn (P*Q)

lemma projection_markov_self {A : Type*} [Ring A] [Module ℝ A] [SMulCommClass ℝ A A]
    {P : A} (hP : IsIdempotentElem P) : P * ((2:ℝ) • (1-P)+P) * P = P := by
  have hc : P * (1-P) = 0 := by rw [mul_sub,mul_one,hP.eq,sub_self]
  simp only [mul_add, mul_smul_comm, hc, smul_zero, zero_add, hP.eq]

open scoped MatrixOrder in
lemma Count.markov_site_le {N : ℕ} (M D : Count N) (i : Fin N) :
    M.site i * D.site i * ((2:ℝ) • (1-M.site i)+M.site i) * D.site i * M.site i ≤ 1 := by
  classical
  by_cases hM : i ∈ M.support
  · by_cases hD : i ∈ D.support
    · simp only [Count.site, ite_eq_left hM, ite_eq_left hD]
      exact rankOne_markov_le _ _ (M.normalized i hM) (D.normalized i hD)
    · simp only [Count.site, ite_eq_left hM, ite_eq_right hD, mul_one]
      rw [projection_markov_self (rankOne_projection (M.normalized i hM)).isIdempotentElem]
      exact (rankOne_projection (M.normalized i hM)).le_one
  · have heq : M.site i = 1 := ite_eq_right hM
    rw [heq]
    simp only [sub_self, smul_zero, zero_add, one_mul, mul_one,
      (D.site_projection i).isIdempotentElem.eq]
    exact (D.site_projection i).le_one

lemma Count.generating_eq_sites {N : ℕ} (M : Count N) :
    (∑ F ∈ M.support.powerset, (2 : ℝ)^F.card • M.pattern F) =
      tensorMatrix (fun i => (2:ℝ) • (1-M.site i)+M.site i) := by
  classical
  rw [M.spectral_power_tensor]
  congr 1
  funext i
  by_cases hi : i ∈ M.support <;> simp [Count.site,hi]

open scoped MatrixOrder in
lemma Count.markov_sandwich_le {N : ℕ} (M D : Count N) :
    M.zero * D.zero * (∑ F ∈ M.support.powerset, (2 : ℝ)^F.card • M.pattern F) *
      D.zero * M.zero ≤ 1 := by
  rw [M.generating_eq_sites]
  change tensorMatrix M.site * tensorMatrix D.site *
    tensorMatrix (fun i => (2:ℝ) • (1-M.site i)+M.site i) *
    tensorMatrix D.site * tensorMatrix M.site ≤ 1
  simp only [tensorMatrix_mul]
  exact tensorMatrix_le_one _
    (fun i => projection_markov_nonneg _ _ (M.site_projection i) (D.site_projection i))
    (fun i => M.markov_site_le D i)

open scoped MatrixOrder in
lemma Count.depth_zero_square {N : ℕ} (M D : Count N) (r : ℝ) :
    ‖M.high r * D.zero * M.zero‖^2 ≤ (2 : ℝ)^(-r) := by
  let A := M.high r * D.zero * M.zero
  have heq : star A * A = M.zero * D.zero * M.high r * D.zero * M.zero := by
    dsimp [A]
    simp only [star_mul, M.zero_projection.isSelfAdjoint.star_eq,
      D.zero_projection.isSelfAdjoint.star_eq, (M.high_projection r).isSelfAdjoint.star_eq]
    simp only [mul_assoc]
    rw [← mul_assoc (M.high r) (M.high r), (M.high_projection r).isIdempotentElem.eq]
  have h := star_right_conjugate_le_conjugate (M.high_le_generating r) (M.zero * D.zero)
  simp only [star_mul, M.zero_projection.isSelfAdjoint.star_eq,
    D.zero_projection.isSelfAdjoint.star_eq, mul_smul_comm, smul_mul_assoc] at h
  have hbound : star A * A ≤ (2 : ℝ)^(-r) • (1 : Operator N) := by
    rw [heq]
    exact le_trans (by simpa only [mul_assoc] using h)
      (smul_le_smul_of_nonneg_left (M.markov_sandwich_le D) (by positivity))
  have hn := (CStarAlgebra.norm_le_iff_le_algebraMap (star A * A) (by positivity : 0 ≤ (2:ℝ)^(-r)) (star_mul_self_nonneg A)).2
    (by simpa only [Algebra.algebraMap_eq_smul_one] using hbound)
  simpa only [CStarRing.norm_star_mul_self, pow_two] using hn

lemma Count.depth_zero_bound {N : ℕ} (M D : Count N) (r : ℝ) :
    ‖M.high r * D.zero * M.zero‖ ≤ Real.exp (-(Real.log 2 / 2) * r) := by
  have hsq := M.depth_zero_square D r
  have heq : Real.exp (-(Real.log 2 / 2) * r)^2 = (2:ℝ)^(-r) := by
    rw [pow_two, ← Real.exp_add, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  rw [← heq] at hsq
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp hsq

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Localization ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

lemma uniform_zero {s t : ℝ} (hst : s < t) : UniformLocalization 0 s t := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_power_le hst (2/Real.log 2)] with N hN
  intro U hU M D
  obtain ⟨L,rfl⟩ := hU
  have hb := M.depth_zero_bound (D.rotate L) ((N:ℝ)^t)
  rw [D.rotate_zero L] at hb
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have h := (div_le_iff₀ hlog).mp (show 2*(N:ℝ)^s/Real.log 2 ≤ (N:ℝ)^t by
    simpa only [div_mul_eq_mul_div] using hN)
  nlinarith only [h]

lemma uniform_large (d : ℕ) {s t : ℝ} (ht : 1 < t) : UniformLocalization d s t := by
  filter_upwards [eventually_power_le ht 2,Filter.eventually_ge_atTop 1] with N hN hN1
  intro U _ M D
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlimit : (N:ℝ) < (N:ℝ)^t := by rw [Real.rpow_one] at hN; linarith only [hN,hNpos]
  rw [M.high_eq_zero hlimit,zero_mul,zero_mul,norm_zero]
  exact (Real.exp_pos _).le

lemma uniform_low_propagation {d : ℕ}
    (ih : ∀ s t : ℝ, 0 ≤ s → s < t → UniformLocalization d s t)
    {a s t : ℝ} (ha : 0 ≤ a) (_hs : 0 ≤ s) (hat : a < t) (hst : s < t) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ U : Operator N, IsCircuit d U → ∀ M D : Count N,
      ‖M.high ((N:ℝ)^t)*conjugate U D.zero*M.low ((N:ℝ)^a)‖ ≤ Real.exp (-((N:ℝ)^s)) := by
  obtain ⟨v,hv,hvt⟩ := exists_between (max_lt hat hst)
  have hav : a < v := (le_max_left _ _).trans_lt hv
  have hsv : s < v := (le_max_right _ _).trans_lt hv
  obtain ⟨q,hvq,hqt⟩ := exists_between hvt
  filter_upwards [ih v q (ha.trans hav.le) hvq,
    eventually_two_powers_le hqt hat,eventually_pattern_cost ha hav hsv,
    Filter.eventually_ge_atTop 1] with N hN hp hc hN1
  intro U hU M D
  exact (M.low_propagation_bound (conjugate U D.zero) hN1 (Real.exp_pos _).le hp
    (fun K => hN U hU K D)).trans hc

lemma uniform_small_support {d : ℕ}
    (ih : ∀ s t : ℝ, 0 ≤ s → s < t → UniformLocalization d s t)
    {u w t : ℝ} (hu : 0 ≤ u) (_hw : 0 ≤ w) (hut : u < t) (hwt : w < t) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ U : Operator N, IsCircuit (d+1) U → ∀ M A : Count N,
      (A.support.card:ℝ) ≤ (N:ℝ)^u →
      ‖M.high ((N:ℝ)^t)*conjugate U A.zero*M.zero‖ ≤ Real.exp (-((N:ℝ)^w)) := by
  obtain ⟨v,hv,hvt⟩ := exists_between (max_lt hut hwt)
  have huv : u < v := (le_max_left _ _).trans_lt hv
  have hwv : w < v := (le_max_right _ _).trans_lt hv
  have hv0 : 0 < v := lt_of_le_of_lt hu huv
  obtain ⟨r₁,hvr₁,hr₁t⟩ := exists_between hvt
  obtain ⟨r₂,hr₁r₂,hr₂t⟩ := exists_between hr₁t
  filter_upwards [ih v r₁ hv0.le hvr₁,
    uniform_low_propagation ih (hv0.le.trans hvr₁.le) hv0.le hr₁r₂ (hvr₁.trans hr₁r₂),
    uniform_low_propagation ih (hv0.le.trans (hvr₁.trans hr₁r₂).le) hv0.le hr₂t hvt,
    eventually_exp_power_gap hwv huv hv0 3 1 1 (Real.log 9) (by norm_num) zero_lt_one] with N h₁ h₂ h₃ hc
  intro U hU M A hA
  obtain ⟨V,R,L,hV,rfl⟩ := hU
  have hb := small_support_layer_bound V hV.mem_unitary R L M A (Real.exp_pos _).le
    (fun D => h₁ V hV M D) (fun D => h₂ V hV M D) (fun D => h₃ V hV M D)
  have hcost : (9:ℝ)^A.support.card ≤ Real.exp (Real.log 9*(N:ℝ)^u) := by
    calc
      _ = Real.exp (Real.log 9*(A.support.card:ℝ)) := by
        rw [mul_comm,Real.exp_nat_mul,Real.exp_log (by norm_num)]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hA (Real.log_nonneg (by norm_num)))
  apply hb.trans
  calc
    _ ≤ Real.exp (Real.log 9*(N:ℝ)^u)*(3*Real.exp (-((N:ℝ)^v))) :=
      mul_le_mul_of_nonneg_right hcost (by positivity)
    _ = 3*Real.exp (Real.log 9*(N:ℝ)^u-(N:ℝ)^v) := by rw [sub_eq_add_neg,Real.exp_add]; ring
    _ ≤ _ := by simpa only [one_mul] using hc

lemma uniform_backward {d : ℕ}
    (ih : ∀ s t : ℝ, 0 ≤ s → s < t → UniformLocalization d s t)
    {s t a b u w : ℝ} (hs : 0 ≤ s) (hsa : s < a) (hau : a < u)
    (huw : u < w) (hwt : w < t) (htb : t < b) (hdegree : (a+b)/2 < u)
    (hnext : UniformLocalization (d+1) t b) : UniformLocalization (d+1) s t := by
  have ha : 0 < a := lt_of_le_of_lt hs hsa
  have hab : a < b := hau.trans (huw.trans (hwt.trans htb))
  filter_upwards [polynomial_approximation ha hab hdegree,
    uniform_small_support ih (ha.trans hau).le (ha.trans (hau.trans huw)).le (huw.trans hwt) hwt,
    hnext,eventually_backward_cost hs hsa hau huw hwt] with N hp hsmall htail hcost
  intro U hU M D
  obtain ⟨p,hdeg,hweight,hzero,hp⟩ := hp
  have hx := D.polynomial_transition M U p ((N:ℝ)^t) ((N:ℝ)^u) (Real.exp (-((N:ℝ)^w)))
    (Real.exp_pos _).le hdeg (fun A hA => hsmall U hU M A hA)
  have hx' : ‖M.high ((N:ℝ)^t)*conjugate U (D.polynomial p)*M.zero‖ ≤
      Real.exp ((N:ℝ)^u-(N:ℝ)^w) := by
    apply hx.trans
    calc
      _ ≤ Real.exp ((N:ℝ)^u)*Real.exp (-((N:ℝ)^w)) :=
        mul_le_mul_of_nonneg_right hweight (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have herr := D.polynomial_error_low p (Real.exp_pos _).le hzero (fun k hk hkb =>
    hp k hk (by exact_mod_cast hkb.le.trans (Nat.le_ceil ((N:ℝ)^b))))
  have hinv := htail (star U) hU.star_mem D M
  simp only [conjugate,star_star,mul_assoc] at hinv
  have hsq := M.backward_finite D U hU.mem_unitary p ((N:ℝ)^t) ((N:ℝ)^b)
    (Real.exp ((N:ℝ)^u-(N:ℝ)^w)) (Real.exp ((N:ℝ)^u))
    (Real.exp (-((N:ℝ)^a))) (Real.exp (-((N:ℝ)^t))) hx'
    ((D.polynomial_norm_le p).trans hweight) herr (by simpa only [mul_assoc] using hinv)
  have hsq' := hsq.trans hcost
  have heq : Real.exp (-2*(N:ℝ)^s) = (Real.exp (-((N:ℝ)^s)))^2 := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [heq] at hsq'
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp hsq'

/-- Uniform localization, proved by depth and finite scale induction. -/
theorem uniform_localization : ∀ d s t, 0 ≤ s → s < t → UniformLocalization d s t := by
  intro d
  induction d with
  | zero => intro s t _ hst; exact uniform_zero hst
  | succ d ih =>
    apply finite_scale_induction (UniformLocalization (d+1))
    · intro s t _ _ ht; exact uniform_large (d+1) ht
    · intro s t a b u w hs hsa hau huw hwt htb hdegree hnext
      exact uniform_backward ih hs hsa hau huw hwt htb hdegree hnext

/-- Uniform product-projection localization in the Euclidean operator norm. -/
theorem localization : LocalizationStatement := by
  intro d s t hs hst
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp (uniform_localization d s t hs hst)
  refine ⟨N₀,?_⟩
  intro N hN U hU M D
  simpa only [conjugate,mul_assoc] using hN₀ N hN U hU M D

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Physical ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

lemma local_gate_matrix {N : ℕ} (q : Fin N) (u : Matrix.unitaryGroup Bit ℂ) :
    Gate.matrix (.local q u) = localMatrix (singleLocal q u) := by
  classical
  change tensorMatrix (fun i => if i=q then (u:QubitOperator) else 1) =
    tensorMatrix (fun i => ((singleLocal q u i):QubitOperator))
  congr 1
  funext i
  unfold singleLocal
  split_ifs <;> rfl

lemma reflectList_rotate {N : ℕ} (l : List (Count N)) (L : LocalLayer N) :
    reflectList (l.map (fun A => A.rotate L)) = conjugate (localMatrix L) (reflectList l) := by
  induction l with
  | nil => simp [reflectList,conjugate_one (localMatrix_unitary L)]
  | cons A l ih =>
    simp only [List.map_cons,reflectList,List.prod_cons,List.map_map] at ih ⊢
    rw [conjugate_mul (localMatrix_unitary L),← ih]
    congr 1
    simp only [reflect,conjugate_sub,conjugate_one (localMatrix_unitary L),conjugate_smul]
    rw [A.rotate_zero L]
    rfl

lemma reflectList_rotate_commute {N : ℕ} (l : List (Count N)) (L : LocalLayer N) :
    localMatrix L*reflectList l = reflectList (l.map (fun A => A.rotate L))*localMatrix L := by
  rw [reflectList_rotate,conjugate]
  simp only [mul_assoc,Unitary.star_mul_self_of_mem (localMatrix_unitary L),mul_one]

lemma normalCounts_support {N : ℕ} (l : List (Gate N)) :
    ∀ A ∈ normalCounts l, ∃ g ∈ l, A.support=g.support := by
  induction l with
  | nil => simp [normalCounts]
  | cons g l ih =>
    cases g with
    | «local» q u =>
      intro A hA
      obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hA
      obtain ⟨g,hg,hBg⟩ := ih B hB
      exact ⟨g,List.mem_cons_of_mem _ hg,hBg⟩
    | toffoli c t ht =>
      intro A hA
      rcases List.mem_cons.mp hA with rfl | hA
      · exact ⟨.toffoli c t ht,List.mem_cons_self ..,rfl⟩
      · obtain ⟨g,hg,hAg⟩ := ih A hA
        exact ⟨g,List.mem_cons_of_mem _ hg,hAg⟩

lemma normalCounts_disjoint {N : ℕ} (l : List (Gate N))
    (hl : l.Pairwise (fun A B => Disjoint A.support B.support)) :
    (normalCounts l).Pairwise (fun A B => Disjoint A.support B.support) := by
  induction l with
  | nil => simp [normalCounts]
  | cons g l ih =>
    have hparts := List.pairwise_cons.mp hl
    clear hl
    cases g with
    | «local» q u =>
      exact (ih hparts.2).map (fun A : Count N => A.rotate (singleLocal q u)) (fun _ _ h => h)
    | toffoli c t ht =>
      apply List.pairwise_cons.mpr
      refine ⟨?_,ih hparts.2⟩
      intro A hA
      obtain ⟨g,hg',hAg⟩ := normalCounts_support l A hA
      change Disjoint (Gate.support (.toffoli c t ht)) A.support
      rw [hAg]
      exact hparts.1 g hg'

lemma gateList_normal {N : ℕ} (l : List (Gate N)) :
    (l.map Gate.matrix).prod = reflectList (normalCounts l)*localMatrix (normalLocal l) := by
  induction l with
  | nil => simp [normalCounts,normalLocal,reflectList,localMatrix]
  | cons g l ih =>
    cases g with
    | «local» q u =>
      simp only [List.map_cons,List.prod_cons,normalCounts,normalLocal]
      rw [local_gate_matrix,ih,← mul_assoc,reflectList_rotate_commute,mul_assoc,localMatrix_mul]
    | toffoli c t ht =>
      simp only [List.map_cons,List.prod_cons,normalCounts,normalLocal]
      rw [toffoli_reflection,ih]
      simp only [reflectList,List.map_cons,List.prod_cons,mul_assoc]

lemma physicalLayer_isCircuit {N : ℕ} (P : PhysicalLayer N) :
    IsCircuit 1 (physicalLayerMatrix P) := by
  let R : ReflectionLayer N := ⟨normalCounts P.gates,normalCounts_disjoint _ P.disjoint⟩
  refine ⟨1,R,normalLocal P.gates,?_,?_⟩
  · exact ⟨fun _ => 1,by simp [localMatrix]⟩
  · rw [one_mul,reflectionMatrix_eq]
    exact gateList_normal P.gates

lemma physicalCircuit_isCircuit {N : ℕ} (l : List (PhysicalLayer N)) :
    IsCircuit l.length (physicalCircuitMatrix l) := by
  induction l with
  | nil => exact ⟨fun _ => 1,by simp [physicalCircuitMatrix,localMatrix]⟩
  | cons L l ih =>
    have h := ih.mul (physicalLayer_isCircuit L)
    simpa only [physicalCircuitMatrix,List.map_cons,List.reverse_cons,List.prod_append,
      List.prod_singleton,List.length_cons] using h

lemma IsCircuit.succ {N d : ℕ} {U : Operator N} (hU : IsCircuit d U) : IsCircuit (d+1) U := by
  refine ⟨U,⟨[],by simp⟩,fun _ => 1,hU,?_⟩
  simp [reflectionMatrix,localMatrix]

lemma IsCircuit.mono {N d e : ℕ} {U : Operator N} (hU : IsCircuit d U) (hde : d ≤ e) :
    IsCircuit e U := by
  induction hde with
  | refl => exact hU
  | step h ih => exact ih.succ

lemma IsCircuit.local_mul {N d : ℕ} {U : Operator N} (hU : IsCircuit d U) (L : LocalLayer N) :
    IsCircuit d (localMatrix L*U) := by
  have hL : IsCircuit 0 (localMatrix L) := ⟨L,rfl⟩
  simpa only [Nat.zero_add] using hL.mul hU

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Computational ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma inputSet_card {n N : ℕ} (hnN : n ≤ N) : (inputSet n N).card=n := by
  rw [inputSet,Fin.card_filter_val_lt,min_eq_right hnN]

lemma inputHadamard_star (n N : ℕ) : star (localMatrix (inputHadamard n N)) =
    localMatrix (inputHadamard n N) := by
  rw [localMatrix_star]
  congr 1
  funext i
  apply Subtype.ext
  by_cases hi : i.val<n
  · simp only [inputHadamard,ite_eq_left hi,Unitary.coe_star,hadamardGate]
    exact bitH_star
  · simp [inputHadamard,hi]

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Parity ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

lemma eventually_exp_neg_power_lt {s ε : ℝ} (hs : 0<s) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, Real.exp (-(N:ℝ)^s)<ε := by
  filter_upwards [eventually_power_le hs (-Real.log ε+1)] with N hN
  rw [Real.rpow_zero,mul_one] at hN
  rw [← Real.exp_log hε]
  exact Real.exp_lt_exp.mpr (by linarith only [hN])

lemma polynomial_qubit_threshold {n N : ℕ} {c t : ℝ} (hn : 1≤n)
    (ht : 0≤t) (hct : c*t≤1) (hN : (N:ℝ)≤(n:ℝ)^c) : (N:ℝ)^t≤(n:ℝ) := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  calc
    (N:ℝ)^t ≤ ((n:ℝ)^c)^t := Real.rpow_le_rpow (Nat.cast_nonneg N) hN ht
    _ = (n:ℝ)^(c*t) := (Real.rpow_mul (Nat.cast_nonneg n) c t).symm
    _ ≤ (n:ℝ)^1 := Real.rpow_le_rpow_of_exponent_le hn1 hct
    _ = (n:ℝ) := Real.rpow_one _

lemma hadamard_high_entry_bound {n N : ℕ} (hnN : n≤N) (W : Operator N)
    (out : Fin N) (x : Word n) {r : ℝ} (hr : r≤(n:ℝ)) :
    ‖(localMatrix (inputHadamard n N)*(star W*(outputZeroCount out).zero*W)*
      localMatrix (inputHadamard n N))
      (flipWord (inputSet n N) (inputWord x)) (inputWord x)‖ ≤
    ‖(computationalCount (inputWord x)).high r*(localMatrix (inputHadamard n N)*star W)*
      (outputZeroCount out).zero*star (localMatrix (inputHadamard n N)*star W)*
      (computationalCount (inputWord x)).zero‖ := by
  have hcard : r≤((inputSet n N).card:ℝ) := by simpa only [inputSet_card hnN] using hr
  have hh := high_entry_bound
    (localMatrix (inputHadamard n N)*(star W*(outputZeroCount out).zero*W)*
      localMatrix (inputHadamard n N)) (inputWord x) (inputSet n N) hcard
  simpa only [star_mul,star_star,inputHadamard_star,mul_assoc] using hh

/-- The measured-output parity lower bound, allowing arbitrary final garbage and
all polynomially many initially zero ancillas. No cleanliness assumption is used. -/
theorem parity_lower_bound : ParityStatement := by
  intro d c ε hc hε _
  have hcpos : 0<c := lt_of_lt_of_le zero_lt_one hc
  let t : ℝ := 1/(2*c)
  let s : ℝ := t/2
  have ht : 0<t := by dsimp [t]; positivity
  have hs : 0<s := by dsimp [s]; positivity
  have hst : s<t := by dsimp [s]; linarith only [ht]
  have hct : c*t≤1 := by
    have hceq : c*t=1/2 := by dsimp [t]; field_simp
    rw [hceq]
    norm_num
  obtain ⟨N₀,hN₀⟩ := localization d s t hs.le hst
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp (eventually_exp_neg_power_lt hs hε)
  refine ⟨max 1 (max N₀ N₁),?_⟩
  intro n hn N hnN hsize layers hdepth out hsuccess
  have hn1 : 1≤n := (le_max_left 1 (max N₀ N₁)).trans hn
  have hn0 : 0<n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hNN₀ : N₀≤N := (le_trans (le_max_left N₀ N₁) (le_max_right 1 (max N₀ N₁))).trans (hn.trans hnN)
  have hNN₁ : N₁≤N := (le_trans (le_max_right N₀ N₁) (le_max_right 1 (max N₀ N₁))).trans (hn.trans hnN)
  let W := physicalCircuitMatrix layers
  let H := localMatrix (inputHadamard n N)
  have hW : IsCircuit d W := (physicalCircuit_isCircuit layers).mono hdepth
  have hU : IsCircuit d (H*star W) := hW.star_mem.local_mul (inputHadamard n N)
  have hthreshold : (N:ℝ)^t≤(n:ℝ) := polynomial_qubit_threshold hn1 ht.le hct hsize
  have hentry (x : Word n) :
      ‖(H*(star W*(outputZeroCount out).zero*W)*H)
        (flipWord (inputSet n N) (inputWord x)) (inputWord x)‖ ≤ Real.exp (-(N:ℝ)^s) := by
    exact (hadamard_high_entry_bound hnN W out x hthreshold).trans
      (hN₀ N hNN₀ (H*star W) hU (computationalCount (inputWord x)) (outputZeroCount out))
  have hadv := parity_advantage_from_entries hn0 hnN W hW.mem_unitary out hsuccess hentry
  exact (not_le_of_gt (hN₁ N hNN₁)) hadv

end QAC

end

end OAI

-- ---- mission target ----
open OAI
open scoped BigOperators Matrix.Norms.L2Operator
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

theorem solution : QAC.ParityStatement := by
  first
    | exact OAI.QAC.parity_lower_bound
    | (apply OAI.QAC.parity_lower_bound <;> assumption)
    | (intros; apply OAI.QAC.parity_lower_bound <;> assumption)
