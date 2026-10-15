-- Prove2me | solution 1 for OAI.QAC.Count.polynomial_transition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:17:17.532506+00:00
-- url     : https://prove2.me/submissions/612257c0-20e9-4e5e-b2d5-03bfe48124f5

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Backward.lean:L45-L63
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.Count.polynomial_transition. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
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
import Theorems.Thm_OAI_QAC_Count_pattern_mul
import Theorems.Thm_OAI_QAC_rankOne_projection

-- ---- from OAI.InformationTheory.QuantumCircuit.ProductProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

lemma Count.pattern_projection {N : ℕ} (M : Count N) (F : Finset (Fin N)) :
    IsStarProjection (M.pattern F) := by
  apply tensorMatrix_projection
  intro i
  split_ifs with hi hF
  · exact (rankOne_projection (M.normalized i hi)).one_sub
  · exact rankOne_projection (M.normalized i hi)
  · exact IsStarProjection.one _

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

variable [PartialOrder A] [StarOrderedRing A]

end SpectralAlgebra

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Circuit ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma rankOne_orthogonalVector {v : Bit → ℂ} (hv : ∑ b, Complex.normSq (v b) = 1) :
    rankOne (orthogonalVector v) = 1 - rankOne v := by
  have h := normalized_complex hv
  simp only [Fin.sum_univ_two, Complex.star_def] at h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rankOne, orthogonalVector]
  · linear_combination h
  · ring
  · ring
  · linear_combination h

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Count ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma Count.restrict_zero_mul {N : ℕ} (M : Count N) (S T : Finset (Fin N)) :
    (M.restrict S).zero * (M.restrict T).zero = (M.restrict (S ∪ T)).zero := by
  classical
  dsimp only [Count.zero, Count.restrict]
  rw [tensorMatrix_mul]
  congr 1
  funext i
  by_cases hi : i ∈ M.support
  · by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
      simp [hi, hS, hT, (rankOne_projection (M.normalized i hi)).isIdempotentElem.eq]
  · simp [hi]

lemma Count.restrict_support_card {N : ℕ} (M : Count N) (S : Finset (Fin N)) :
    (M.restrict S).support.card ≤ S.card := Finset.card_le_card Finset.inter_subset_right

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Spectral ----
-- Lean 4.34 name of List.sum_le_card_nsmul (same statement) in Mathlib 0df444a.
private abbrev List.sum_le_length_nsmul := @List.sum_le_card_nsmul

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

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

lemma Count.generator_eq_restrict {N : ℕ} (M : Count N) (i : Fin N) (hi : i ∈ M.support) :
    tensorMatrix (fun j => if j = i then 1-rankOne (M.vector i) else 1) =
      ((M.flip M.support).restrict {i}).zero := by
  classical
  dsimp only [Count.zero, Count.restrict, Count.flip]
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Finset.mem_inter, Finset.mem_singleton, hi, true_and, ite_true]
    exact (rankOne_orthogonalVector (M.normalized i hi)).symm
  · simp [hji]

lemma selectionSets_card {ι : Type*} [DecidableEq ι] (S : Finset ι) (k : ℕ) :
    ∀ F ∈ selectionSets S k, F.card ≤ k := by
  induction k with
  | zero => intro F hF; simpa [selectionSets] using hF
  | succ k ih =>
    intro F hF
    obtain ⟨i, _, hFi⟩ := List.mem_flatMap.mp hF
    obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hFi
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (ih G hG) 1)

lemma selectionSets_length {ι : Type*} [DecidableEq ι] (S : Finset ι) (k : ℕ) :
    (selectionSets S k).length = S.card^k := by
  induction k with
  | zero => simp [selectionSets]
  | succ k ih => simp [selectionSets, List.length_flatMap, ih, pow_succ, mul_comm]

lemma list_sum_flatMap {ι κ A : Type*} [AddMonoid A] (l : List ι) (f : ι → List κ) (g : κ → A) :
    ((l.flatMap f).map g).sum = (l.map (fun i => ((f i).map g).sum)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

lemma Count.selectionSets_sum {N : ℕ} (M : Count N) (S : Finset (Fin N)) (k : ℕ) :
    ((selectionSets S k).map (fun F => (M.restrict F).zero)).sum =
      (∑ i ∈ S, (M.restrict {i}).zero)^k := by
  classical
  induction k with
  | zero => simp [selectionSets,Count.zero,Count.restrict]
  | succ k ih =>
    rw [selectionSets, list_sum_flatMap]
    simp only [List.map_map]
    dsimp only [Function.comp_def]
    have hi : ∀ i, ((selectionSets S k).map (fun F => (M.restrict (insert i F)).zero)).sum =
        (M.restrict {i}).zero * ((selectionSets S k).map (fun F => (M.restrict F).zero)).sum := by
      intro i
      simp_rw [← Finset.singleton_union, ← M.restrict_zero_mul]
      exact List.sum_map_mul_left _ _ _
    simp_rw [hi,ih]
    rw [List.sum_map_mul_right, ← List.sum_toFinset _ S.nodup_toList, Finset.toList_toFinset, pow_succ']

lemma Count.operator_monomials {N : ℕ} (M : Count N) (k : ℕ) :
    M.operator^k = ((selectionSets M.support k).map
      (fun F => ((M.flip M.support).restrict F).zero)).sum := by
  rw [(M.flip M.support).selectionSets_sum]
  congr 1
  unfold Count.operator
  apply Finset.sum_congr rfl
  intro i hi
  exact M.generator_eq_restrict i hi

lemma list_norm_sum_le {A : Type*} [SeminormedAddCommGroup A] (l : List A) :
    ‖l.sum‖ ≤ (l.map norm).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons,List.map_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

lemma list_norm_sum_le_const {ι A : Type*} [SeminormedAddCommGroup A]
    (l : List ι) (f : ι → A) (C : ℝ) (hf : ∀ i ∈ l, ‖f i‖ ≤ C) :
    ‖(l.map f).sum‖ ≤ l.length * C := by
  apply (list_norm_sum_le _).trans
  rw [List.map_map]
  have h := List.sum_le_length_nsmul (l.map (norm ∘ f)) C (by
    intro c hc
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    exact hf i hi)
  simpa only [List.length_map, nsmul_eq_mul] using h

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

lemma conjugate_smul (U B : A) (r : ℝ) : conjugate U (r • B) = r • conjugate U B := by
  simp only [conjugate,mul_smul_comm,smul_mul_assoc]

lemma conjugate_list_sum {ι : Type*} (U : A) (l : List ι) (f : ι → A) :
    conjugate U (l.map f).sum = (l.map (fun i => conjugate U (f i))).sum := by
  simp only [conjugate,← List.sum_map_mul_left,← List.sum_map_mul_right]

end Conjugation

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Backward ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma conjugate_finset_sum {A ι : Type*} [CStarAlgebra A] (U : A) (s : Finset ι) (f : ι → A) :
    conjugate U (∑ i ∈ s, f i) = ∑ i ∈ s, conjugate U (f i) := by
  simp only [conjugate,Finset.mul_sum,Finset.sum_mul]

lemma Count.monomial_transition {N : ℕ} (D M : Count N) (U : Operator N) (r μ δ : ℝ)
    (hδ : 0 ≤ δ) (k : ℕ) (hk : (k:ℝ) ≤ μ)
    (hA : ∀ A : Count N, (A.support.card:ℝ) ≤ μ →
      ‖M.high r*conjugate U A.zero*M.zero‖ ≤ δ) :
    ‖M.high r*conjugate U (D.operator^k)*M.zero‖ ≤ (N:ℝ)^k*δ := by
  rw [D.operator_monomials,conjugate_list_sum,← List.sum_map_mul_left,← List.sum_map_mul_right]
  have h := list_norm_sum_le_const (selectionSets D.support k)
    (fun F => M.high r*conjugate U ((D.flip D.support).restrict F).zero*M.zero) δ (by
      intro F hF
      apply hA
      have hc := ((D.flip D.support).restrict_support_card F).trans (selectionSets_card _ _ F hF)
      exact (show (((D.flip D.support).restrict F).support.card:ℝ) ≤ k by exact_mod_cast hc).trans hk)
  apply h.trans
  rw [selectionSets_length]
  apply mul_le_mul_of_nonneg_right _ hδ
  exact_mod_cast Nat.pow_le_pow_left (show D.support.card ≤ N by simpa using Finset.card_le_univ D.support) k

lemma Count.polynomial_transition {N : ℕ} (D M : Count N) (U : Operator N)
    (p : Polynomial ℝ) (r μ δ : ℝ) (hδ : 0 ≤ δ) (hp : (p.natDegree:ℝ) ≤ μ)
    (hA : ∀ A : Count N, (A.support.card:ℝ) ≤ μ →
      ‖M.high r*conjugate U A.zero*M.zero‖ ≤ δ) :
    ‖M.high r*conjugate U (D.polynomial p)*M.zero‖ ≤ weight N p*δ := by
  classical
  rw [D.polynomial_eq_sum,conjugate_finset_sum,Finset.mul_sum,Finset.sum_mul]
  simp only [conjugate_smul,mul_smul_comm,smul_mul_assoc]
  apply (norm_sum_le _ _).trans
  change (∑ k ∈ p.support, ‖p.coeff k • (M.high r*conjugate U (D.operator^k)*M.zero)‖) ≤
    (∑ k ∈ p.support, |p.coeff k| *(N:ℝ)^k)*δ
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_smul,Real.norm_eq_abs]
  rw [mul_assoc (|p.coeff k|) ((N:ℝ)^k)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply D.monomial_transition M U r μ δ hδ k _ hA
  exact (show (k:ℝ) ≤ p.natDegree by exact_mod_cast Polynomial.le_natDegree_of_mem_supp k hk).trans hp

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

theorem solution {N : ℕ} (D M : Count N) (U : Operator N)
    (p : Polynomial ℝ) (r μ δ : ℝ) (hδ : 0 ≤ δ) (hp : (p.natDegree:ℝ) ≤ μ)
    (hA : ∀ A : Count N, (A.support.card:ℝ) ≤ μ →
      ‖M.high r*conjugate U A.zero*M.zero‖ ≤ δ) :
    ‖M.high r*conjugate U (D.polynomial p)*M.zero‖ ≤ weight N p*δ := by
  first
    | exact OAI.QAC.Count.polynomial_transition D M U p r μ δ hδ hp hA
    | exact OAI.QAC.Count.polynomial_transition
    | (apply OAI.QAC.Count.polynomial_transition <;> assumption)
    | (intros; apply OAI.QAC.Count.polynomial_transition <;> assumption)
