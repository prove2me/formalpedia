-- Prove2me | solution 1 for OAI.QAC.Count.low_propagation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:05:51.360921+00:00
-- url     : https://prove2.me/submissions/6a523912-6969-4a9d-ba53-3e282fd6e7f7

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Transition.lean:L129-L144
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.Count.low_propagation_bound. The node keeps its source
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
import Theorems.Thm_OAI_QAC_Count_high_mul_pattern
import Theorems.Thm_OAI_QAC_Count_pattern_mul
import Theorems.Thm_OAI_QAC_rankOne_projection

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

section SpectralAlgebra

variable {A ι : Type*} [CStarAlgebra A]

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

lemma Count.flip_zero {N : ℕ} (M : Count N) (F : Finset (Fin N)) :
    (M.flip F).zero = M.pattern F := by
  classical
  dsimp only [Count.zero, Count.flip, Count.pattern]
  congr 1
  funext i
  split_ifs with hi hF
  · exact rankOne_orthogonalVector (M.normalized i hi)
  · rfl
  · rfl

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Spectral ----
-- Lean 4.34 name of List.sum_le_card_nsmul (same statement) in Mathlib 0df444a.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma Count.flip_pattern {N : ℕ} (M : Count N) (F G : Finset (Fin N)) :
    (M.flip F).pattern G = M.pattern (F ∆ G) := by
  classical
  dsimp only [Count.pattern, Count.flip]
  congr 1
  funext i
  by_cases hi : i ∈ M.support
  · have hv := rankOne_orthogonalVector (M.normalized i hi)
    by_cases hF : i ∈ F <;> by_cases hG : i ∈ G <;>
      simp [hi, hF, hG, Finset.mem_symmDiff, hv]
  · simp [hi]

lemma symmDiff_subset_of_subset {α : Type*} [DecidableEq α] {F G S : Finset α}
    (hF : F ⊆ S) (hG : G ⊆ S) : F ∆ G ⊆ S :=
  Finset.symmDiff_subset_union.trans (Finset.union_subset hF hG)

lemma card_le_add_symmDiff {α : Type*} [DecidableEq α] (F G : Finset α) :
    G.card ≤ F.card + (F ∆ G).card := by
  have h : G ⊆ F ∪ (F ∆ G) := by
    intro i hi
    by_cases hF : i ∈ F
    · exact Finset.mem_union_left _ hF
    · exact Finset.mem_union_right _ (Finset.mem_symmDiff.mpr (Or.inr ⟨hi,hF⟩))
  exact (Finset.card_le_card h).trans (Finset.card_union_le _ _)

lemma Count.high_flip_absorb {N : ℕ} (M : Count N) (F : Finset (Fin N))
    (hF : F ⊆ M.support) {r q : ℝ} (hrq : q + F.card ≤ r) :
    (M.flip F).high q * M.high r = M.high r := by
  classical
  rw [M.high_eq_sum_filter r, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G hG
  have hrG : r ≤ (G.card : ℝ) := (Finset.mem_filter.mp hG).2
  have hGs : G ⊆ M.support := Finset.mem_powerset.mp (Finset.mem_filter.mp hG).1
  have hFGs : F ∆ G ⊆ (M.flip F).support := symmDiff_subset_of_subset hF hGs
  have heq : M.pattern G = (M.flip F).pattern (F ∆ G) := by
    rw [M.flip_pattern, symmDiff_symmDiff_cancel_left]
  rw [heq, (M.flip F).high_mul_pattern _ hFGs, ite_eq_left]
  have hc : (G.card : ℝ) ≤ F.card + (F ∆ G).card := by exact_mod_cast card_le_add_symmDiff F G
  linarith

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

lemma norm_mul_le_right {A : Type*} [NormedRing A] (x y : A) (hx : ‖x‖ ≤ 1) :
    ‖x*y‖ ≤ ‖y‖ := (norm_mul_le _ _).trans (by nlinarith only [hx, norm_nonneg y])

lemma Count.high_flip_norm {N : ℕ} (M : Count N) (F : Finset (Fin N))
    (hF : F ⊆ M.support) {r q : ℝ} (hrq : q + F.card ≤ r) (B : Operator N) :
    ‖M.high r * B * M.pattern F‖ ≤ ‖(M.flip F).high q * B * (M.flip F).zero‖ := by
  have habs := congrArg star (M.high_flip_absorb F hF hrq)
  simp only [star_mul, (M.high_projection r).isSelfAdjoint.star_eq,
    ((M.flip F).high_projection q).isSelfAdjoint.star_eq] at habs
  rw [M.flip_zero]
  calc
    _ = ‖M.high r * ((M.flip F).high q * B * M.pattern F)‖ := by rw [← mul_assoc, ← mul_assoc, habs]
    _ ≤ _ := norm_mul_le_right _ _ (IsStarProjection.norm_le _ (M.high_projection r))

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

lemma sum_powers_bound (N K : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range K, N^k ≤ (N+1)^K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hpow : N^K ≤ (N+1)^K := Nat.pow_le_pow_left (by omega) _
    have hmul : (N+1)^K ≤ (N+1)^K*N := by
      simpa only [mul_one] using Nat.mul_le_mul_left ((N+1)^K) hN
    nlinarith only [ih, hpow, hmul]

lemma low_patterns_card {N : ℕ} (S : Finset (Fin N)) {r : ℝ} (hN : 1 ≤ N) :
    (S.powerset.filter (fun F => (F.card:ℝ) < r)).card ≤ (N+1)^(⌈r⌉₊+1) := by
  classical
  have hsub : S.powerset.filter (fun F => (F.card:ℝ) < r) ⊆
      (Finset.range (⌈r⌉₊+1)).biUnion (fun k => S.powersetCard k) := by
    intro F hF
    obtain ⟨hFS, hFr⟩ := Finset.mem_filter.mp hF
    refine Finset.mem_biUnion.mpr ⟨F.card, ?_, Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hFS,rfl⟩⟩
    rw [Finset.mem_range]
    have h : (F.card:ℝ) ≤ ⌈r⌉₊ := hFr.le.trans (Nat.le_ceil r)
    have : F.card ≤ ⌈r⌉₊ := by exact_mod_cast h
    omega
  calc
    _ ≤ ((Finset.range (⌈r⌉₊+1)).biUnion (fun k => S.powersetCard k)).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range (⌈r⌉₊+1), (S.powersetCard k).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (⌈r⌉₊+1), N^k := by
      apply Finset.sum_le_sum
      intro k _
      rw [Finset.card_powersetCard]
      exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by simpa using Finset.card_le_univ S) _)
    _ ≤ _ := sum_powers_bound N _ hN

lemma Count.low_propagation_bound {N : ℕ} (M : Count N) (B : Operator N)
    {r q R δ : ℝ} (hN : 1 ≤ N) (hδ : 0 ≤ δ) (hrq : q + r ≤ R)
    (hB : ∀ K : Count N, ‖K.high q * B * K.zero‖ ≤ δ) :
    ‖M.high R * B * M.low r‖ ≤ (N+1:ℝ)^(⌈r⌉₊+1) * δ := by
  classical
  rw [M.low_eq_sum, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ F ∈ M.support.powerset.filter (fun F => (F.card:ℝ) < r), δ := by
      apply Finset.sum_le_sum
      intro F hF
      obtain ⟨hFs, hFr⟩ := Finset.mem_filter.mp hF
      exact (M.high_flip_norm F (Finset.mem_powerset.mp hFs)
        (by linarith) B).trans (hB (M.flip F))
    _ = ((M.support.powerset.filter (fun F => (F.card:ℝ) < r)).card:ℝ)*δ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast low_patterns_card M.support (r:=r) hN) hδ

section ThreeFactors
variable {A : Type*} [CStarAlgebra A]

end ThreeFactors

section Conjugation
variable {A : Type*} [CStarAlgebra A]

end Conjugation

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

theorem solution {N : ℕ} (M : Count N) (B : Operator N)
    {r q R δ : ℝ} (hN : 1 ≤ N) (hδ : 0 ≤ δ) (hrq : q + r ≤ R)
    (hB : ∀ K : Count N, ‖K.high q * B * K.zero‖ ≤ δ) :
    ‖M.high R * B * M.low r‖ ≤ (N+1:ℝ)^(⌈r⌉₊+1) * δ := by
  first
    | exact OAI.QAC.Count.low_propagation_bound M B hN hδ hrq hB
    | exact OAI.QAC.Count.low_propagation_bound
    | (apply OAI.QAC.Count.low_propagation_bound <;> assumption)
    | (intros; apply OAI.QAC.Count.low_propagation_bound <;> assumption)
