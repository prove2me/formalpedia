-- Prove2me | solution 1 for OAI.QAC.Count.backward_finite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:19:38.726482+00:00
-- url     : https://prove2.me/submissions/1e2fb8d4-6c25-4c04-951b-8dc0e7ac15cc

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Backward.lean:L65-L103
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.Count.backward_finite. The node keeps its source
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
import Theorems.Thm_OAI_QAC_projection_transition_square
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

section SpectralAlgebra

variable {A ι : Type*} [CStarAlgebra A]

variable [PartialOrder A] [StarOrderedRing A]

end SpectralAlgebra

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

lemma norm_mul_le_left {A : Type*} [NormedRing A] (x y : A) (hy : ‖y‖ ≤ 1) :
    ‖x*y‖ ≤ ‖x‖ := (norm_mul_le _ _).trans (by nlinarith only [hy, norm_nonneg x])

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

lemma norm_unitary_conjugate {U : A} (hU : U ∈ unitary A) (B : A) :
    ‖U * B * star U‖ = ‖B‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU), CStarRing.norm_mem_unitary_mul _ hU]

lemma conjugate_projection {U B : A} (hU : U ∈ unitary A) (hB : IsStarProjection B) :
    IsStarProjection (U * B * star U) := by
  rw [isStarProjection_iff']
  constructor
  · calc
      _ = U * (B * B) * star U := by
        simp only [mul_assoc, ← mul_assoc (star U) U, Unitary.star_mul_self_of_mem hU, one_mul]
      _ = _ := by rw [hB.isIdempotentElem.eq]
  · simp only [star_mul, star_star, hB.isSelfAdjoint.star_eq, mul_assoc]

lemma norm_split_bound (E W P Q : A) (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) :
    ‖E*P*Q‖ ≤ ‖E*(1-W)‖ + ‖E‖*‖W*P*Q‖ := by
  have heq : E*P*Q = E*(1-W)*P*Q + E*(W*P*Q) := by noncomm_ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_mul_le_left _ _ hQ).trans (norm_mul_le_left _ _ hP)) (norm_mul_le _ _))
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

lemma Count.backward_finite {N : ℕ} (M D : Count N) (U : Operator N) (hU : U ∈ unitary (Operator N))
    (p : Polynomial ℝ) (r b A B E T : ℝ)
    (hx : ‖M.high r*conjugate U (D.polynomial p)*M.zero‖ ≤ A)
    (hp : ‖D.polynomial p‖ ≤ B)
    (he : ‖(D.zero-D.polynomial p)*D.low b‖ ≤ E)
    (ht : ‖D.high b*star U*M.zero*U*D.zero‖ ≤ T) :
    ‖M.high r*conjugate U D.zero*M.zero‖^2 ≤ A+E+(1+B)*T := by
  let Q := conjugate U D.zero
  let X := conjugate U (D.polynomial p)
  let W := conjugate U (D.high b)
  have hQ : IsStarProjection Q := conjugate_projection hU D.zero_projection
  have hQn : ‖Q‖ ≤ 1 := IsStarProjection.norm_le _ hQ
  have hXn : ‖X‖ ≤ B := by
    change ‖U*D.polynomial p*star U‖ ≤ B
    rw [norm_unitary_conjugate hU]
    exact hp
  have hn : ‖Q-X‖ ≤ 1+B := (norm_sub_le _ _).trans (add_le_add hQn hXn)
  have hlow : ‖(Q-X)*(1-W)‖ ≤ E := by
    have heq : (Q-X)*(1-W) = conjugate U ((D.zero-D.polynomial p)*D.low b) := by
      change (conjugate U D.zero-conjugate U (D.polynomial p))*(1-conjugate U (D.high b)) = _
      simp only [Count.low,conjugate_mul hU,conjugate_sub,conjugate_one hU]
    rw [heq]
    change ‖U*((D.zero-D.polynomial p)*D.low b)*star U‖ ≤ E
    rw [norm_unitary_conjugate hU]
    exact he
  have htail : ‖W*M.zero*Q‖ ≤ T := by
    have heq : W*M.zero*Q = conjugate U (D.high b*star U*M.zero*U*D.zero) := by
      dsimp only [W,Q,conjugate]
      simp only [mul_assoc]
    rw [heq]
    change ‖U*(D.high b*star U*M.zero*U*D.zero)*star U‖ ≤ T
    rw [norm_unitary_conjugate hU]
    exact ht
  have herr : ‖(Q-X)*M.zero*Q‖ ≤ E+(1+B)*T := by
    apply (norm_split_bound (Q-X) W M.zero Q (IsStarProjection.norm_le _ M.zero_projection) hQn).trans
    exact add_le_add hlow (mul_le_mul hn htail (norm_nonneg _) ((norm_nonneg _).trans hn))
  have hsquare := projection_transition_square (M.high r) M.zero Q X
    (M.high_projection r) M.zero_projection hQ
  exact hsquare.trans ((add_le_add hx herr).trans_eq (by ring))

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

theorem solution {N : ℕ} (M D : Count N) (U : Operator N) (hU : U ∈ unitary (Operator N))
    (p : Polynomial ℝ) (r b A B E T : ℝ)
    (hx : ‖M.high r*conjugate U (D.polynomial p)*M.zero‖ ≤ A)
    (hp : ‖D.polynomial p‖ ≤ B)
    (he : ‖(D.zero-D.polynomial p)*D.low b‖ ≤ E)
    (ht : ‖D.high b*star U*M.zero*U*D.zero‖ ≤ T) :
    ‖M.high r*conjugate U D.zero*M.zero‖^2 ≤ A+E+(1+B)*T := by
  first
    | exact OAI.QAC.Count.backward_finite M D U hU p r b A B E T hx hp he ht
    | exact OAI.QAC.Count.backward_finite
    | (apply OAI.QAC.Count.backward_finite <;> assumption)
    | (intros; apply OAI.QAC.Count.backward_finite <;> assumption)
