-- Prove2me | solution 1 for OAI.QAC.small_support_layer_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:11:24.363743+00:00
-- url     : https://prove2.me/submissions/b2380d6b-ed66-4289-a358-9131820255bb

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Reflection.lean:L186-L210
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.small_support_layer_bound. The node keeps its source
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
import Theorems.Thm_OAI_QAC_Count_pattern_mul
import Theorems.Thm_OAI_QAC_list_conjugate_filter
import Theorems.Thm_OAI_QAC_list_disjoint_hits_length
import Theorems.Thm_OAI_QAC_rankOne_projection
import Theorems.Thm_OAI_QAC_reflectionTerms_sum
import Theorems.Thm_OAI_QAC_three_factor_transition

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

lemma reflection_unitary {N : ℕ} (M : Count N) :
    (1 : Operator N) - (2 : ℂ) • M.zero ∈ unitary (Operator N) := by
  have h := M.zero_projection.two_mul_sub_one_mem_unitary
  have hneg : -(2 * M.zero - 1) ∈ unitary (Operator N) := by
    simpa only [Unitary.mem_iff, star_neg, neg_mul_neg] using h
  simpa only [two_smul, two_mul, neg_sub] using hneg

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Count ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma Count.disjoint_commute {N : ℕ} (A B : Count N) (h : Disjoint A.support B.support) :
    Commute A.zero B.zero := by
  classical
  show A.zero * B.zero = B.zero * A.zero
  dsimp only [Count.zero]
  rw [tensorMatrix_mul, tensorMatrix_mul]
  congr 1
  funext i
  by_cases hA : i ∈ A.support
  · have hB : i ∉ B.support := Finset.disjoint_left.mp h hA
    simp [hA, hB]
  · simp [hA]

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

lemma Count.low_projection {N : ℕ} (M : Count N) (r : ℝ) : IsStarProjection (M.low r) :=
  (M.high_projection r).one_sub

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

lemma conjugate_projection {U B : A} (hU : U ∈ unitary A) (hB : IsStarProjection B) :
    IsStarProjection (U * B * star U) := by
  rw [isStarProjection_iff']
  constructor
  · calc
      _ = U * (B * B) * star U := by
        simp only [mul_assoc, ← mul_assoc (star U) U, Unitary.star_mul_self_of_mem hU, one_mul]
      _ = _ := by rw [hB.isIdempotentElem.eq]
  · simp only [star_mul, star_star, hB.isSelfAdjoint.star_eq, mul_assoc]

end NormAlgebra

/-- Scalar list estimates retain multiplicities, including the ordered monomials. -/
lemma norm_list_smul_sum {ι A : Type*} [SeminormedAddCommGroup A] [NormedSpace ℝ A]
    (l : List ι) (c : ι → ℝ) (f : ι → A) (δ : ℝ) (hf : ∀ i ∈ l, ‖f i‖ ≤ δ) :
    ‖(l.map (fun i => c i • f i)).sum‖ ≤ (l.map (fun i => |c i|)).sum * δ := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons,List.sum_cons,add_mul]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hf i (List.mem_cons_self ..)) (abs_nonneg _)
    · exact ih (fun j hj => hf j (List.mem_cons_of_mem _ hj))

section ThreeFactors
variable {A : Type*} [CStarAlgebra A]

end ThreeFactors

section Conjugation
variable {A : Type*} [CStarAlgebra A]

lemma conjugate_comp (U V B : A) : conjugate (U*V) B = conjugate U (conjugate V B) := by
  simp only [conjugate,star_mul,mul_assoc]

lemma conjugate_mul {U : A} (hU : U ∈ unitary A) (B C : A) :
    conjugate U (B*C) = conjugate U B * conjugate U C := by
  simp only [conjugate,mul_assoc,← mul_assoc (star U) U,Unitary.star_mul_self_of_mem hU,one_mul]

lemma conjugate_smul (U B : A) (r : ℝ) : conjugate U (r • B) = r • conjugate U B := by
  simp only [conjugate,mul_smul_comm,smul_mul_assoc]

lemma conjugate_list_sum {ι : Type*} (U : A) (l : List ι) (f : ι → A) :
    conjugate U (l.map f).sum = (l.map (fun i => conjugate U (f i))).sum := by
  simp only [conjugate,← List.sum_map_mul_left,← List.sum_map_mul_right]

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

lemma reflect_unitary {N : ℕ} (D : Count N) : reflect D ∈ unitary (Operator N) := by
  simpa only [reflect,two_smul] using reflection_unitary D

lemma reflect_disjoint_commute {N : ℕ} (A B : Count N) (h : Disjoint A.support B.support) :
    Commute (reflect A) (reflect B) := by
  exact (Commute.one_left _).sub_left
    (((Commute.one_right _).sub_right ((A.disjoint_commute B h).smul_right (2:ℝ))).smul_left (2:ℝ))

lemma reflect_disjoint_zero_commute {N : ℕ} (A B : Count N) (h : Disjoint A.support B.support) :
    Commute (reflect A) B.zero :=
  (Commute.one_left _).sub_left ((A.disjoint_commute B h).smul_left (2:ℝ))

lemma ReflectionLayer.active_length {N : ℕ} (R : ReflectionLayer N) (A : Count N) :
    (R.active A).gates.length ≤ A.support.card := by
  apply list_disjoint_hits_length Count.support _ (R.active A).disjoint
  intro D hD
  have h := (List.mem_filter.mp hD).2
  simp only [decide_eq_true_eq] at h
  exact Finset.not_disjoint_iff_nonempty_inter.mp h

lemma ReflectionLayer.active_conjugate {N : ℕ} (R : ReflectionLayer N) (A : Count N) :
    conjugate (reflectionMatrix R) A.zero = conjugate (reflectionMatrix (R.active A)) A.zero := by
  rw [reflectionMatrix_eq,reflectionMatrix_eq]
  apply list_conjugate_filter
  · exact R.disjoint.imp (fun h => reflect_disjoint_commute _ _ h)
  · intro D _; exact reflect_unitary D
  · intro D _ hD
    apply reflect_disjoint_zero_commute
    simpa using hD

lemma reflectionTerms_weight {N : ℕ} (l : List (Count N)) :
    ((reflectionTerms l).map (fun p => |p.1|)).sum = (3:ℝ)^l.length := by
  induction l with
  | nil => simp [reflectionTerms]
  | cons A l ih =>
    simp only [reflectionTerms,List.map_append,List.sum_append,List.map_map,List.length_cons,pow_succ]
    change ((reflectionTerms l).map (fun p => |p.1|)).sum +
      ((reflectionTerms l).map (fun p => |(-2:ℝ)*p.1|)).sum = _
    simp_rw [abs_mul]
    norm_num only [abs_neg]
    rw [List.sum_map_mul_left,ih]
    ring

lemma star_list_sum {A ι : Type*} [AddMonoid A] [StarAddMonoid A] (l : List ι) (f : ι → A) :
    star (l.map f).sum = (l.map (fun i => star (f i))).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

lemma reflectList_selfAdjoint {N : ℕ} (l : List (Count N))
    (hl : l.Pairwise (fun A B => Disjoint A.support B.support)) :
    star (reflectList l) = reflectList l := by
  rw [← reflectionTerms_sum l hl,star_list_sum]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [star_smul,star_trivial,p.2.zero_projection.isSelfAdjoint.star_eq]

section BilinearBudget
variable {A : Type*} [CStarAlgebra A]

lemma list_sum_sandwich {ι : Type*} (l : List ι) (c : ι → ℝ) (f : ι → A) (L R : A) :
    L * (l.map (fun i => c i • f i)).sum * R =
      (l.map (fun i => c i • (L*f i*R))).sum := by
  simp only [← List.sum_map_mul_left,← List.sum_map_mul_right,mul_smul_comm,smul_mul_assoc]

lemma bilinear_list_bound {ι : Type*} (l : List ι) (c : ι → ℝ) (f : ι → A)
    (H B P : A) (δ : ℝ)
    (h : ∀ i ∈ l, ∀ j ∈ l, ‖H*f i*B*f j*P‖ ≤ δ) :
    ‖H * (l.map (fun i => c i • f i)).sum * B *
      (l.map (fun i => c i • f i)).sum * P‖ ≤ (l.map (fun i => |c i|)).sum^2 * δ := by
  let T := (l.map (fun i => c i • f i)).sum
  let C := (l.map (fun i => |c i|)).sum
  have hj : ∀ i ∈ l, ‖H*f i*B*T*P‖ ≤ C*δ := by
    intro i hi
    rw [show H*f i*B*T*P = (H*f i*B)*T*P by rfl, list_sum_sandwich]
    exact norm_list_smul_sum l c _ δ (h i hi)
  have heq : H*T*B*T*P = (l.map (fun i => c i • (H*f i*B*T*P))).sum := by
    calc
      _ = H*T*(B*T*P) := by simp only [mul_assoc]
      _ = _ := by rw [list_sum_sandwich]; simp only [mul_assoc]
  change ‖H*T*B*T*P‖ ≤ C^2*δ
  rw [heq]
  exact (norm_list_smul_sum l c _ (C*δ) hj).trans_eq (by ring)
end BilinearBudget

lemma reflection_conjugate_expansion {N : ℕ} (l : List (Count N))
    (hl : l.Pairwise (fun A B => Disjoint A.support B.support)) (V : Operator N) :
    conjugate V (reflectList l) =
      ((reflectionTerms l).map (fun p => p.1 • conjugate V p.2.zero)).sum := by
  rw [← reflectionTerms_sum l hl,conjugate_list_sum]
  simp only [conjugate_smul]

lemma reflection_transition_bound {N : ℕ} (R : ReflectionLayer N) (V H P : Operator N)
    (A : Count N) (hV : V ∈ unitary (Operator N)) (δ : ℝ)
    (h : ∀ X Y : Count N, ‖H*conjugate V X.zero*conjugate V A.zero*conjugate V Y.zero*P‖ ≤ δ) :
    ‖H*conjugate V (conjugate (reflectionMatrix R) A.zero)*P‖ ≤ (9:ℝ)^R.gates.length*δ := by
  rw [reflectionMatrix_eq]
  unfold conjugate at *
  have heq : H*(V*(reflectList R.gates*A.zero*star (reflectList R.gates))*star V)*P =
      H*conjugate V (reflectList R.gates)*conjugate V A.zero*conjugate V (reflectList R.gates)*P := by
    change H*conjugate V (reflectList R.gates*A.zero*star (reflectList R.gates))*P = _
    rw [reflectList_selfAdjoint _ R.disjoint,conjugate_mul hV,conjugate_mul hV]
    simp only [mul_assoc]
  rw [heq,reflection_conjugate_expansion _ R.disjoint V]
  apply (bilinear_list_bound (reflectionTerms R.gates) Prod.fst
    (fun p => conjugate V p.2.zero) H (conjugate V A.zero) P δ (fun i _ j _ => h i.2 j.2)).trans_eq
  rw [reflectionTerms_weight]
  congr 1
  rw [pow_two,← mul_pow]
  norm_num

lemma small_support_layer_bound {N : ℕ} (V : Operator N) (hV : V ∈ unitary (Operator N))
    (R : ReflectionLayer N) (L : LocalLayer N) (M A : Count N) {r r₁ r₂ δ : ℝ} (hδ : 0 ≤ δ)
    (h₁ : ∀ D : Count N, ‖M.high r₁*conjugate V D.zero*M.zero‖ ≤ δ)
    (h₂ : ∀ D : Count N, ‖M.high r₂*conjugate V D.zero*M.low r₁‖ ≤ δ)
    (h₃ : ∀ D : Count N, ‖M.high r*conjugate V D.zero*M.low r₂‖ ≤ δ) :
    ‖M.high r*conjugate (V*reflectionMatrix R*localMatrix L) A.zero*M.zero‖ ≤
      (9:ℝ)^A.support.card*(3*δ) := by
  have hc : ∀ D : Count N, ‖conjugate V D.zero‖ ≤ 1 := fun D =>
    IsStarProjection.norm_le _ (conjugate_projection hV D.zero_projection)
  have htriple : ∀ X Y Z : Count N,
      ‖M.high r*conjugate V X.zero*conjugate V Y.zero*conjugate V Z.zero*M.zero‖ ≤ 3*δ := by
    intro X Y Z
    exact three_factor_transition _ _ (M.high r₁) (M.high r₂) _ _ _
      (IsStarProjection.norm_le _ (M.high_projection r)) (IsStarProjection.norm_le _ M.zero_projection)
      (IsStarProjection.norm_le _ (M.low_projection r₁)) (hc X) (hc Y) (hc Z) (h₁ Z) (h₂ Y) (h₃ X)
  have hbound := reflection_transition_bound (R.active (A.rotate L)) V (M.high r) M.zero
    (A.rotate L) hV (3*δ) (fun X Y => htriple X (A.rotate L) Y)
  have hlen : (R.active (A.rotate L)).gates.length ≤ A.support.card := R.active_length (A.rotate L)
  calc
    _ = ‖M.high r*conjugate V (conjugate (reflectionMatrix (R.active (A.rotate L))) (A.rotate L).zero)*M.zero‖ := by
      rw [conjugate_comp,conjugate_comp,
        show conjugate (localMatrix L) A.zero = (A.rotate L).zero from (A.rotate_zero L).symm,
        R.active_conjugate]
    _ ≤ (9:ℝ)^(R.active (A.rotate L)).gates.length*(3*δ) := hbound
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hlen) (by positivity)

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

theorem solution {N : ℕ} (V : Operator N) (hV : V ∈ unitary (Operator N))
    (R : ReflectionLayer N) (L : LocalLayer N) (M A : Count N) {r r₁ r₂ δ : ℝ} (hδ : 0 ≤ δ)
    (h₁ : ∀ D : Count N, ‖M.high r₁*conjugate V D.zero*M.zero‖ ≤ δ)
    (h₂ : ∀ D : Count N, ‖M.high r₂*conjugate V D.zero*M.low r₁‖ ≤ δ)
    (h₃ : ∀ D : Count N, ‖M.high r*conjugate V D.zero*M.low r₂‖ ≤ δ) :
    ‖M.high r*conjugate (V*reflectionMatrix R*localMatrix L) A.zero*M.zero‖ ≤
      (9:ℝ)^A.support.card*(3*δ) := by
  first
    | exact OAI.QAC.small_support_layer_bound V hV R L M A hδ h₁ h₂ h₃
    | exact OAI.QAC.small_support_layer_bound
    | (apply OAI.QAC.small_support_layer_bound <;> assumption)
    | (intros; apply OAI.QAC.small_support_layer_bound <;> assumption)
