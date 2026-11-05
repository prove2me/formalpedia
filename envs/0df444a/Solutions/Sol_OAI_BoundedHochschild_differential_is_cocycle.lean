-- Prove2me | solution 1 for OAI.BoundedHochschild.differential_is_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:05:07.475114+00:00
-- url     : https://prove2.me/submissions/eca3e7d7-0ed4-41bf-b456-66222647eca3

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section

namespace BoundedHochschild

section AlgebraicAveraging
variable {M : Type*} [NormedRing M] [NormedAlgebra ℂ M]

@[simp] theorem differentialValue_add {n : ℕ} (f g : Cochain M n)
    (v : Fin (n + 1) → M) :
    differentialValue (f + g) v = differentialValue f v + differentialValue g v := by
  simp only [differentialValue, add_apply, mul_add, add_mul,
    smul_add, Finset.sum_add_distrib]
  abel

@[simp] theorem differentialValue_smul {n : ℕ} (c : ℂ) (f : Cochain M n)
    (v : Fin (n + 1) → M) :
    differentialValue (c • f) v = c • differentialValue f v := by
  simp only [differentialValue, smul_apply, smul_mul_assoc,
    mul_smul_comm, smul_add, Finset.smul_sum, smul_smul]
  congr 2
  · apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm c]
  · rw [mul_comm c]

end AlgebraicAveraging

section TupleIdentities
variable {M : Type*}

@[simp] theorem mergeInputs_snoc_castSucc [Mul M] {n : ℕ} (v : Fin (n + 1) → M)
    (u : M) (j : Fin n) :
    mergeInputs (Fin.snoc v u) j.castSucc = Fin.snoc (mergeInputs v j) u := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · have hlt : ¬ Fin.last n < j.castSucc := by
      simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc]
      omega
    have heq : Fin.last n ≠ j.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      omega
    simp [mergeInputs, hlt, heq]
  · simp [mergeInputs, ← Fin.castSucc_succ]

@[simp] theorem mergeInputs_snoc_last [Mul M] {n : ℕ} (v : Fin (n + 1) → M) (u : M) :
    mergeInputs (Fin.snoc v u) (Fin.last n) =
      Fin.snoc (fun i : Fin n => v i.castSucc) (v (Fin.last n) * u) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [mergeInputs]
  · simp [mergeInputs]
end TupleIdentities
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
namespace BoundedHochschild

lemma mergeInputs_mergeInputs {M : Type*} [Semigroup M] {n : ℕ}
    (v : Fin (n+3) → M) (i : Fin (n+1)) (j : Fin (n+2)) (hj : j.val ≤ i.val) :
    mergeInputs (mergeInputs v j) i =
      mergeInputs (mergeInputs v i.succ) (Fin.castLT j (by omega)) := by
  funext k
  simp only [mergeInputs, Fin.lt_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ,
    Fin.val_castLT]
  split_ifs <;> try simp_all only <;> try omega
  all_goals try contradiction
  all_goals try rfl
  all_goals try simp only [mul_assoc]
  all_goals congr 1 <;> apply Fin.ext <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

variable {M : Type*} [CStarAlgebra M]

def barDifferential {n : ℕ} (F : (Fin (n+1) → M) → M) : (Fin (n+2) → M) → M :=
  fun v => ∑ j : Fin (n+1), ((-1:ℂ)^j.val) • F (mergeInputs v j)

lemma barDifferential_squared {n : ℕ} (F : (Fin (n+1) → M) → M)
    (v : Fin (n+3) → M) : barDifferential (barDifferential F) v=0 := by
  classical
  simp only [barDifferential, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm,← Finset.sum_product',Finset.univ_product_univ]
  let P := Fin (n+1) × Fin (n+2)
  let S : Finset P := {ij : P | ij.2.val ≤ ij.1.val}
  rw [← Finset.sum_add_sum_compl S,← eq_neg_iff_add_eq_zero,← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right ij.1.isLt),ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S,φ,Finset.compl_filter,Finset.mem_filter_univ,Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i,j⟩ hij ⟨i',j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using congrArg Prod.snd h,
      by simpa [φ,Fin.castSucc_castLT] using congrArg Fin.castSucc (congrArg Prod.fst h)⟩
  · rintro ⟨i',j'⟩ hij'
    simp_rw [S,Finset.compl_filter,Finset.mem_filter_univ,not_le] at hij'
    refine ⟨(j'.pred (by intro h; simp [h] at hij'),i'.castSucc),?_,?_⟩
    · simpa [S] using Nat.le_sub_one_of_lt hij'
    · simp only [φ,Fin.castLT_castSucc,Fin.succ_pred]
  · rintro ⟨i,j⟩ hij
    dsimp only [φ]
    rw [← neg_smul]
    have hji : j.val ≤ i.val := (Finset.mem_filter.mp hij).2
    rw [mergeInputs_mergeInputs v i j hji]
    congr 1
    simp only [Fin.val_succ,Fin.val_castLT,pow_succ,mul_neg,mul_one]
    ring

end BoundedHochschild

open scoped BigOperators
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

lemma mergeInputs_cons_zero {n : ℕ} (v : Fin (n+1) → M) (a : M) :
    mergeInputs (Fin.cons a v) 0=Fin.cons (a*v 0) (fun i : Fin n => v i.succ) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [mergeInputs]
  · simp [mergeInputs,Fin.succ_ne_zero]

lemma mergeInputs_cons_succ {n : ℕ} (v : Fin (n+1) → M) (a : M) (j : Fin n) :
    mergeInputs (Fin.cons a v) j.succ=Fin.cons a (mergeInputs v j) := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [mergeInputs]
  · simp [mergeInputs,Fin.castSucc_succ]

def barEnvelope {n : ℕ} (f : Cochain M n) : (Fin (n+2) → M) → M :=
  fun v => v 0*f (fun i => v i.succ.castSucc)*v (Fin.last (n+1))

lemma barEnvelope_apply {n : ℕ} (f : Cochain M n) (a b : M) (v : Fin n → M) :
    barEnvelope f (Fin.snoc (Fin.cons a v) b)=a*f v*b := by
  simp only [barEnvelope,Fin.snoc_last]
  have h0 : (Fin.snoc (Fin.cons a v) b : Fin (n+2) → M) 0=a := by
    change (Fin.snoc (Fin.cons a v) b : Fin (n+2) → M) (0 : Fin (n+1)).castSucc=a
    simp
  have hv : (fun i : Fin n => (Fin.snoc (Fin.cons a v) b : Fin (n+2) → M) i.succ.castSucc)=v := by
    ext i; simp only [Fin.snoc_castSucc,Fin.cons_succ]
  rw [h0,hv]

lemma barDifferential_envelope_apply {n : ℕ} (f : Cochain M n) (a b : M)
    (v : Fin (n+1) → M) :
    barDifferential (barEnvelope f) (Fin.snoc (Fin.cons a v) b)=
      a*differentialValue f v*b := by
  rw [barDifferential,Fin.sum_univ_castSucc]
  simp only [mergeInputs_snoc_castSucc,Fin.val_castSucc]
  rw [Fin.sum_univ_succ]
  simp only [mergeInputs_cons_zero,mergeInputs_cons_succ,barEnvelope_apply,
    Fin.val_zero,pow_zero,one_smul,Fin.val_succ,mergeInputs_snoc_last,Fin.val_last]
  have hi : (fun i : Fin (n+1) => (Fin.cons a v : Fin (n+2) → M) i.castSucc)=Fin.cons a (fun i : Fin n => v i.castSucc) := by
    ext i; refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.castSucc_succ,Fin.cons_succ]
  have hl : (Fin.cons a v : Fin (n+2) → M) (Fin.last (n+1))=v (Fin.last n) := by
    change (Fin.cons a v : Fin (n+2) → M) (Fin.last n).succ=_
    simp
  rw [hi,hl,barEnvelope_apply]
  simp only [differentialValue,mul_add,add_mul,Finset.mul_sum,Finset.sum_mul,
    mul_smul_comm,smul_mul_assoc,mul_assoc]
  try abel

lemma barDifferential_envelope {n : ℕ} (f : Cochain M n) :
    barDifferential (barEnvelope f)=barEnvelope (differential f) := by
  ext v
  have hv : v=Fin.snoc (Fin.cons (v 0) (fun i : Fin (n+1) => v i.succ.castSucc)) (v (Fin.last (n+2))) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · simp only [Fin.snoc_castSucc,Fin.cons_succ]
  rw [hv,barDifferential_envelope_apply,barEnvelope_apply,differential_apply]

theorem differential_squared {n : ℕ} (f : Cochain M n) :
    differential (differential f)=0 := by
  ext v
  have h := barDifferential_squared (barEnvelope f) (Fin.snoc (Fin.cons (1:M) v) 1)
  rw [barDifferential_envelope,barDifferential_envelope,barEnvelope_apply,one_mul,mul_one] at h
  exact h

lemma differential_is_cocycle {n : ℕ} (f : Cochain M n) (v : Fin (n+2) → M) :
    differentialValue (differential f) v=0 := by
  rw [← differential_apply,differential_squared]
  rfl
end BoundedHochschild
end
end OAI
end

theorem solution.{u_1} : type_of% @OAI.BoundedHochschild.differential_is_cocycle.{u_1} := @OAI.BoundedHochschild.differential_is_cocycle.{u_1}
