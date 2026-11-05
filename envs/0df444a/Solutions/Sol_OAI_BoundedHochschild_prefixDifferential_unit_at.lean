-- Prove2me | solution 1 for OAI.BoundedHochschild.prefixDifferential_unit_at
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:44:36.421046+00:00
-- url     : https://prove2.me/submissions/547312a5-18e3-4652-be28-b8cc468b3c18

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

set_option Elab.async false
set_option linter.all false

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
open Filter Topology
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

end BoundedHochschild

namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

end BoundedHochschild

namespace BoundedHochschild
variable {M : Type*}

def tupleInsert {n : ℕ} (p : Fin (n+1)) (a : M) (v : Fin n → M) (i : Fin (n+1)) : M :=
  if h : i.val < p.val then v ⟨i.val, by omega⟩
  else if h : i = p then a else v ⟨i.val-1, by have := i.isLt; have := p.isLt; omega⟩

lemma tupleInsert_eq {n : ℕ} (p : Fin (n+1)) (a : M) (v : Fin n → M) :
    tupleInsert p a v = p.insertNth a v := by
  apply (Fin.eq_insertNth_iff).mpr
  constructor
  · simp [tupleInsert]
  · funext i
    change tupleInsert p a v (p.succAbove i) = v i
    by_cases h : i.castSucc < p
    · rw [Fin.succAbove_of_castSucc_lt _ _ h]
      dsimp [tupleInsert]
      rw [dite_eq_left (show i.val < p.val from h)]
    · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt h)]
      dsimp [tupleInsert]
      rw [dite_eq_right (by change ¬i.val < p.val at h; omega),
        ite_eq_right (by intro he; have hv := congrArg Fin.val he; dsimp at hv; change ¬i.val < p.val at h; omega)]

lemma tupleInsert_lt {n : ℕ} (p : Fin (n+1)) (a : M) (v : Fin n → M)
    (i : Fin (n+1)) (h : i.val < p.val) :
    Fin.insertNth (α := fun _ => M) p a v i = v ⟨i.val, by omega⟩ := by
  rw [← tupleInsert_eq]
  simp only [tupleInsert, dite_eq_left h]

lemma tupleInsert_gt {n : ℕ} (p : Fin (n+1)) (a : M) (v : Fin n → M)
    (i : Fin (n+1)) (h : p.val < i.val) :
    Fin.insertNth (α := fun _ => M) p a v i = v ⟨i.val-1, by have := i.isLt; omega⟩ := by
  rw [← tupleInsert_eq]
  simp only [tupleInsert, dite_eq_right (by omega : ¬i.val < p.val),
    dite_eq_right (by intro he; have := congrArg Fin.val he; omega : i ≠ p)]

lemma merge_insert_same [Mul M] {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1)) (q : M)
    (hq : q*v r=v r) : mergeInputs (r.castSucc.insertNth q v) r = v := by
  funext i
  simp only [mergeInputs]
  split_ifs with h h
  · rw [tupleInsert_lt _ _ _ _ (by simpa only [Fin.val_castSucc, Fin.lt_def] using h)]
    rfl
  · subst i
    rw [Fin.insertNth_apply_same, tupleInsert_gt _ _ _ _ (by simp)]
    simpa using hq
  · rw [tupleInsert_gt _ _ _ _ (by simpa only [Fin.val_castSucc,Fin.val_succ] using
        (show r.val < i.val+1 by omega))]
    rfl

lemma merge_insert_before [Mul M] {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1))
    (q : M) (j : Fin n) (hjr : j.val+1 < r.val) :
    mergeInputs (r.castSucc.insertNth q v) (r.succAbove j) =
      (⟨r.val-1, by omega⟩ : Fin (n+1)).insertNth q (mergeInputs v j) := by
  have hs : r.succAbove j=j.castSucc := by
    exact Fin.succAbove_of_castSucc_lt _ _ (by simpa only [Fin.lt_def, Fin.val_castSucc] using (show j.val < r.val by omega))
  rw [hs]
  funext i
  simp only [mergeInputs, ← tupleInsert_eq, tupleInsert, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ, Fin.ext_iff]
  split_ifs <;> try omega
  all_goals first | rfl | congr 1
  all_goals exact Fin.ext (by dsimp; omega)

lemma merge_insert_after [Mul M] {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1))
    (q : M) (j : Fin n) (hjr : r.val ≤ j.val) :
    mergeInputs (r.castSucc.insertNth q v) (r.succAbove j) =
      (⟨r.val, by omega⟩ : Fin (n+1)).insertNth q (mergeInputs v j) := by
  have hs : r.succAbove j=j.succ := by
    exact Fin.succAbove_of_le_castSucc _ _ (by simpa only [Fin.le_def, Fin.val_castSucc] using hjr)
  rw [hs]
  funext i
  simp only [mergeInputs, ← tupleInsert_eq, tupleInsert, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ, Fin.ext_iff]
  split_ifs <;> try omega
  all_goals first | rfl | congr 1
  all_goals first | rfl | (apply Fin.ext; dsimp; omega) |
    (apply congrArg v; apply Fin.ext; dsimp; omega)

lemma tail_insert {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1)) (q : M)
    (hr : 0 < r.val) :
    (fun i : Fin (n+1) => (r.castSucc.insertNth (α := fun _ => M) q v) i.succ) =
    (⟨r.val-1, by omega⟩ : Fin (n+1)).insertNth (α := fun _ => M) q (fun i => v i.succ) := by
  funext i
  simp only [← tupleInsert_eq, tupleInsert, Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]
  split_ifs <;> try omega
  all_goals first | rfl | congr 1
  all_goals exact Fin.ext (by dsimp; omega)
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma merge_insert_prev {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1))
    (j : Fin n) (hjr : j.val+1=r.val) (a : M) :
    mergeInputs (r.castSucc.insertNth a v) (r.succAbove j)=
      Function.update v j.castSucc (v j.castSucc*a) := by
  have hs : r.succAbove j=j.castSucc :=
    Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def,Fin.val_castSucc]; omega)
  rw [hs]
  ext i
  by_cases hij : i<j.castSucc
  · simp only [mergeInputs,ite_eq_left hij,Function.update_of_ne (ne_of_lt hij)]
    exact tupleInsert_lt _ _ _ _ (by simp only [Fin.val_castSucc,Fin.lt_def] at *; omega)
  · by_cases he : i=j.castSucc
    · subst i
      simp only [mergeInputs,lt_self_iff_false,ite_false,ite_true,Function.update_self]
      rw [tupleInsert_lt _ _ _ _ (by simp only [Fin.val_castSucc]; omega)]
      have hi : j.castSucc.succ=r.castSucc := Fin.ext hjr
      rw [hi,Fin.insertNth_apply_same]
      rfl
    · simp only [mergeInputs,ite_eq_right hij,ite_eq_right he,Function.update_of_ne he]
      rw [tupleInsert_gt _ _ _ _ (by
        simp only [Fin.val_castSucc,Fin.val_succ,Fin.lt_def,Fin.ext_iff] at *
        omega)]
      rfl

end BoundedHochschild

namespace BoundedHochschild
open HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma prefix_middle_unit_other {n : ℕ} (h : Cochain M (n+1)) (r : ℕ)
    (hU : UnitZeroBefore h r) (i : Fin (n+1)) (hi : i.val≤r)
    (v : Fin (n+1) → M) (j : Fin n) :
    (if (i.succAbove j).val<r then ((-1:ℂ)^((i.succAbove j).val+1)) •
      h (mergeInputs (i.castSucc.insertNth 1 v) (i.succAbove j)) else 0)=
    if j.val+1=i.val then ((-1:ℂ)^i.val) • h v else 0 := by
  rcases lt_trichotomy (j.val+1) i.val with hij|hij|hij
  · have hz : h (mergeInputs (i.castSucc.insertNth (1:M) v) (i.succAbove j))=0 := by
      rw [merge_insert_before v i 1 j hij]
      exact hU _ (by dsimp; omega) _
    rw [hz]
    simp only [smul_zero,ite_self,show ¬j.val+1=i.val by omega,ite_false]
  · have hs : i.succAbove j=j.castSucc :=
      Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def,Fin.val_castSucc]; omega)
    have hjr : (i.succAbove j).val<r := by rw [hs]; simp only [Fin.val_castSucc]; omega
    rw [ite_eq_left hjr,merge_insert_prev v i j hij 1,hs]
    simp only [Fin.val_castSucc,hij,ite_true,mul_one,Function.update_eq_self]
  · have hle : i.val≤j.val := by omega
    rw [ite_eq_right (by omega : ¬j.val+1=i.val)]
    split_ifs with hjr
    · rw [merge_insert_after v i 1 j hle]
      have hs : i.succAbove j=j.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simpa only [Fin.le_def,Fin.val_castSucc] using hle)
      rw [hs] at hjr
      rw [hU _ (by simp only [Fin.val_succ] at hjr; dsimp; omega) _,smul_zero]
    · rfl

lemma prefixDifferential_unit {n : ℕ} (h : Cochain M (n+1)) (r : ℕ)
    (hU : UnitZeroBefore h r) (i : Fin (n+1)) (hi : i.val≤r) (v : Fin (n+1) → M) :
    prefixDifferential h r (i.castSucc.insertNth 1 v)=
      ((-1:ℂ)^i.val) • h v +
      if i.val<r then ((-1:ℂ)^(i.val+1)) • h v else 0 := by
  rw [prefixDifferential_apply,Fin.sum_univ_succAbove _ i]
  have hs : mergeInputs (i.castSucc.insertNth (1:M) v) i=v :=
    merge_insert_same v i 1 (by simp)
  rw [hs]
  simp_rw [prefix_middle_unit_other h r hU i hi v]
  by_cases hz : i.val=0
  · have hie : i=0 := Fin.ext hz
    subst i
    simp only [Fin.val_zero,Fin.castSucc_zero,Fin.insertNth_zero',Fin.cons_zero,
      Fin.cons_succ,one_mul,pow_zero,one_smul]
    have hj (j : Fin n) : ¬j.val+1=0 := by omega
    simp only [hj,ite_false,Finset.sum_const_zero,add_zero]
  · have hip : 0 < i.val := by omega
    have hl : (i.castSucc.insertNth (α := fun _ => M) 1 v) 0*
        h (fun j => (i.castSucc.insertNth (α := fun _ => M) 1 v) j.succ)=0 := by
      rw [tail_insert v i 1 hip,hU _ (by dsimp; omega),mul_zero]
    rw [hl,zero_add]
    let b : Fin n := ⟨i.val-1,by omega⟩
    have hj (j : Fin n) : (j.val+1=i.val) ↔ j=b := by
      simp only [Fin.ext_iff,b]
      omega
    simp only [hj,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    abel

lemma prefixDifferential_unit_at {n : ℕ} (h : Cochain M (n+1)) (r : Fin (n+1))
    (hU : UnitZeroBefore h r.val) (v : Fin (n+1) → M) :
    prefixDifferential h r.val (r.castSucc.insertNth 1 v)=((-1:ℂ)^r.val) • h v := by
  rw [prefixDifferential_unit h r.val hU r (by rfl) v,ite_eq_right (lt_irrefl _),add_zero]
end BoundedHochschild
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.prefixDifferential_unit_at.{u} := @OAI.BoundedHochschild.prefixDifferential_unit_at.{u}
