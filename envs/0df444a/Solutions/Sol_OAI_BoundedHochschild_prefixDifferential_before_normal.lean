-- Prove2me | solution 1 for OAI.BoundedHochschild.prefixDifferential_before_normal
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:08:00.735891+00:00
-- url     : https://prove2.me/submissions/d8065c82-123e-4eb9-8eb6-16da96b658b2

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

open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end HochschildNormalPart

namespace HochschildNormalPart
open BoundedHochschild
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

omit [CompleteSpace X] in
lemma hasPreadjoint_iff_scalar (T : M →L[ℂ] M) :
    HasPreadjoint e T ↔ ∀ z, (predualEmbedding e z).comp T ∈ normalDual e := by
  constructor
  · intro h z
    exact normalDual_comp e ⟨z,rfl⟩ T h
  · intro h z
    obtain ⟨w,hw⟩ := (mem_normalDual e _).mp (h z)
    exact ⟨w,fun a => star_injective (hw a)⟩
end HochschildNormalPart
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

end BoundedHochschild

namespace BoundedHochschild
open HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

omit [CompleteSpace X] in
lemma HasPreadjoint.add {S T : M →L[ℂ] M}
    (hS : HasPreadjoint e S) (hT : HasPreadjoint e T) : HasPreadjoint e (S+T) := by
  intro z
  obtain ⟨w,hw⟩ := hS z
  obtain ⟨y,hy⟩ := hT z
  refine ⟨w+y,fun a => ?_⟩
  simp only [add_apply,map_add,hw,hy]

omit [CompleteSpace X] in
lemma HasPreadjoint.comp {S T : M →L[ℂ] M}
    (hS : HasPreadjoint e S) (hT : HasPreadjoint e T) : HasPreadjoint e (S.comp T) := by
  intro z
  obtain ⟨w,hw⟩ := hS z
  obtain ⟨y,hy⟩ := hT w
  exact ⟨y,fun a => (hw (T a)).trans (hy a)⟩
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

lemma merge_insert_product {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1)) (a : M) :
    mergeInputs (r.castSucc.insertNth a v) r=Function.update v r (a*v r) := by
  ext i
  by_cases hir : i < r
  · simp only [mergeInputs,ite_eq_left hir,Function.update_of_ne (ne_of_lt hir)]
    rw [tupleInsert_lt _ _ _ _ (by simpa only [Fin.val_castSucc,Fin.lt_def] using hir)]
    rfl
  · by_cases he : i=r
    · subst i
      simp only [mergeInputs,lt_self_iff_false,ite_false,ite_true,Function.update_self,
        Fin.insertNth_apply_same]
      rw [tupleInsert_gt _ _ _ _ (by simp)]
      rfl
    · simp only [mergeInputs,ite_eq_right hir,ite_eq_right he,Function.update_of_ne he]
      rw [tupleInsert_gt _ _ _ _ (by simp only [Fin.val_castSucc,Fin.val_succ]; omega)]
      rfl

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

lemma sliceAt_add {n : ℕ} (f g : Cochain M (n+1)) (i : Fin (n+1)) (v : Fin n → M) :
    sliceAt (f+g) i v=sliceAt f i v+sliceAt g i v := by ext a; simp

lemma sliceAt_smul {n : ℕ} (c : ℂ) (f : Cochain M (n+1)) (i : Fin (n+1)) (v : Fin n → M) :
    sliceAt (c • f) i v=c • sliceAt f i v := by ext a; simp

lemma sliceAt_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Cochain M (n+1))
    (i : Fin (n+1)) (v : Fin n → M) :
    sliceAt (∑ j ∈ s,f j) i v=∑ j ∈ s,sliceAt (f j) i v := by ext a; simp

lemma sliceAt_zero {n : ℕ} (i : Fin (n+1)) (v : Fin n → M) :
    sliceAt (0 : Cochain M (n+1)) i v=0 := by ext a; simp

lemma sliceAt_left {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1)) (hr : 0<r.val)
    (v : Fin (n+1) → M) :
    sliceAt (leftCoboundary f) r.castSucc v=
      (ContinuousLinearMap.mul ℂ M (v 0)).comp
        (sliceAt f ⟨r.val-1,by omega⟩ (fun i => v i.succ)) := by
  ext a
  simp only [sliceAt_apply,leftCoboundary_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply']
  rw [tupleInsert_lt _ _ _ _ hr,tail_insert v r a hr]
  rfl

lemma sliceAt_middle_same {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (v : Fin (n+1) → M) :
    sliceAt (middleCoboundary f r) r.castSucc v=
      (sliceAt f r (r.removeNth v)).comp ((ContinuousLinearMap.mul ℂ M).flip (v r)) := by
  ext a
  simp only [sliceAt_apply,middleCoboundary_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.mul_apply',merge_insert_product,
    Fin.insertNth_removeNth]

lemma sliceAt_middle_before {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (j : Fin n) (hjr : j.val+1<r.val) (v : Fin (n+1) → M) :
    sliceAt (middleCoboundary f (r.succAbove j)) r.castSucc v=
      sliceAt f ⟨r.val-1,by omega⟩ (mergeInputs v j) := by
  ext a
  simp only [sliceAt_apply,middleCoboundary_apply,merge_insert_before v r _ j hjr]

lemma sliceAt_middle_after {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (j : Fin n) (hjr : r.val≤j.val) (v : Fin (n+1) → M) :
    sliceAt (middleCoboundary f (r.succAbove j)) r.castSucc v=
      sliceAt f r (mergeInputs v j) := by
  ext a
  simp only [sliceAt_apply,middleCoboundary_apply,merge_insert_after v r _ j hjr]

lemma sliceAt_middle_before_boundary {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (j : Fin n) (hjr : j.val+1=r.val) (v : Fin (n+1) → M) :
    sliceAt (middleCoboundary f (r.succAbove j)) r.castSucc v=
      (sliceAt f j.castSucc (j.castSucc.removeNth v)).comp
        (ContinuousLinearMap.mul ℂ M (v j.castSucc)) := by
  ext a
  simp only [sliceAt_apply,middleCoboundary_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply',merge_insert_prev v r j hjr,Fin.insertNth_removeNth]

end BoundedHochschild

namespace BoundedHochschild
open HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

omit [CompleteSpace X] in
lemma HasPreadjoint.smul {T : M →L[ℂ] M} (hT : HasPreadjoint e T) (c : ℂ) :
    HasPreadjoint e (c • T) := by
  rw [hasPreadjoint_iff_scalar] at hT ⊢
  intro z
  simpa only [ContinuousLinearMap.comp_smul] using (normalDual e).smul_mem c (hT z)

omit [CompleteSpace X] in
lemma HasPreadjoint.zero : HasPreadjoint e (0 : M →L[ℂ] M) := by
  rw [hasPreadjoint_iff_scalar]
  intro z
  simpa only [ContinuousLinearMap.comp_zero] using (normalDual e).zero_mem

omit [CompleteSpace X] in
lemma HasPreadjoint.sum {ι : Type*} (s : Finset ι) (T : ι → M →L[ℂ] M)
    (hT : ∀ j ∈ s,HasPreadjoint e (T j)) : HasPreadjoint e (∑ j ∈ s,T j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using HasPreadjoint.zero e
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hT a (Finset.mem_insert_self _ _)).add e
      (ih (fun j hj => hT j (Finset.mem_insert_of_mem hj)))

lemma leftCoboundary_before_normal {n : ℕ} (h : Cochain M (n+1)) (r : ℕ)
    (hN : NormalBefore e h r) (i : Fin (n+1)) (hi : i.val≤r) (v : Fin (n+1) → M) :
    HasPreadjoint e (sliceAt (leftCoboundary h) i.castSucc v) := by
  by_cases hzero : i.val=0
  · have hie : i=0 := Fin.ext hzero
    subst i
    have hs : sliceAt (leftCoboundary h) (0:Fin (n+2)) v=
        (ContinuousLinearMap.mul ℂ M).flip (h v) := by
      ext a
      simp only [sliceAt_apply,leftCoboundary_apply,ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.mul_apply',Fin.insertNth_zero',Fin.cons_zero,Fin.cons_succ]
    rw [show (0:Fin (n+1)).castSucc=(0:Fin (n+2)) from rfl,hs]
    exact (HochschildSakai.abstract_multiplication_normal e).2 _
  · have hip : (0 : ℕ) < (i : ℕ) := by omega
    rw [sliceAt_left h i hip v]
    exact ((HochschildSakai.abstract_multiplication_normal e).1 _).comp e
      (hN _ (by dsimp; omega) _)

lemma middleCoboundary_before_normal {n : ℕ} (h : Cochain M (n+1)) (r : ℕ)
    (hN : NormalBefore e h r) (i : Fin (n+1)) (hi : i.val≤r) (v : Fin (n+1) → M) :
    ∀ j : Fin (n+1),j.val<r → HasPreadjoint e (sliceAt (middleCoboundary h j) i.castSucc v) := by
  rw [Fin.forall_iff_succAbove i]
  constructor
  · intro hir
    rw [sliceAt_middle_same]
    exact (hN _ hir _).comp e ((HochschildSakai.abstract_multiplication_normal e).2 _)
  · intro j hj
    rcases lt_trichotomy (j.val+1) i.val with hij|hij|hij
    · rw [sliceAt_middle_before h i j hij v]
      exact hN _ (by dsimp; omega) _
    · rw [sliceAt_middle_before_boundary h i j hij v]
      exact (hN j.castSucc (by simp only [Fin.val_castSucc]; omega) _).comp e
        ((HochschildSakai.abstract_multiplication_normal e).1 _)
    · have hle : i.val≤j.val := by omega
      rw [sliceAt_middle_after h i j hle v]
      have hs : i.succAbove j=j.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simpa only [Fin.le_def,Fin.val_castSucc] using hle)
      rw [hs] at hj
      exact hN _ (by simp only [Fin.val_succ] at hj; omega) _

lemma prefixDifferential_before_normal {n : ℕ} (h : Cochain M (n+1)) (r : ℕ)
    (hN : NormalBefore e h r) (i : Fin (n+1)) (hi : i.val≤r) (v : Fin (n+1) → M) :
    HasPreadjoint e (sliceAt (prefixDifferential h r) i.castSucc v) := by
  rw [prefixDifferential,sliceAt_add,sliceAt_sum]
  apply (leftCoboundary_before_normal e h r hN i hi v).add e
  apply HasPreadjoint.sum e
  intro j _
  by_cases hj : j.val<r
  · rw [ite_eq_left hj,sliceAt_smul]
    exact (middleCoboundary_before_normal e h r hN i hi v j hj).smul e _
  · rw [ite_eq_right hj,sliceAt_zero]
    exact HasPreadjoint.zero e
end BoundedHochschild
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.prefixDifferential_before_normal.{u} := @OAI.BoundedHochschild.prefixDifferential_before_normal.{u}
