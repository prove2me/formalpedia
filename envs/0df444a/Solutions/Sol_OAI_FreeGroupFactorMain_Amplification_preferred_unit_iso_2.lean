-- Prove2me | solution 2 for OAI.FreeGroupFactorMain.Amplification.preferred_unit_iso
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T05:18:00.324858+00:00
-- url     : https://prove2.me/submissions/0171febc-df40-4271-a316-14d00407465f

import Mathlib
import Definitions.Def_FreeGroupFactorProof33

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace FreeGroupFactorMain.HilbertUltraweak
variable (E : Type u_1) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

@[instance_reducible] def topology : TopologicalSpace (E →L[ℂ] E) :=
  ⨅ (ξ : lp (fun _ : ℕ => E) 2) (η : lp (fun _ : ℕ => E) 2),
    TopologicalSpace.induced (fun T : E →L[ℂ] E => ∑' k : ℕ, inner ℂ (η k) (T (ξ k))) inferInstance

variable {E} {F : Type u_2} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
def sequenceMap (L : E →L[ℂ] F) (ξ : lp (fun _ : ℕ => E) 2) : lp (fun _ : ℕ => F) 2 :=
  ⟨fun k => L (ξ k),((lp.memℓp ξ).norm.const_mul ‖L‖).mono (fun k => L.le_opNorm (ξ k))⟩

omit [CompleteSpace E] in
theorem functional_continuous (ξ η : lp (fun _ : ℕ => E) 2) :
    @Continuous _ _ (topology E) _ (fun T : E →L[ℂ] E => ∑' k : ℕ,inner ℂ (η k) (T (ξ k))) :=
  continuous_iInf_dom (i := ξ) (continuous_iInf_dom (i := η) continuous_induced_dom)

theorem sandwich_continuous (L : E →L[ℂ] F) (R : F →L[ℂ] E) :
    @Continuous _ _ (topology E) (topology F) (fun T : E →L[ℂ] E => L.comp (T.comp R)) := by
  apply continuous_iInf_rng.mpr
  intro ξ
  apply continuous_iInf_rng.mpr
  intro η
  apply continuous_induced_rng.mpr
  have he : (fun T : E →L[ℂ] E => ∑' k : ℕ,inner ℂ (η k) (L (T (R (ξ k)))))=
      (fun T : E →L[ℂ] E => ∑' k : ℕ,inner ℂ (sequenceMap (ContinuousLinearMap.adjoint L) η k)
        (T (sequenceMap R ξ k))) := by
    funext T
    apply tsum_congr
    intro k
    exact (ContinuousLinearMap.adjoint_inner_left L (T (R (ξ k))) (η k)).symm
  change @Continuous _ _ (topology E) _ (fun T : E →L[ℂ] E => ∑' k : ℕ,inner ℂ (η k) (L (T (R (ξ k)))))
  rw [he]
  exact functional_continuous _ _

omit [CompleteSpace E] in
theorem add_continuous {X : Type u_3} [TopologicalSpace X] {f g : X → (E →L[ℂ] E)}
    (hf : @Continuous _ _ _ (topology E) f) (hg : @Continuous _ _ _ (topology E) g) :
    @Continuous _ _ _ (topology E) (fun x => f x+g x) := by
  let : TopologicalSpace (E →L[ℂ] E) := topology E
  apply continuous_iInf_rng.mpr
  intro ξ
  apply continuous_iInf_rng.mpr
  intro η
  apply continuous_induced_rng.mpr
  have he (x : X) :
      (∑' k : ℕ,inner ℂ (η k) ((f x+g x) (ξ k)))=
        (∑' k : ℕ,inner ℂ (η k) (f x (ξ k)))+(∑' k : ℕ,inner ℂ (η k) (g x (ξ k))) := by
    simp only [add_apply,inner_add_right]
    exact (lp.summable_inner η (sequenceMap (f x) ξ)).tsum_add (lp.summable_inner η (sequenceMap (g x) ξ))
  change Continuous (fun x : X => ∑' k : ℕ,inner ℂ (η k) ((f x+g x) (ξ k)))
  simp_rw [he]
  exact ((functional_continuous ξ η).comp hf).add ((functional_continuous ξ η).comp hg)
end FreeGroupFactorMain.HilbertUltraweak

section
namespace FreeGroupFactorMain.CornerRerouting
variable {A : Type u_4} [Ring A] [StarRing A]

end FreeGroupFactorMain.CornerRerouting

namespace FreeGroupFactorMain.FullReducingCorner
open Amplification CornerRerouting
variable {A : Type u_5} [CStarAlgebra A]

variable (p : A) (hp : IsStarProjection p) (s : Set A)
variable (hps : p∈StarSubalgebra.centralizer ℂ s)

variable (v : A) (hvs : v∈StarSubalgebra.centralizer ℂ s)
variable (hpv : p*v=v) (hvr : v*(1-p)=v) (hvi : star v*v=1-p)

end FreeGroupFactorMain.FullReducingCorner

end

namespace FreeGroupFactorMain.ReducingSubspace
variable {E : Type u_6} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (K : Submodule ℂ E) [CompleteSpace K]

variable [CompleteSpace E]

end FreeGroupFactorMain.ReducingSubspace

namespace FreeGroupFactorMain.GaussianRecognition.System
open ReducingSubspace
variable {A : Type u_7} {E : Type u_8} {I : Type u_9} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)

end FreeGroupFactorMain.GaussianRecognition.System

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification CyclicSpectral GaussianRecognition
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.Amplification

section
open scoped ENNReal
variable {G : Type u_1}

def matrixBlock (i j : ℕ) (T : GroupOperator G) : GroupOperator (ℕ × G) :=
  (productSingle ℕ G i).comp (T.comp (productCoordinate ℕ G j))

@[simp] theorem matrixBlock_apply (i j k : ℕ) (T : GroupOperator G)
    (ξ : GroupHilbert (ℕ × G)) (g : G) :
    matrixBlock i j T ξ (k,g)=if k=i then T (productCoordinate ℕ G j ξ) g else 0 := by
  simp only [matrixBlock,ContinuousLinearMap.comp_apply,productSingle_apply]

@[simp] theorem matrixEntry_matrixBlock (i j k l : ℕ) (T : GroupOperator G) :
    matrixEntry (matrixBlock i j T) k l=if k=i ∧ l=j then T else 0 := by
  ext ξ g
  simp only [matrixEntry_apply,matrixBlock_apply,productCoordinate_productSingle]
  by_cases hk : k=i <;> by_cases hl : l=j <;> simp [hk,hl,show (j=l) ↔ (l=j) from eq_comm]

@[simp] theorem matrixBlock_zero (i j : ℕ) : matrixBlock i j (0 : GroupOperator G)=0 := by
  ext ξ ⟨k,g⟩
  simp

@[simp] theorem matrixBlock_mul (i j k l : ℕ) (T S : GroupOperator G) :
    matrixBlock i j T * matrixBlock k l S=if j=k then matrixBlock i l (T*S) else 0 := by
  ext ξ ⟨m,g⟩
  simp only [mul_apply_eq_comp,matrixBlock_apply]
  have hc : productCoordinate ℕ G j (matrixBlock k l S ξ)=
      if j=k then S (productCoordinate ℕ G l ξ) else 0 := by
    change productCoordinate ℕ G j (productSingle ℕ G k (S (productCoordinate ℕ G l ξ)))=_
    rw [productCoordinate_productSingle]
  rw [hc]
  by_cases hj : j=k <;> by_cases hm : m=i <;> simp [hj,hm,mul_apply_eq_comp]

@[simp] theorem matrixBlock_star (i j : ℕ) (T : GroupOperator G) :
    star (matrixBlock i j T)=matrixBlock j i (star T) := by
  apply matrixEntry_ext
  intro k l
  rw [matrixEntry_star,matrixEntry_matrixBlock,matrixEntry_matrixBlock]
  by_cases h : l=i ∧ k=j
  · simp only [ite_eq_left h,ite_eq_left (And.symm h)]
  · simp only [ite_eq_right h,ite_eq_right (fun hh => h (And.symm hh)),star_zero (GroupOperator G)]

theorem matrixBlock_mem [Group G] (i j : ℕ) (T : groupVonNeumann G) :
    matrixBlock i j (T : GroupOperator G)∈stabilization G := by
  rw [mem_stabilization_iff_matrix]
  intro k l
  rw [matrixEntry_matrixBlock]
  split_ifs
  · exact T.property
  · exact (groupVonNeumann G).zero_mem

def finiteMatrix (n : ℕ) (X : Fin n → Fin n → GroupOperator G) : GroupOperator (ℕ × G) :=
  ∑ i : Fin n, ∑ j : Fin n, matrixBlock i.val j.val (X i j)

theorem matrixEntry_finiteMatrix (n : ℕ) (X : Fin n → Fin n → GroupOperator G) (i j : Fin n) :
    matrixEntry (finiteMatrix n X) i.val j.val=X i j := by
  classical
  simp [finiteMatrix,matrixEntry_sum,matrixEntry_matrixBlock,Fin.val_inj,ite_and]

theorem matrixEntry_finiteMatrix_out (n : ℕ) (X : Fin n → Fin n → GroupOperator G) (i j : ℕ)
    (h : n ≤ i ∨ n ≤ j) : matrixEntry (finiteMatrix n X) i j=0 := by
  classical
  simp only [finiteMatrix,matrixEntry_sum,matrixEntry_matrixBlock]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  rw [ite_eq_right]
  rintro ⟨rfl,rfl⟩
  cases h with
  | inl h => exact (not_le_of_gt a.isLt) h
  | inr h => exact (not_le_of_gt b.isLt) h

theorem finiteMatrix_mem [Group G] (n : ℕ) (X : Fin n → Fin n → groupVonNeumann G) :
    finiteMatrix n (fun i j => (X i j : GroupOperator G))∈stabilization G := by
  classical
  exact (stabilization G).sum_mem (fun i _ => (stabilization G).sum_mem (fun j _ => matrixBlock_mem i.val j.val (X i j)))

@[simp] theorem matrixBlock_add (i j : ℕ) (T S : GroupOperator G) :
    matrixBlock i j (T+S)=matrixBlock i j T+matrixBlock i j S := by
  ext ξ ⟨k,g⟩
  by_cases h : k=i <;> simp [h]

@[simp] theorem matrixBlock_smul (i j : ℕ) (c : ℂ) (T : GroupOperator G) :
    matrixBlock i j (c • T)=c • matrixBlock i j T := by
  ext ξ ⟨k,g⟩
  by_cases h : k=i <;> simp [h]

@[simp] theorem matrixBlock_sum {ι : Type u_3} (i j : ℕ) (s : Finset ι) (T : ι → GroupOperator G) :
    matrixBlock i j (∑ k∈s,T k)=∑ k∈s,matrixBlock i j (T k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha,ih]

 theorem matrixBlock_mul_finiteMatrix (n : ℕ) (i : ℕ) (j : Fin n) (T : GroupOperator G)
    (Y : Fin n → Fin n → GroupOperator G) :
    matrixBlock i j.val T * finiteMatrix n Y=∑ l : Fin n,matrixBlock i l.val (T*Y j l) := by
  classical
  simp only [finiteMatrix,Finset.mul_sum,matrixBlock_mul,Fin.val_inj]
  rw [Finset.sum_comm]
  congr 1
  ext l
  simp

 theorem finiteMatrix_mul (n : ℕ) (X Y : Fin n → Fin n → GroupOperator G) :
    finiteMatrix n X * finiteMatrix n Y=finiteMatrix n (fun i j => ∑ k : Fin n,X i k*Y k j) := by
  classical
  simp only [finiteMatrix,Finset.sum_mul]
  change (∑ i : Fin n,∑ j : Fin n,matrixBlock i.val j.val (X i j)*finiteMatrix n Y)=_
  simp only [matrixBlock_mul_finiteMatrix,matrixBlock_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

 theorem finiteMatrix_star (n : ℕ) (X : Fin n → Fin n → GroupOperator G) :
    star (finiteMatrix n X)=finiteMatrix n (fun i j => star (X j i)) := by
  classical
  simp only [finiteMatrix,star_sum (R := GroupOperator (ℕ × G)),matrixBlock_star]
  exact Finset.sum_comm

 def finiteDiagonal (n : ℕ) (T : GroupOperator G) : GroupOperator (ℕ × G) :=
  finiteMatrix n (fun i j => if i=j then T else 0)

 theorem finiteDiagonal_sum (n : ℕ) (T : GroupOperator G) :
    finiteDiagonal n T=∑ i : Fin n,matrixBlock i.val i.val T := by
  classical
  simp only [finiteDiagonal,finiteMatrix]
  apply Finset.sum_congr rfl
  intro i _
  have hh (j : Fin n) : matrixBlock i.val j.val (if i=j then T else 0)=if i=j then matrixBlock i.val j.val T else 0 := by split_ifs <;> simp
  simp_rw [hh]
  simp

 theorem finiteDiagonal_mul (n : ℕ) (T S : GroupOperator G) :
    finiteDiagonal n T*finiteDiagonal n S=finiteDiagonal n (T*S) := by
  classical
  rw [finiteDiagonal,finiteDiagonal,finiteMatrix_mul]
  congr 1
  funext i j
  simp

 theorem finiteDiagonal_star (n : ℕ) (T : GroupOperator G) :
    star (finiteDiagonal n T)=finiteDiagonal n (star T) := by
  classical
  rw [finiteDiagonal,finiteMatrix_star]
  congr 1
  funext i j
  split_ifs <;> simp_all [eq_comm,star_zero (R := GroupOperator G)]

theorem matrixBlock_sandwich (i j k l : ℕ) (A B : GroupOperator G) (T : GroupOperator (ℕ × G)) :
    matrixBlock i j A*T*matrixBlock k l B=matrixBlock i l (A*matrixEntry T j k*B) := by
  apply ContinuousLinearMap.ext
  intro ξ
  rfl

 theorem finiteDiagonal_sandwich (n : ℕ) (A B : GroupOperator G) (T : GroupOperator (ℕ × G)) :
    finiteDiagonal n A*T*finiteDiagonal n B=
      finiteMatrix n (fun i j => A*matrixEntry T i.val j.val*B) := by
  classical
  simp only [finiteDiagonal_sum,Finset.sum_mul,Finset.mul_sum,matrixBlock_sandwich,finiteMatrix]
  exact Finset.sum_comm

variable [Group G]

 def finiteProjection (n : ℕ) (p : groupVonNeumann G) : stabilization G :=
  ⟨finiteDiagonal n (p : GroupOperator G),by
    classical
    rw [finiteDiagonal_sum]
    exact (stabilization G).sum_mem (fun i _ => matrixBlock_mem i.val i.val p)⟩

 theorem finiteProjection_projection (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p) :
    IsStarProjection (finiteProjection n p) := by
  constructor
  · apply Subtype.ext
    change finiteDiagonal n (p : GroupOperator G)*finiteDiagonal n (p : GroupOperator G)=_
    rw [finiteDiagonal_mul]
    exact congrArg (finiteDiagonal n) (congrArg Subtype.val hp.isIdempotentElem.eq)
  · apply Subtype.ext
    change star (finiteDiagonal n (p : GroupOperator G))=_
    rw [finiteDiagonal_star]
    exact congrArg (finiteDiagonal n) (congrArg Subtype.val hp.isSelfAdjoint.star_eq)

 theorem finiteDiagonal_entries (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : Corner (finiteProjection n p) (finiteProjection_projection n p hp)) :
    finiteMatrix n (fun i j => (p : GroupOperator G)*matrixEntry (x.val : GroupOperator (ℕ × G)) i.val j.val*(p : GroupOperator G))=
      (x.val : GroupOperator (ℕ × G)) := by
  rw [←finiteDiagonal_sandwich]
  change ((finiteProjection n p * x.val * finiteProjection n p : stabilization G) : GroupOperator (ℕ × G))=_
  rw [x.property.1,x.property.2]

end

open scoped ENNReal
variable {G : Type u_4} [Group G]

abbrev FiniteCorner (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p) :=
  Corner (finiteProjection n p) (finiteProjection_projection n p hp)

theorem finiteCorner_entry_sandwich (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : FiniteCorner n p hp) (i j : Fin n) :
    (p : GroupOperator G)*matrixEntry (x.val : GroupOperator (ℕ × G)) i.val j.val*(p : GroupOperator G)=
      matrixEntry (x.val : GroupOperator (ℕ × G)) i.val j.val := by
  have hh := congrArg (fun T : GroupOperator (ℕ × G) => matrixEntry T i.val j.val)
    (finiteDiagonal_entries n p hp x)
  rwa [matrixEntry_finiteMatrix] at hh

def finiteCornerEntry (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : FiniteCorner n p hp) (i j : Fin n) : Corner p hp := by
  let T : groupVonNeumann G := ⟨matrixEntry (x.val : GroupOperator (ℕ × G)) i.val j.val,
    (mem_stabilization_iff_matrix _).mp x.val.property i.val j.val⟩
  have hh : p*T*p=T := Subtype.ext (finiteCorner_entry_sandwich n p hp x i j)
  refine ⟨T,?_,?_⟩
  · calc p*T=p*(p*T*p) := congrArg (p*·) hh.symm
         _=p*T*p := by rw [←mul_assoc,←mul_assoc,hp.isIdempotentElem.eq]
         _=T := hh
  · calc T*p=(p*T*p)*p := congrArg (·*p) hh.symm
         _=p*T*p := by rw [mul_assoc (p*T),hp.isIdempotentElem.eq]
         _=T := hh

theorem finiteCorner_reconstruct (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : FiniteCorner n p hp) :
    finiteMatrix n (fun i j => ((finiteCornerEntry n p hp x i j).val : GroupOperator G))=
      (x.val : GroupOperator (ℕ × G)) := by
  have he : (fun i j : Fin n => ((finiteCornerEntry n p hp x i j).val : GroupOperator G))=
      (fun i j : Fin n => (p : GroupOperator G)*matrixEntry (x.val : GroupOperator (ℕ × G)) i.val j.val*(p : GroupOperator G)) := by
    funext i j
    exact (finiteCorner_entry_sandwich n p hp x i j).symm
  rw [he]
  exact finiteDiagonal_entries n p hp x

theorem finiteCorner_ext (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x y : FiniteCorner n p hp) (h : ∀ i j,finiteCornerEntry n p hp x i j=finiteCornerEntry n p hp y i j) : x=y := by
  apply Subtype.ext
  apply Subtype.ext
  rw [←finiteCorner_reconstruct n p hp x,←finiteCorner_reconstruct n p hp y]
  congr 1
  funext i j
  rw [h i j]

 def finiteCornerOfMatrix (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (X : Fin n → Fin n → Corner p hp) : FiniteCorner n p hp := by
  let T : stabilization G := ⟨finiteMatrix n (fun i j => ((X i j).val : GroupOperator G)),
    finiteMatrix_mem n (fun i j => (X i j).val)⟩
  refine ⟨T,?_,?_⟩
  · apply Subtype.ext
    change finiteMatrix n (fun i j => if i=j then (p : GroupOperator G) else 0)*finiteMatrix n _=_
    rw [finiteMatrix_mul]
    congr 1
    funext i j
    simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    exact congrArg Subtype.val (X i j).property.1
  · apply Subtype.ext
    change finiteMatrix n _*finiteMatrix n (fun i j => if i=j then (p : GroupOperator G) else 0)=_
    rw [finiteMatrix_mul]
    congr 1
    funext i j
    simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact congrArg Subtype.val (X i j).property.2

@[simp] theorem finiteCornerEntry_ofMatrix (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (X : Fin n → Fin n → Corner p hp) (i j : Fin n) :
    finiteCornerEntry n p hp (finiteCornerOfMatrix n p hp X) i j=X i j := by
  apply Subtype.ext
  apply Subtype.ext
  exact matrixEntry_finiteMatrix n _ i j

@[simp] theorem finiteCornerEntry_add (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x y : FiniteCorner n p hp) (i j : Fin n) :
    finiteCornerEntry n p hp (x+y) i j=finiteCornerEntry n p hp x i j+finiteCornerEntry n p hp y i j := by
  apply Subtype.ext
  apply Subtype.ext
  ext ξ g
  simp [finiteCornerEntry,matrixEntry_apply]

@[simp] theorem finiteCornerEntry_smul (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : FiniteCorner n p hp) (c : ℂ) (i j : Fin n) :
    finiteCornerEntry n p hp (c • x) i j=c • finiteCornerEntry n p hp x i j := by
  apply Subtype.ext
  apply Subtype.ext
  ext ξ g
  simp [finiteCornerEntry,matrixEntry_apply]

@[simp] theorem finiteCornerEntry_star (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : FiniteCorner n p hp) (i j : Fin n) :
    finiteCornerEntry n p hp (star x) i j=star (finiteCornerEntry n p hp x j i) := by
  apply Subtype.ext
  apply Subtype.ext
  exact matrixEntry_star _ i.val j.val

 theorem finiteCornerEntry_mul (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x y : FiniteCorner n p hp) (i j : Fin n) :
    finiteCornerEntry n p hp (x*y) i j=∑ k : Fin n,finiteCornerEntry n p hp x i k*finiteCornerEntry n p hp y k j := by
  apply Subtype.ext
  apply Subtype.ext
  change matrixEntry ((x.val : GroupOperator (ℕ × G))*(y.val : GroupOperator (ℕ × G))) i.val j.val=_
  rw [←finiteCorner_reconstruct n p hp x,←finiteCorner_reconstruct n p hp y,finiteMatrix_mul,matrixEntry_finiteMatrix]
  simp

variable {H : Type u_5} [Group H]

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

section
namespace FreeGroupFactorMain.HilbertUltraweak
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {X : Type u_2} [TopologicalSpace X]

theorem finset_sum_continuous {ι : Type u_3} (s : Finset ι) (f : ι → X → (E →L[ℂ] E))
    (hf : ∀ i∈s,@Continuous _ _ _ (topology E) (f i)) :
    @Continuous _ _ _ (topology E) (fun x => ∑ i∈s,f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (@continuous_const X _ _ (topology E) (0 : E →L[ℂ] E))
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact add_continuous (hf a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
end FreeGroupFactorMain.HilbertUltraweak

namespace FreeGroupFactorMain.Amplification
variable {G : Type u_4} {H : Type u_5}

 theorem matrixEntry_normal (i j : ℕ) :
    @Continuous _ _ (ultraweakOperatorTopology (ℕ × G)) (ultraweakOperatorTopology G)
      (fun T : GroupOperator (ℕ × G) => matrixEntry T i j) := by
  have hc := HilbertUltraweak.sandwich_continuous (productCoordinate ℕ G i) (productSingle ℕ G j)
  convert hc using 1 <;> rfl

 theorem matrixBlock_normal (i j : ℕ) :
    @Continuous _ _ (ultraweakOperatorTopology G) (ultraweakOperatorTopology (ℕ × G))
      (matrixBlock (G := G) i j) :=
  HilbertUltraweak.sandwich_continuous (productSingle ℕ G i) (productCoordinate ℕ G j)

variable [Group G] [Group H]

 theorem finiteCornerEntry_normal (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p) (i j : Fin n) :
    @Continuous _ _ (cornerTopology (stabilizationTopology G) (finiteProjection n p) (finiteProjection_projection n p hp))
      (cornerTopology (groupUltraweakTopology G) p hp) (fun x => finiteCornerEntry n p hp x i j) := by
  let : TopologicalSpace (GroupOperator (ℕ × G)) := ultraweakOperatorTopology (ℕ × G)
  let : TopologicalSpace (GroupOperator G) := ultraweakOperatorTopology G
  let : TopologicalSpace (stabilization G) := stabilizationTopology G
  let : TopologicalSpace (groupVonNeumann G) := groupUltraweakTopology G
  let : TopologicalSpace (FiniteCorner n p hp) := cornerTopology (stabilizationTopology G) (finiteProjection n p) (finiteProjection_projection n p hp)
  let : TopologicalSpace (Corner p hp) := cornerTopology (groupUltraweakTopology G) p hp
  exact (((matrixEntry_normal i.val j.val).comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).subtype_mk _

 theorem finiteCornerOfMatrix_normal (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    {X : Type u_6} [TopologicalSpace X] (f : X → Fin n → Fin n → Corner p hp)
    (hf : ∀ i j,@Continuous _ _ _ (cornerTopology (groupUltraweakTopology G) p hp) (fun x => f x i j)) :
    @Continuous _ _ _ (cornerTopology (stabilizationTopology G) (finiteProjection n p) (finiteProjection_projection n p hp))
      (fun x => finiteCornerOfMatrix n p hp (f x)) := by
  let : TopologicalSpace (GroupOperator (ℕ × G)) := ultraweakOperatorTopology (ℕ × G)
  let : TopologicalSpace (GroupOperator G) := ultraweakOperatorTopology G
  let : TopologicalSpace (stabilization G) := stabilizationTopology G
  let : TopologicalSpace (groupVonNeumann G) := groupUltraweakTopology G
  let : TopologicalSpace (Corner p hp) := cornerTopology (groupUltraweakTopology G) p hp
  have hc : Continuous (fun x => finiteMatrix n (fun i j => ((f x i j).val : GroupOperator G))) := by
    apply HilbertUltraweak.finset_sum_continuous
    intro i _
    apply HilbertUltraweak.finset_sum_continuous
    intro j _
    exact (matrixBlock_normal i.val j.val).comp (continuous_subtype_val.comp (continuous_subtype_val.comp (hf i j)))
  exact (hc.subtype_mk _).subtype_mk _

end FreeGroupFactorMain.Amplification

end

namespace FreeGroupFactorMain.Amplification
open scoped ENNReal
variable {G : Type u_7}

 theorem productSingle_norm (i : ℕ) (ξ : GroupHilbert G) : ‖productSingle ℕ G i ξ‖=‖ξ‖ := by
  classical
  let : DecidableEq ℕ := Classical.decEq ℕ
  simp only [productSingle,ContinuousLinearMap.comp_apply,lp.singleContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [LinearIsometryEquiv.norm_map,lp.norm_single (by norm_num : (0 : ℝ≥0∞)<2)]

 theorem matrixBlock_productSingle (i j k : ℕ) (T : GroupOperator G) (ξ : GroupHilbert G) :
    matrixBlock i j T (productSingle ℕ G k ξ)=if j=k then productSingle ℕ G i (T ξ) else 0 := by
  simp only [matrixBlock,ContinuousLinearMap.comp_apply,productCoordinate_productSingle]
  split_ifs <;> simp

 theorem finiteDiagonal_productSingle (n : ℕ) (T : GroupOperator G) (k : ℕ) (ξ : GroupHilbert G) :
    finiteDiagonal n T (productSingle ℕ G k ξ)=if k<n then productSingle ℕ G k (T ξ) else 0 := by
  classical
  rw [finiteDiagonal_sum]
  simp only [sum_apply,matrixBlock_productSingle]
  by_cases hk : k<n
  · rw [ite_eq_left hk]
    let j : Fin n := ⟨k,hk⟩
    have he : ∀ i : Fin n,i.val=k ↔ i=j := fun i => (Fin.ext_iff (a := i) (b := j)).symm
    simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rfl
  · rw [ite_eq_right hk]
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right]
    intro hi
    exact hk (hi ▸ i.isLt)

variable [Group G]

 theorem finiteProjection_trace (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (a : ℝ) (_ha : 0≤a) (hpa : canonicalTrace p=(a:ℂ)) :
    stabilizedProjectionTrace (finiteProjection n p)=ENNReal.ofReal (n*a) := by
  classical
  have hv : ‖(p : GroupOperator G) (lp.single 2 (1:G) (1:ℂ))‖^2=a := by
    apply Complex.ofReal_injective
    have hh := canonicalTrace_star_mul p
    rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq,hpa] at hh
    simpa only [Complex.ofReal_pow] using hh.symm
  change (∑' k : ℕ,ENNReal.ofReal (‖finiteDiagonal n (p : GroupOperator G) (lp.single 2 (k,1) (1:ℂ))‖^2))=_
  have he (k : ℕ) : ENNReal.ofReal (‖finiteDiagonal n (p : GroupOperator G) (lp.single 2 (k,1) (1:ℂ))‖^2)=
      if k<n then ENNReal.ofReal a else 0 := by
    rw [←productSingle_single,finiteDiagonal_productSingle]
    split_ifs
    · rw [productSingle_norm,hv]
    · simp
  simp_rw [he]
  rw [tsum_eq_sum (s := Finset.range n)]
  · have hh : (∑ k∈Finset.range n,if k<n then ENNReal.ofReal a else 0)=∑ _k∈Finset.range n,ENNReal.ofReal a :=
      Finset.sum_congr rfl (fun k hk => ite_eq_left (Finset.mem_range.mp hk))
    rw [hh]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n),ENNReal.ofReal_natCast]
  · intro k hk
    rw [ite_eq_right (fun h => hk (Finset.mem_range.mpr h))]

 theorem stabilizedTrace_matrix (T : stabilization G) :
    stabilizedTrace T=∑' k : ℕ,canonicalTrace
      (⟨matrixEntry (T : GroupOperator (ℕ × G)) k k,(mem_stabilization_iff_matrix _).mp T.property k k⟩ : groupVonNeumann G) := by
  classical
  apply tsum_congr
  intro k
  rw [←productSingle_single,productSingle_inner_left,canonicalTrace_eq_inner]
  rfl

 theorem finiteCorner_trace (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p) (x : FiniteCorner n p hp) :
    stabilizedTrace x.val=∑ i : Fin n,canonicalTrace (finiteCornerEntry n p hp x i i).val := by
  classical
  rw [stabilizedTrace_matrix]
  have he (k : ℕ) : canonicalTrace
      (⟨matrixEntry (x.val : GroupOperator (ℕ × G)) k k,(mem_stabilization_iff_matrix _).mp x.val.property k k⟩ : groupVonNeumann G)=
      if hk : k<n then canonicalTrace (finiteCornerEntry n p hp x ⟨k,hk⟩ ⟨k,hk⟩).val else 0 := by
    split_ifs with hk
    · rfl
    · have hz : matrixEntry (x.val : GroupOperator (ℕ × G)) k k=0 := by
        rw [←finiteCorner_reconstruct n p hp x]
        exact matrixEntry_finiteMatrix_out n _ k k (Or.inl (le_of_not_gt hk))
      have hs : (⟨matrixEntry (x.val : GroupOperator (ℕ × G)) k k,(mem_stabilization_iff_matrix _).mp x.val.property k k⟩ : groupVonNeumann G)=0 := Subtype.ext hz
      rw [hs]
      exact map_zero (canonicalTraceLinear (G := G))
  simp_rw [he]
  rw [tsum_eq_sum (s := Finset.range n)]
  · rw [←Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    simp only [dite_eq_left k.isLt]
  · intro k hk
    simp only [dite_eq_right (fun h => hk (Finset.mem_range.mpr h))]

variable {H : Type u_8} [Group H]

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

namespace FreeGroupFactorMain.Amplification

section
open scoped ENNReal
variable {G : Type u_1} [Group G]

section Singles
variable [DecidableEq G]

end Singles

end

section
variable {G : Type u_2} [Group G]

def finiteCornerSingletonIso (p : groupVonNeumann G) (hp : IsStarProjection p) :
    FiniteCorner 1 p hp ≃⋆ₐ[ℂ] Corner p hp where
  toFun x := finiteCornerEntry 1 p hp x 0 0
  invFun x := finiteCornerOfMatrix 1 p hp (fun _ _ => x)
  left_inv x := by
    apply finiteCorner_ext 1 p hp
    intro i j
    have hi : i=0 := Subsingleton.elim _ _
    have hj : j=0 := Subsingleton.elim _ _
    subst i; subst j
    exact finiteCornerEntry_ofMatrix 1 p hp _ 0 0
  right_inv x := finiteCornerEntry_ofMatrix 1 p hp _ 0 0
  map_mul' x y := by
    rw [finiteCornerEntry_mul]
    simp
  map_add' x y := finiteCornerEntry_add 1 p hp x y 0 0
  map_smul' c x := finiteCornerEntry_smul 1 p hp x c 0 0
  map_star' x := finiteCornerEntry_star 1 p hp x 0 0

theorem finiteCornerSingletonIso_normal (p : groupVonNeumann G) (hp : IsStarProjection p) :
    @Continuous _ _
      (cornerTopology (stabilizationTopology G) (finiteProjection 1 p) (finiteProjection_projection 1 p hp))
      (cornerTopology (groupUltraweakTopology G) p hp) (finiteCornerSingletonIso p hp) :=
  finiteCornerEntry_normal 1 p hp 0 0

theorem finiteCornerSingletonIso_trace (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : FiniteCorner 1 p hp) :
    canonicalTrace (finiteCornerSingletonIso p hp x).val=stabilizedTrace x.val := by
  rw [finiteCorner_trace]
  simp only [Fin.sum_univ_one]
  rfl

end

variable {G : Type u_3} {H : Type u_4} [Group G] [Group H]

theorem finiteCornerSingletonIso_symm_normal (p : groupVonNeumann G) (hp : IsStarProjection p) :
    @Continuous _ _ (cornerTopology (groupUltraweakTopology G) p hp)
      (cornerTopology (stabilizationTopology G) (finiteProjection 1 p) (finiteProjection_projection 1 p hp))
      (finiteCornerSingletonIso p hp).symm := by
  let : TopologicalSpace (Corner p hp) := cornerTopology (groupUltraweakTopology G) p hp
  exact finiteCornerOfMatrix_normal 1 p hp _ (fun _ _ => continuous_id)

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_1} {B : Type u_2} [CStarAlgebra A] [CStarAlgebra B]

def unitCornerEquiv : A ≃⋆ₐ[ℂ] Corner (1:A) (IsStarProjection.one A) where
  toFun a := ⟨a,⟨one_mul a,mul_one a⟩⟩
  invFun a := a.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

end

variable {A : Type u_3} {B : Type u_4} [CStarAlgebra A] [CStarAlgebra B]

end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification GaussianRecognition

end FreeGroupFactorMain.WeightedFock

namespace FreeGroupFactorMain.Amplification
open WeightedFock FreeFock

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

namespace NormalTracialEquiv
variable {τA : A → ℂ} {τB : B → ℂ} {τC : C → ℂ}
variable {𝒯A : TopologicalSpace A} {𝒯B : TopologicalSpace B} {𝒯C : TopologicalSpace C}

def trans (e : NormalTracialEquiv τA τB 𝒯A 𝒯B) (f : NormalTracialEquiv τB τC 𝒯B 𝒯C) :
    NormalTracialEquiv τA τC 𝒯A 𝒯C where
  equiv := e.equiv.trans f.equiv
  trace_eq x := (f.trace_eq (e.equiv x)).trans (e.trace_eq x)
  normal := by
    let : TopologicalSpace A := 𝒯A
    let : TopologicalSpace B := 𝒯B
    let : TopologicalSpace C := 𝒯C
    exact f.normal.comp e.normal
  inverse_normal := by
    let : TopologicalSpace A := 𝒯A
    let : TopologicalSpace B := 𝒯B
    let : TopologicalSpace C := 𝒯C
    exact e.inverse_normal.comp f.inverse_normal

end NormalTracialEquiv
end

open scoped ENNReal
variable {G : Type u_4} [Group G]

def unitNormalIso {A : Type u_5} [CStarAlgebra A] (τ : A → ℂ) (𝒯 : TopologicalSpace A) :
    NormalTracialEquiv (fun x : Corner (1:A) (IsStarProjection.one A) => τ x.val) τ
      (cornerTopology 𝒯 1 (IsStarProjection.one A)) 𝒯 where
  equiv := unitCornerEquiv.symm
  trace_eq _ := rfl
  normal := by
    let : TopologicalSpace A := 𝒯
    exact continuous_subtype_val
  inverse_normal := by
    let : TopologicalSpace A := 𝒯
    exact continuous_id.subtype_mk _

def finiteSingletonNormalIso (p : groupVonNeumann G) (hp : IsStarProjection p) :
    NormalTracialEquiv (normalizedCornerTrace stabilizedTrace 1 (finiteProjection 1 p)
      (finiteProjection_projection 1 p hp)) (fun x : Corner p hp => canonicalTrace x.val)
      (cornerTopology (stabilizationTopology G) (finiteProjection 1 p) (finiteProjection_projection 1 p hp))
      (cornerTopology (groupUltraweakTopology G) p hp) where
  equiv := finiteCornerSingletonIso p hp
  trace_eq x := by
    simp only [normalizedCornerTrace,Complex.ofReal_one,inv_one,one_mul]
    exact finiteCornerSingletonIso_trace p hp x
  normal := finiteCornerSingletonIso_normal p hp
  inverse_normal := finiteCornerSingletonIso_symm_normal p hp

def finiteUnitCornerIso : GroupCornerNormalIso (G := G) 1
    (finiteProjection 1 (1 : groupVonNeumann G)) (finiteProjection_projection 1 1 (IsStarProjection.one _)) :=
  (finiteSingletonNormalIso (1 : groupVonNeumann G) (IsStarProjection.one _)).trans
    (unitNormalIso canonicalTrace (groupUltraweakTopology G))

theorem canonicalTrace_one : canonicalTrace (1 : groupVonNeumann G)=1 := by
  classical
  simp [canonicalTrace,lp.single_apply]

theorem finiteUnitProjection_trace :
    stabilizedProjectionTrace (finiteProjection 1 (1 : groupVonNeumann G))=ENNReal.ofReal 1 := by
  rw [finiteProjection_trace 1 1 (IsStarProjection.one _) 1 zero_le_one canonicalTrace_one]
  norm_num

theorem preferred_unit_iso
    (hbase : ∀ T : groupVonNeumann G, (∀ S : groupVonNeumann G,Commute T S) →
      ∃ c : ℂ,T=c • (1 : groupVonNeumann G))
    (p : stabilization G) (hp : IsStarProjection p) (hptr : stabilizedProjectionTrace p=ENNReal.ofReal 1) :
    Nonempty (GroupCornerNormalIso 1 p hp) := by
  obtain ⟨e,heτ,hen,hein⟩ := finite_corner_choice_both (G := G) hbase 1 p
    (finiteProjection 1 (1 : groupVonNeumann G)) hp (finiteProjection_projection 1 1 (IsStarProjection.one _))
    (hptr.trans finiteUnitProjection_trace.symm) (hptr ▸ ENNReal.ofReal_ne_top)
  let E : NormalTracialEquiv (normalizedCornerTrace stabilizedTrace 1 p hp)
      (normalizedCornerTrace stabilizedTrace 1 (finiteProjection 1 (1 : groupVonNeumann G))
        (finiteProjection_projection 1 1 (IsStarProjection.one _)))
      (cornerTopology (stabilizationTopology G) p hp)
      (cornerTopology (stabilizationTopology G) (finiteProjection 1 (1 : groupVonNeumann G))
        (finiteProjection_projection 1 1 (IsStarProjection.one _))) := ⟨e,heτ,hen,hein⟩
  exact ⟨E.trans finiteUnitCornerIso⟩

end FreeGroupFactorMain.Amplification

end

end OAI
end

theorem solution.{u_4} : type_of% @OAI.FreeGroupFactorMain.Amplification.preferred_unit_iso.{u_4} := @OAI.FreeGroupFactorMain.Amplification.preferred_unit_iso.{u_4}
