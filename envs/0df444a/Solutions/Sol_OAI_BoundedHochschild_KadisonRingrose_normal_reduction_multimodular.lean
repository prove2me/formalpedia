-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.normal_reduction_multimodular
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:15:43.299209+00:00
-- url     : https://prove2.me/submissions/22715bf1-681e-4beb-8160-0181fa564d1e

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_HochschildNormalPart_normalProjection_fixes_normal
import Theorems.Thm_OAI_HochschildNormalPart_normalProjection_sum
import Theorems.Thm_OAI_BoundedHochschild_differential_is_cocycle
import Theorems.Thm_OAI_HochschildNormalPart_functionalModel_nonempty
import Theorems.Thm_OAI_BoundedHochschild_prefixDifferential_before_normal
import Theorems.Thm_OAI_BoundedHochschild_prefixDifferential_unit_before
import Theorems.Thm_OAI_BoundedHochschild_prefixDifferential_unit_at
import Theorems.Thm_OAI_BoundedHochschild_all_normal_of_before_penultimate
import Theorems.Thm_OAI_HochschildDomination_exists_quartic_hilbert_modulus
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_multimodularAt_differential

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

lemma init_insert {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1)) (q : M) :
    (fun i : Fin (n+1) => (r.castSucc.insertNth (α := fun _ => M) q v) i.castSucc) =
    r.insertNth (α := fun _ => M) q (fun i => v i.castSucc) := by
  funext i
  simp only [← tupleInsert_eq, tupleInsert, Fin.val_castSucc, Fin.ext_iff]
  split_ifs <;> rfl

lemma last_insert {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1)) (q : M) :
    (r.castSucc.insertNth (α := fun _ => M) q v) (Fin.last (n+1)) = v (Fin.last n) := by
  rw [tupleInsert_gt _ _ _ _ (by simp only [Fin.val_castSucc,Fin.val_last]; omega)]
  rfl
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
open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

variable [CompleteSpace X]

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : M →⋆ₐ[ℂ] (H →L[ℂ] H))

lemma coefficient_norm (η ξ : H) : ‖coefficient π η ξ‖ ≤ ‖η‖*‖ξ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro a
  calc
    _ ≤ ‖η‖*‖π a ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖η‖*(‖π a‖*‖ξ‖) := by gcongr; exact (π a).le_opNorm ξ
    _ ≤ ‖η‖*(‖a‖*‖ξ‖) := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le π a
    _ = _ := by ring

lemma projection_commutes (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (T : H →L[ℂ] H)
    (hT : ∀ ξ ∈ K, T ξ ∈ K) (hTstar : ∀ ξ ∈ K, star T ξ ∈ K) :
    K.starProjection*T=T*K.starProjection := by
  ext ξ
  change K.starProjection (T ξ)=T (K.starProjection ξ)
  apply Submodule.eq_starProjection_of_mem_orthogonal (hT _ (by simp))
  intro η hη
  change ⟪η,T ξ-T (K.starProjection ξ)⟫_ℂ=0
  rw [← map_sub]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact K.sub_starProjection_mem_orthogonal ξ _ (hTstar η hη)

lemma normalProjection_mul (a : M) :
    normalProjection e π*π a=π a*normalProjection e π := by
  apply projection_commutes
  · intro ξ hξ; exact normalVectors_mul e π hξ a
  · intro ξ hξ
    rw [← map_star]
    exact normalVectors_mul e π hξ (star a)

end HochschildNormalPart

open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v w
variable {M : Type u} [CStarAlgebra M]
variable {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma coefficient_sum (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (η ξ : WithLp 2 (H×K)) :
    coefficient (sumRepresentation π ρ) η ξ=
      coefficient π η.fst ξ.fst+coefficient ρ η.snd ξ.snd := by
  ext a; rfl

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K))

lemma coefficient_normal_eq_of_eq
    (η ξ : H) (ζ ω : K) (h : coefficient π η ξ=coefficient ρ ζ ω) :
    coefficient π η (normalProjection e π ξ)=coefficient ρ ζ (normalProjection e ρ ω) := by
  let A : WithLp 2 (H×K) := WithLp.toLp 2 (η,ζ)
  let B : WithLp 2 (H×K) := WithLp.toLp 2 (ξ,-ω)
  have hz : coefficient (sumRepresentation π ρ) A B=0 := by
    rw [coefficient_sum]
    change coefficient π η ξ+coefficient ρ ζ (-ω)=0
    rw [map_neg,h,add_neg_cancel]
  have hn : coefficient (sumRepresentation π ρ) A B ∈ normalDual e := hz ▸ (normalDual e).zero_mem
  have hp := normalProjection_fixes_normal e (sumRepresentation π ρ) A B hn
  rw [hz,normalProjection_sum,coefficient_sum] at hp
  change coefficient π η (normalProjection e π ξ)+coefficient ρ ζ (normalProjection e ρ (-ω))=0 at hp
  rw [map_neg,map_neg] at hp
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hp)
end HochschildNormalPart
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

variable {M : Type*} [CStarAlgebra M]

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
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
namespace HochschildNormalPart
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

attribute [instance] FunctionalModel.normed FunctionalModel.innerSpace FunctionalModel.complete

end HochschildNormalPart

namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def functionalModel (φ : StrongDual ℂ M) : FunctionalModel φ := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  exact Classical.choice (functionalModel_nonempty φ)

def normalPartRaw (φ : StrongDual ℂ M) : StrongDual ℂ M :=
  coefficient (functionalModel φ).representation (functionalModel φ).leftVector
    (normalProjection e (functionalModel φ).representation (functionalModel φ).rightVector)

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma normalPartRaw_coefficient (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    normalPartRaw e (coefficient π η ξ)=coefficient π η (normalProjection e π ξ) := by
  exact coefficient_normal_eq_of_eq e _ π _ _ η ξ (functionalModel _).realizes

lemma normalPartRaw_add (φ ψ : StrongDual ℂ M) :
    normalPartRaw e (φ+ψ)=normalPartRaw e φ+normalPartRaw e ψ := by
  let m := functionalModel φ
  let n := functionalModel ψ
  let π := sumRepresentation m.representation n.representation
  let η : WithLp 2 (m.H×n.H) := WithLp.toLp 2 (m.leftVector,n.leftVector)
  let ξ : WithLp 2 (m.H×n.H) := WithLp.toLp 2 (m.rightVector,n.rightVector)
  have hc : coefficient π η ξ=φ+ψ := by
    rw [coefficient_sum]
    change coefficient m.representation m.leftVector m.rightVector+
      coefficient n.representation n.leftVector n.rightVector=φ+ψ
    rw [m.realizes,n.realizes]
  rw [← hc,normalPartRaw_coefficient,normalProjection_sum,coefficient_sum]
  rfl

lemma normalPartRaw_smul (r : ℂ) (φ : StrongDual ℂ M) :
    normalPartRaw e (r • φ)=r • normalPartRaw e φ := by
  let m := functionalModel φ
  have hc : coefficient m.representation m.leftVector (r • m.rightVector)=r • φ := by
    rw [map_smul,m.realizes]
  rw [← hc,normalPartRaw_coefficient,map_smul,map_smul]
  rfl

lemma normalPartRaw_norm (φ : StrongDual ℂ M) : ‖normalPartRaw e φ‖≤4*‖φ‖ := by
  let m := functionalModel φ
  exact (coefficient_norm _ _ _).trans
    ((mul_le_mul_of_nonneg_left ((normalVectors e m.representation).norm_starProjection_apply_le _)
      (norm_nonneg m.leftVector)).trans m.bound)

def scalarNormalPart : StrongDual ℂ M →L[ℂ] StrongDual ℂ M :=
  LinearMap.mkContinuous
    { toFun := normalPartRaw e
      map_add' := normalPartRaw_add e
      map_smul' := normalPartRaw_smul e } 4 (normalPartRaw_norm e)

@[simp] lemma scalarNormalPart_coefficient (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    scalarNormalPart e (coefficient π η ξ)=coefficient π η (normalProjection e π ξ) :=
  normalPartRaw_coefficient e π η ξ

lemma scalarNormalPart_norm : ‖scalarNormalPart e‖≤4 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) (normalPartRaw_norm e)

lemma scalarNormalPart_mem (φ : StrongDual ℂ M) : scalarNormalPart e φ ∈ normalDual e := by
  apply (mem_normalVectors e (functionalModel φ).representation _).mp
  simp [normalProjection]

lemma scalarNormalPart_fixes {φ : StrongDual ℂ M} (hφ : φ ∈ normalDual e) :
    scalarNormalPart e φ=φ := by
  let m := functionalModel φ
  change coefficient m.representation m.leftVector (normalProjection e m.representation m.rightVector)=φ
  rw [normalProjection_fixes_normal e _ _ _ (m.realizes.symm ▸ hφ),m.realizes]

lemma scalarNormalPart_comp_left (φ : StrongDual ℂ M) (b : M) :
    scalarNormalPart e (φ.comp (ContinuousLinearMap.mul ℂ M b))=
      (scalarNormalPart e φ).comp (ContinuousLinearMap.mul ℂ M b) := by
  let m := functionalModel φ
  have hc (ξ : m.H) : (coefficient m.representation m.leftVector ξ).comp
      (ContinuousLinearMap.mul ℂ M b)=coefficient m.representation (m.representation (star b) m.leftVector) ξ := by
    ext a
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.mul_apply',coefficient_apply,
      map_mul,mul_apply_eq_comp,map_star,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  rw [← m.realizes,hc,scalarNormalPart_coefficient,scalarNormalPart_coefficient,hc]

lemma scalarNormalPart_comp_right (φ : StrongDual ℂ M) (b : M) :
    scalarNormalPart e (φ.comp ((ContinuousLinearMap.mul ℂ M).flip b))=
      (scalarNormalPart e φ).comp ((ContinuousLinearMap.mul ℂ M).flip b) := by
  let m := functionalModel φ
  have hc (ξ : m.H) : (coefficient m.representation m.leftVector ξ).comp
      ((ContinuousLinearMap.mul ℂ M).flip b)=coefficient m.representation m.leftVector (m.representation b ξ) := by
    ext a
    simp [map_mul]
  rw [← m.realizes,hc,scalarNormalPart_coefficient,scalarNormalPart_coefficient,hc]
  exact congrArg (coefficient m.representation m.leftVector)
    (congrArg (fun T : m.H →L[ℂ] m.H => T m.rightVector) (normalProjection_mul e m.representation b))

end HochschildNormalPart

namespace HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

omit [CompleteSpace X] in
lemma predual_separates {a b : M}
    (h : ∀ z,predualEmbedding e z a=predualEmbedding e z b) : a=b := by
  apply e.symm.injective
  ext z
  exact star_injective (h z)

def normalPredualVector (T : M →L[ℂ] M) (z : X) : X :=
  Classical.choose ((mem_normalDual e _).mp (scalarNormalPart_mem e ((predualEmbedding e z).comp T)))

lemma normalPredualVector_spec (T : M →L[ℂ] M) (z : X) :
    predualEmbedding e (normalPredualVector e T z)=
      scalarNormalPart e ((predualEmbedding e z).comp T) := by
  ext a
  exact (Classical.choose_spec ((mem_normalDual e _).mp
    (scalarNormalPart_mem e ((predualEmbedding e z).comp T))) a).symm

lemma normalPredualVector_add (T : M →L[ℂ] M) (z w : X) :
    normalPredualVector e T (z+w)=normalPredualVector e T z+normalPredualVector e T w := by
  apply (predualEmbedding e).injective
  simp only [normalPredualVector_spec,map_add,ContinuousLinearMap.add_comp]

lemma normalPredualVector_smul (T : M →L[ℂ] M) (c : ℂ) (z : X) :
    normalPredualVector e T (c • z)=c • normalPredualVector e T z := by
  apply (predualEmbedding e).injective
  simp only [normalPredualVector_spec,map_smulₛₗ,ContinuousLinearMap.smul_comp,RingHom.id_apply]

lemma normalPredualVector_norm (T : M →L[ℂ] M) (z : X) :
    ‖normalPredualVector e T z‖≤(4*‖T‖)*‖z‖ := by
  rw [← (predualEmbedding e).norm_map,normalPredualVector_spec]
  calc
    _ ≤ 4*‖(predualEmbedding e z).comp T‖ := (scalarNormalPart e).le_of_opNorm_le (scalarNormalPart_norm e) _
    _ ≤ 4*(‖predualEmbedding e z‖*‖T‖) := by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = (4*‖T‖)*‖z‖ := by rw [(predualEmbedding e).norm_map]; ring

def normalPreadjoint (T : M →L[ℂ] M) : X →L[ℂ] X :=
  LinearMap.mkContinuous
    { toFun := normalPredualVector e T
      map_add' := normalPredualVector_add e T
      map_smul' := normalPredualVector_smul e T } (4*‖T‖) (normalPredualVector_norm e T)

def normalOperator (T : M →L[ℂ] M) : M →L[ℂ] M :=
  e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((ContinuousLinearMap.compL ℂ X X ℂ).flip (normalPreadjoint e T)).comp
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap)

lemma normalOperator_pairing (T : M →L[ℂ] M) (a : M) (z : X) :
    predualEmbedding e z (normalOperator e T a)=
      scalarNormalPart e ((predualEmbedding e z).comp T) a := by
  rw [← normalPredualVector_spec]
  simp [normalOperator,normalPreadjoint,predualEmbedding_apply]

lemma normalOperator_normal (T : M →L[ℂ] M) : BoundedHochschild.HasPreadjoint e (normalOperator e T) := by
  intro z
  refine ⟨normalPreadjoint e T z,?_⟩
  intro a
  simp [normalOperator]

lemma normalOperator_add (S T : M →L[ℂ] M) : normalOperator e (S+T)=normalOperator e S+normalOperator e T := by
  ext a
  apply predual_separates e
  intro z
  simp only [normalOperator_pairing,ContinuousLinearMap.comp_add,map_add,add_apply]

lemma normalOperator_smul (c : ℂ) (T : M →L[ℂ] M) : normalOperator e (c • T)=c • normalOperator e T := by
  ext a
  apply predual_separates e
  intro z
  simp only [normalOperator_pairing,ContinuousLinearMap.comp_smul,map_smul,smul_apply]

lemma normalOperator_norm (T : M →L[ℂ] M) : ‖normalOperator e T‖≤4*‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  rw [← e.symm.norm_map]
  change ‖e.symm (e ((e.symm a).comp (normalPreadjoint e T)))‖≤_
  rw [e.symm_apply_apply]
  calc
    _ ≤ ‖normalPreadjoint e T‖*‖e.symm a‖ := by
      simpa only [mul_comm] using (ContinuousLinearMap.opNorm_comp_le (e.symm a) (normalPreadjoint e T))
    _ ≤ (4*‖T‖)*‖a‖ := by
      rw [e.symm.norm_map]
      gcongr
      exact LinearMap.mkContinuous_norm_le _ (by positivity) (normalPredualVector_norm e T)

def operatorNormalPart : (M →L[ℂ] M) →L[ℂ] (M →L[ℂ] M) :=
  LinearMap.mkContinuous
    { toFun := normalOperator e
      map_add' := normalOperator_add e
      map_smul' := normalOperator_smul e } 4 (normalOperator_norm e)

lemma operatorNormalPart_pairing (T : M →L[ℂ] M) (a : M) (z : X) :
    predualEmbedding e z (operatorNormalPart e T a)=
      scalarNormalPart e ((predualEmbedding e z).comp T) a := normalOperator_pairing e T a z

lemma operatorNormalPart_normal (T : M →L[ℂ] M) :
    BoundedHochschild.HasPreadjoint e (operatorNormalPart e T) := normalOperator_normal e T

lemma operatorNormalPart_fixes (T : M →L[ℂ] M) (hT : BoundedHochschild.HasPreadjoint e T) :
    operatorNormalPart e T=T := by
  ext a
  apply predual_separates e
  intro z
  rw [operatorNormalPart_pairing]
  have hn : (predualEmbedding e z).comp T ∈ normalDual e :=
    normalDual_comp e (φ := predualEmbedding e z) ⟨z,rfl⟩ T hT
  exact congrArg (fun φ : StrongDual ℂ M => φ a) (scalarNormalPart_fixes e hn)

lemma operatorNormalPart_comp_normal (T L : M →L[ℂ] M)
    (hL : BoundedHochschild.HasPreadjoint e L) :
    operatorNormalPart e (L.comp T)=L.comp (operatorNormalPart e T) := by
  ext a
  apply predual_separates e
  intro z
  obtain ⟨w,hw⟩ := hL z
  have he : (predualEmbedding e z).comp L=predualEmbedding e w := by
    ext b
    simp only [ContinuousLinearMap.comp_apply,predualEmbedding_apply,hw]
  rw [operatorNormalPart_pairing,← ContinuousLinearMap.comp_assoc,he]
  change _=predualEmbedding e z (L (operatorNormalPart e T a))
  rw [← ContinuousLinearMap.comp_apply (predualEmbedding e z) L,he,operatorNormalPart_pairing]

lemma operatorNormalPart_comp_left (T : M →L[ℂ] M) (b : M) :
    operatorNormalPart e (T.comp (ContinuousLinearMap.mul ℂ M b))=
      (operatorNormalPart e T).comp (ContinuousLinearMap.mul ℂ M b) := by
  ext a
  apply predual_separates e
  intro z
  rw [operatorNormalPart_pairing,← ContinuousLinearMap.comp_assoc,scalarNormalPart_comp_left]
  exact (operatorNormalPart_pairing e T (b*a) z).symm

lemma operatorNormalPart_comp_right (T : M →L[ℂ] M) (b : M) :
    operatorNormalPart e (T.comp ((ContinuousLinearMap.mul ℂ M).flip b))=
      (operatorNormalPart e T).comp ((ContinuousLinearMap.mul ℂ M).flip b) := by
  ext a
  apply predual_separates e
  intro z
  rw [operatorNormalPart_pairing,← ContinuousLinearMap.comp_assoc,scalarNormalPart_comp_right]
  exact (operatorNormalPart_pairing e T (a*b) z).symm
end HochschildNormalPart
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
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def normalLast {n : ℕ} (f : Cochain M (n+1)) : Cochain M (n+1) :=
  ((operatorNormalPart e).compContinuousMultilinearMap f.curryRight).uncurryRight

@[simp] lemma normalLast_apply {n : ℕ} (f : Cochain M (n+1)) (v : Fin (n+1) → M) :
    normalLast e f v=operatorNormalPart e (f.curryRight (fun i => v i.castSucc)) (v (Fin.last n)) := rfl

@[simp] lemma normalLast_snoc {n : ℕ} (f : Cochain M (n+1)) (v : Fin n → M) (a : M) :
    normalLast e f (Fin.snoc v a)=operatorNormalPart e (f.curryRight v) a := by
  simp

lemma sign_succ (k : ℕ) : (-1:ℂ)^(k+1) = -((-1:ℂ)^k) := by
  rw [pow_succ]
  ring

lemma differentialValue_sub {n : ℕ} (f g : Cochain M n) (v : Fin (n+1) → M) :
    differentialValue (f-g) v=differentialValue f v-differentialValue g v := by
  rw [sub_eq_add_neg,show -g=(-1:ℂ) • g by simp,differentialValue_add,differentialValue_smul]
  simp [sub_eq_add_neg]

end BoundedHochschild

namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def reverseArguments {n : ℕ} (f : Cochain M n) : Cochain M n :=
  ContinuousMultilinearMap.domDomCongr Fin.revPerm f

lemma reverseArguments_apply {n : ℕ} (f : Cochain M n) (v : Fin n → M) :
    reverseArguments f v=f (v ∘ Fin.rev) := rfl

@[simp] lemma reverseArguments_norm {n : ℕ} (f : Cochain M n) : ‖reverseArguments f‖=‖f‖ :=
  ContinuousMultilinearMap.norm_domDomCongr ℂ M M _ _

def firstSliceN {n : ℕ} (f : Cochain M (n+1)) (v : Fin n → M) : M →L[ℂ] M :=
  (reverseArguments f).curryRight (v ∘ Fin.rev)

@[simp] lemma firstSliceN_apply {n : ℕ} (f : Cochain M (n+1)) (v : Fin n → M) (a : M) :
    firstSliceN f v a=f (Fin.cons a v) := by
  change reverseArguments f (Fin.snoc (v ∘ Fin.rev) a)=_
  rw [reverseArguments_apply,Fin.snoc_comp_rev]
  have hv : (v ∘ Fin.rev) ∘ Fin.rev=v := by
    ext i
    simp
  rw [hv]

def normalFirst {n : ℕ} (f : Cochain M (n+1)) : Cochain M (n+1) :=
  reverseArguments (normalLast e (reverseArguments f))

@[simp] lemma normalFirst_cons {n : ℕ} (f : Cochain M (n+1)) (a : M) (v : Fin n → M) :
    normalFirst e f (Fin.cons a v)=operatorNormalPart e (firstSliceN f v) a := by
  rw [normalFirst,reverseArguments_apply,Fin.cons_comp_rev,normalLast_snoc]
  rfl

lemma normalFirst_normal {n : ℕ} (f : Cochain M (n+1)) (v : Fin n → M) :
    HasPreadjoint e (firstSliceN (normalFirst e f) v) := by
  have he : firstSliceN (normalFirst e f) v=operatorNormalPart e (firstSliceN f v) := by
    ext a
    simp
  rw [he]
  exact operatorNormalPart_normal e _

lemma differentialValue_cons {n : ℕ} (f : Cochain M (n+1))
    (a : M) (v : Fin (n+1) → M) :
    differentialValue f (Fin.cons a v)=a*f v-f (Fin.cons (a*v 0) (fun i : Fin n => v i.succ))+
      (∑ j : Fin n,((-1:ℂ)^(j.val+2)) • f (Fin.cons a (mergeInputs v j)))+
      ((-1:ℂ)^(n+2)) • (f (Fin.cons a (fun i : Fin n => v i.castSucc))*v (Fin.last n)) := by
  have hinit : (fun i : Fin (n+1) => (Fin.cons a v : Fin (n+2) → M) i.castSucc)=
      Fin.cons a (fun i : Fin n => v i.castSucc) := by
    ext i; refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.castSucc_succ,Fin.cons_succ]
  have hlast : (Fin.cons a v : Fin (n+2) → M) (Fin.last (n+1))=v (Fin.last n) := by
    change (Fin.cons a v : Fin (n+2) → M) (Fin.last n).succ=_
    simp
  simp only [differentialValue,Fin.cons_zero,Fin.cons_succ,hinit,hlast,
    Fin.sum_univ_succ,mergeInputs_cons_zero,mergeInputs_cons_succ,
    Fin.val_zero,zero_add,pow_one,neg_smul,one_smul,Fin.val_succ,Nat.add_assoc]
  abel

lemma normalFirst_identity {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ z,differentialValue f z=0) (a : M) (v : Fin (n+1) → M) :
    a*f v-normalFirst e f (Fin.cons (a*v 0) (fun i : Fin n => v i.succ))+
      (∑ j : Fin n,((-1:ℂ)^(j.val+2)) • normalFirst e f (Fin.cons a (mergeInputs v j)))+
      ((-1:ℂ)^(n+2)) • (normalFirst e f (Fin.cons a (fun i : Fin n => v i.castSucc))*v (Fin.last n))=0 := by
  let R := (ContinuousLinearMap.mul ℂ M).flip
  have hop : R (f v)-(firstSliceN f (fun i : Fin n => v i.succ)).comp (R (v 0))+
      (∑ j : Fin n,((-1:ℂ)^(j.val+2)) • firstSliceN f (mergeInputs v j))+
      ((-1:ℂ)^(n+2)) • (R (v (Fin.last n))).comp (firstSliceN f (fun i : Fin n => v i.castSucc))=0 := by
    ext b
    simpa only [R,sub_apply,add_apply,sum_apply,smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply,ContinuousLinearMap.mul_apply',firstSliceN_apply,zero_apply,
      differentialValue_cons] using hf (Fin.cons b v)
  have h := congrArg (fun T : M →L[ℂ] M => operatorNormalPart e T a) hop
  dsimp only [R] at h
  simp only [map_sub,map_add,map_sum,map_smul,map_zero,sub_apply,add_apply,sum_apply,smul_apply,zero_apply,
    operatorNormalPart_fixes e _ ((HochschildSakai.abstract_multiplication_normal e).2 _),
    operatorNormalPart_comp_right,operatorNormalPart_comp_normal e _ _
      ((HochschildSakai.abstract_multiplication_normal e).2 _),
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply',← normalFirst_cons] at h
  exact h

def firstNormalCorrectionN {n : ℕ} (f : Cochain M (n+1)) : Cochain M n :=
  (normalFirst e f).curryLeft 1

def firstNormalRemainderN {n : ℕ} (f : Cochain M (n+1)) : Cochain M (n+1) :=
  f-differential (firstNormalCorrectionN e f)

@[simp] lemma firstNormalCorrectionN_apply {n : ℕ} (f : Cochain M (n+1)) (v : Fin n → M) :
    firstNormalCorrectionN e f v=normalFirst e f (Fin.cons 1 v) := rfl

lemma firstNormalRemainderN_apply {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ z,differentialValue f z=0) (v : Fin (n+1) → M) :
    firstNormalRemainderN e f v=normalFirst e f v-
      v 0*normalFirst e f (Fin.cons 1 (fun i : Fin n => v i.succ)) := by
  have h := normalFirst_identity e f hf 1 v
  have hv : Fin.cons (v 0) (fun i : Fin n => v i.succ)=v := Fin.cons_self_tail v
  simp only [one_mul,hv] at h
  simp only [firstNormalRemainderN,sub_apply,differential_apply,differentialValue,
    firstNormalCorrectionN_apply]
  have hsign (j : Fin n) : (-1:ℂ)^(j.val+2) = -((-1:ℂ)^(j.val+1)) := sign_succ _
  rw [sign_succ (n+1)] at h
  simp only [hsign,neg_smul,Finset.sum_neg_distrib] at h
  linear_combination (norm := module) h

lemma firstNormalRemainderN_cocycle {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ z,differentialValue f z=0) (z : Fin (n+2) → M) :
    differentialValue (firstNormalRemainderN e f) z=0 := by
  rw [firstNormalRemainderN,differentialValue_sub,hf,differential_is_cocycle,sub_self]

lemma firstNormalRemainderN_identity {n : ℕ} (f : Cochain M (n+1)) (v : Fin (n+1) → M) :
    f v=firstNormalRemainderN e f v+differentialValue (firstNormalCorrectionN e f) v := by
  simp only [firstNormalRemainderN,sub_apply,differential_apply,sub_add_cancel]
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

def hilbertNormalFunctional (T : M →L[ℂ] H) (a : M) : StrongDual ℂ H :=
  LinearMap.mkContinuous
    { toFun := fun η => star (scalarNormalPart e ((innerSL ℂ η).comp T) a)
      map_add' := by
        intro η ξ
        simp only [map_add,ContinuousLinearMap.add_comp,add_apply,star_add]
      map_smul' := by
        intro c η
        have hη : (innerSL ℂ (c • η)).comp T = star c • (innerSL ℂ η).comp T := by
          ext b
          change ⟪c • η,T b⟫_ℂ=star c*⟪η,T b⟫_ℂ
          simp only [inner_smul_left,starRingEnd_apply]
        change star (scalarNormalPart e ((innerSL ℂ (c • η)).comp T) a) =
          c • star (scalarNormalPart e ((innerSL ℂ η).comp T) a)
        rw [hη,map_smul,smul_apply,star_smul,star_star] }
    (4*‖T‖*‖a‖) (by
      intro η
      have hP := (scalarNormalPart e).le_opNorm ((innerSL ℂ η).comp T)
      have hT := ContinuousLinearMap.opNorm_comp_le (innerSL ℂ η) T
      have h := (scalarNormalPart e ((innerSL ℂ η).comp T)).le_opNorm a
      change ‖star (scalarNormalPart e ((innerSL ℂ η).comp T) a)‖ ≤ _
      rw [norm_star]
      calc
        _ ≤ ‖scalarNormalPart e ((innerSL ℂ η).comp T)‖*‖a‖ := h
        _ ≤ (4*(‖η‖*‖T‖))*‖a‖ := by
          gcongr
          exact hP.trans (mul_le_mul (scalarNormalPart_norm e)
            (by simpa only [innerSL_apply_norm] using hT) (norm_nonneg _) (by norm_num))
        _ = (4*‖T‖*‖a‖)*‖η‖ := by ring)

omit [CompleteSpace H] in
@[simp] lemma hilbertNormalFunctional_apply (T : M →L[ℂ] H) (a : M) (η : H) :
    hilbertNormalFunctional e T a η =
      star (scalarNormalPart e ((innerSL ℂ η).comp T) a) := rfl

def hilbertNormalValue (T : M →L[ℂ] H) (a : M) : H :=
  (InnerProductSpace.toDual ℂ H).symm (hilbertNormalFunctional e T a)

lemma hilbertNormalValue_inner (T : M →L[ℂ] H) (a : M) (η : H) :
    ⟪η,hilbertNormalValue e T a⟫_ℂ =
      scalarNormalPart e ((innerSL ℂ η).comp T) a := by
  have h := (InnerProductSpace.toDual ℂ H).apply_symm_apply (hilbertNormalFunctional e T a)
  have h' := congrArg (fun φ : StrongDual ℂ H => φ η) h
  change ⟪hilbertNormalValue e T a,η⟫_ℂ = _ at h'
  rw [hilbertNormalFunctional_apply] at h'
  apply star_injective
  simpa only [← starRingEnd_apply,inner_conj_symm] using h'

lemma hilbertNormalValue_add (T : M →L[ℂ] H) (a b : M) :
    hilbertNormalValue e T (a+b)=hilbertNormalValue e T a+hilbertNormalValue e T b := by
  apply ext_inner_left ℂ
  intro η
  simp only [inner_add_right,hilbertNormalValue_inner,map_add]

lemma hilbertNormalValue_smul (T : M →L[ℂ] H) (c : ℂ) (a : M) :
    hilbertNormalValue e T (c • a)=c • hilbertNormalValue e T a := by
  apply ext_inner_left ℂ
  intro η
  simp only [inner_smul_right,hilbertNormalValue_inner,map_smul,smul_eq_mul]

lemma hilbertNormalValue_norm (T : M →L[ℂ] H) (a : M) :
    ‖hilbertNormalValue e T a‖≤4*‖T‖*‖a‖ := by
  rw [hilbertNormalValue,LinearIsometryEquiv.norm_map]
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

def hilbertNormalPart (T : M →L[ℂ] H) : M →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := hilbertNormalValue e T
      map_add' := hilbertNormalValue_add e T
      map_smul' := hilbertNormalValue_smul e T }
    (4*‖T‖) (hilbertNormalValue_norm e T)

lemma hilbertNormalPart_inner (T : M →L[ℂ] H) (a : M) (η : H) :
    ⟪η,hilbertNormalPart e T a⟫_ℂ =
      scalarNormalPart e ((innerSL ℂ η).comp T) a := hilbertNormalValue_inner e T a η

lemma hilbertNormalPart_pairing (T : M →L[ℂ] H) (a : M) (φ : StrongDual ℂ H) :
    φ (hilbertNormalPart e T a)=scalarNormalPart e (φ.comp T) a := by
  let η := (InnerProductSpace.toDual ℂ H).symm φ
  have hη : innerSL ℂ η=φ := (InnerProductSpace.toDual ℂ H).apply_symm_apply φ
  rw [← hη]
  change ⟪η,hilbertNormalPart e T a⟫_ℂ = _
  exact hilbertNormalPart_inner e T a η

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

lemma firstNormalRemainderN_one {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v,differentialValue f v=0) (v : Fin n → M) :
    firstNormalRemainderN e f (Fin.cons 1 v)=0 := by
  rw [firstNormalRemainderN_apply e f hf]
  simp only [Fin.cons_zero,Fin.cons_succ,one_mul,sub_self]

end BoundedHochschild

namespace BoundedHochschild
open HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

omit [CompleteSpace X] in
lemma HasPreadjoint.sub {S T : M →L[ℂ] M}
    (hS : HasPreadjoint e S) (hT : HasPreadjoint e T) : HasPreadjoint e (S-T) := by
  intro z
  obtain ⟨w,hw⟩ := hS z
  obtain ⟨y,hy⟩ := hT z
  refine ⟨w-y,fun a => ?_⟩
  simp only [sub_apply,map_sub,hw,hy]

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

def normalAt {n : ℕ} (f : Cochain M (n+1)) (i : Fin (n+1)) : Cochain M (n+1) :=
  (((operatorNormalPart e).compContinuousMultilinearMap
    (f.curryMid i).flipMultilinear).flipLinear).uncurryMid i

@[simp] lemma normalAt_insert {n : ℕ} (f : Cochain M (n+1)) (i : Fin (n+1))
    (v : Fin n → M) (a : M) :
    normalAt e f i (i.insertNth a v)=operatorNormalPart e (sliceAt f i v) a := by
  change (((normalAt e f i).curryMid i) a) v=_
  rw [normalAt,ContinuousLinearMap.curryMid_uncurryMid]
  rfl

lemma normalAt_normal {n : ℕ} (f : Cochain M (n+1)) (i : Fin (n+1))
    (v : Fin n → M) : HasPreadjoint e (sliceAt (normalAt e f i) i v) := by
  have heq : sliceAt (normalAt e f i) i v=operatorNormalPart e (sliceAt f i v) := by
    ext a
    exact normalAt_insert e f i v a
  rw [heq]
  exact operatorNormalPart_normal e _

def slotInsertion {n : ℕ} (f : Cochain M (n+1)) (i : Fin (n+1)) : Cochain M n :=
  (normalAt e f i).curryMid i 1

@[simp] lemma slotInsertion_apply {n : ℕ} (f : Cochain M (n+1)) (i : Fin (n+1))
    (v : Fin n → M) :
    slotInsertion e f i v=operatorNormalPart e (sliceAt f i v) 1 := normalAt_insert e f i v 1

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

lemma sliceAt_right {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (v : Fin (n+1) → M) :
    sliceAt (rightCoboundary f) r.castSucc v=
      ((ContinuousLinearMap.mul ℂ M).flip (v (Fin.last n))).comp
        (sliceAt f r (fun i => v i.castSucc)) := by
  ext a
  simp only [sliceAt_apply,rightCoboundary_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.mul_apply']
  rw [init_insert,last_insert]

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

lemma projected_left_zero {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (hr : 0<r.val) (hN : NormalBefore e f r.val) (hU : UnitZeroBefore f r.val)
    (v : Fin (n+1) → M) :
    operatorNormalPart e (sliceAt (leftCoboundary f) r.castSucc v) 1=0 := by
  rw [sliceAt_left f r hr v,operatorNormalPart_comp_normal e _ _
    ((HochschildSakai.abstract_multiplication_normal e).1 _),
    operatorNormalPart_fixes e _ (hN _ (by dsimp; omega) _)]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.mul_apply',sliceAt_apply]
  rw [hU _ (by dsimp; omega),mul_zero]

lemma projected_middle_before_zero {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (hN : NormalBefore e f r.val) (hU : UnitZeroBefore f r.val)
    (j : Fin n) (hjr : j.val+1<r.val) (v : Fin (n+1) → M) :
    operatorNormalPart e (sliceAt (middleCoboundary f (r.succAbove j)) r.castSucc v) 1=0 := by
  rw [sliceAt_middle_before f r j hjr v,
    operatorNormalPart_fixes e _ (hN _ (by dsimp; omega) _),sliceAt_apply]
  exact hU _ (by dsimp; omega) _

lemma projected_middle_boundary {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (hN : NormalBefore e f r.val)
    (j : Fin n) (hjr : j.val+1=r.val) (v : Fin (n+1) → M) :
    operatorNormalPart e (sliceAt (middleCoboundary f (r.succAbove j)) r.castSucc v) 1=f v := by
  rw [sliceAt_middle_before_boundary f r j hjr v,operatorNormalPart_fixes e _
    ((hN j.castSucc (by simp only [Fin.val_castSucc]; omega) _).comp e
      ((HochschildSakai.abstract_multiplication_normal e).1 _))]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.mul_apply',mul_one,
    sliceAt_apply,Fin.insertNth_self_removeNth]

lemma projected_middle_same {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (v : Fin (n+1) → M) :
    operatorNormalPart e (sliceAt (middleCoboundary f r) r.castSucc v) 1=normalAt e f r v := by
  rw [sliceAt_middle_same,operatorNormalPart_comp_right]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply',one_mul]
  rw [← normalAt_insert,Fin.insertNth_self_removeNth]

lemma projected_middle_after {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (j : Fin n) (hjr : r.val≤j.val) (v : Fin (n+1) → M) :
    operatorNormalPart e (sliceAt (middleCoboundary f (r.succAbove j)) r.castSucc v) 1=
      slotInsertion e f r (mergeInputs v j) := by
  rw [sliceAt_middle_after f r j hjr v,slotInsertion_apply]

lemma projected_right {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (v : Fin (n+1) → M) :
    operatorNormalPart e (sliceAt (rightCoboundary f) r.castSucc v) 1=
      slotInsertion e f r (fun i => v i.castSucc)*v (Fin.last n) := by
  rw [sliceAt_right,operatorNormalPart_comp_normal e _ _
    ((HochschildSakai.abstract_multiplication_normal e).2 _)]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply',slotInsertion_apply]

lemma projected_middle_sum {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (hr : 0<r.val) (hN : NormalBefore e f r.val) (hU : UnitZeroBefore f r.val)
    (v : Fin (n+1) → M) :
    (∑ j : Fin (n+1),((-1:ℂ)^(j.val+1)) •
      operatorNormalPart e (sliceAt (middleCoboundary f j) r.castSucc v) 1)=
    ((-1:ℂ)^(r.val+1)) • normalAt e f r v + ((-1:ℂ)^r.val) • f v +
      ∑ j : Fin n,if r.val≤j.val then
        ((-1:ℂ)^(j.val+2)) • slotInsertion e f r (mergeInputs v j) else 0 := by
  rw [Fin.sum_univ_succAbove _ r,projected_middle_same]
  let b : Fin n := ⟨r.val-1,by omega⟩
  have hj (j : Fin n) :
      ((-1:ℂ)^((r.succAbove j).val+1)) •
        operatorNormalPart e (sliceAt (middleCoboundary f (r.succAbove j)) r.castSucc v) 1=
      (if j=b then ((-1:ℂ)^r.val) • f v else 0) +
      (if r.val≤j.val then ((-1:ℂ)^(j.val+2)) • slotInsertion e f r (mergeInputs v j) else 0) := by
    rcases lt_trichotomy (j.val+1) r.val with h|h|h
    · rw [projected_middle_before_zero e f r hN hU j h v]
      have hb : j≠b := by intro he; have := congrArg Fin.val he; dsimp [b] at this; omega
      simp only [hb,ite_false,show ¬r.val≤j.val by omega,smul_zero,add_zero]
    · have he : j=b := Fin.ext (by dsimp [b]; omega)
      have hs : r.succAbove j=j.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def,Fin.val_castSucc]; omega)
      rw [projected_middle_boundary e f r hN j h v,hs]
      simp only [Fin.val_castSucc]
      rw [h]
      simp only [he,ite_true,show ¬r.val≤b.val by dsimp [b]; omega,ite_false,add_zero]
    · have hle : r.val≤j.val := by omega
      have hb : j≠b := by intro he; have := congrArg Fin.val he; dsimp [b] at this; omega
      have hs : r.succAbove j=j.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simpa only [Fin.le_def,Fin.val_castSucc] using hle)
      rw [projected_middle_after e f r j hle v,hs]
      simp only [Fin.val_succ,hb,ite_false,hle,ite_true,zero_add]
  simp_rw [hj]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  abel

lemma slot_cocycle_identity {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (hr : 0<r.val) (hf : ∀ v,differentialValue f v=0)
    (hN : NormalBefore e f r.val) (hU : UnitZeroBefore f r.val)
    (v : Fin (n+1) → M) :
    ((-1:ℂ)^r.val) • f v + ((-1:ℂ)^(r.val+1)) • normalAt e f r v +
      (∑ j : Fin n,if r.val≤j.val then
        ((-1:ℂ)^(j.val+2)) • slotInsertion e f r (mergeInputs v j) else 0) +
      ((-1:ℂ)^(n+2)) •
        (slotInsertion e f r (fun i => v i.castSucc)*v (Fin.last n))=0 := by
  have hd : differential f=0 := by ext w; simpa only [differential_apply,zero_apply] using hf w
  have hp := congrArg (fun T : Cochain M (n+2) =>
    operatorNormalPart e (sliceAt T r.castSucc v) 1) hd
  simp only [differential,sliceAt_add,sliceAt_sum,sliceAt_smul,sliceAt_zero,
    map_add,map_sum,map_smul,map_zero,add_apply,sum_apply,smul_apply,zero_apply] at hp
  rw [projected_left_zero e f r hr hN hU v,projected_right,
    projected_middle_sum e f r hr hN hU v,zero_add] at hp
  convert hp using 1
  abel

def slotRemainder {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1)) : Cochain M (n+1) :=
  f-((-1:ℂ)^r.val) • differential (slotInsertion e f r)

def slotCorrection {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1)) : Cochain M n :=
  ((-1:ℂ)^r.val) • slotInsertion e f r

lemma slotRemainder_identity {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (v : Fin (n+1) → M) :
    f v=slotRemainder e f r v+differentialValue (slotCorrection e f r) v := by
  simp only [slotRemainder,slotCorrection,sub_apply,smul_apply,differential_apply,
    differentialValue_smul,sub_add_cancel]

lemma slotRemainder_cocycle {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (hf : ∀ v,differentialValue f v=0) (v : Fin (n+2) → M) :
    differentialValue (slotRemainder e f r) v=0 := by
  rw [slotRemainder,sub_eq_add_neg,← neg_one_smul ℂ (((-1:ℂ)^r.val) •_),
    differentialValue_add,differentialValue_smul,differentialValue_smul,
    hf,differential_is_cocycle,smul_zero,smul_zero,add_zero]

lemma slotRemainder_apply {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (hr : 0<r.val) (hf : ∀ v,differentialValue f v=0)
    (hN : NormalBefore e f r.val) (hU : UnitZeroBefore f r.val)
    (v : Fin (n+1) → M) :
    slotRemainder e f r v=normalAt e f r v-
      ((-1:ℂ)^r.val) • prefixDifferential (slotInsertion e f r) r.val v := by
  have h := slot_cocycle_identity e f r hr hf hN hU v
  have hm : (∑ j : Fin n,if r.val≤j.val then
        ((-1:ℂ)^(j.val+2)) • slotInsertion e f r (mergeInputs v j) else 0)=
      (∑ j : Fin n,if j.val<r.val then
        ((-1:ℂ)^(j.val+1)) • slotInsertion e f r (mergeInputs v j) else 0)-
      ∑ j : Fin n,((-1:ℂ)^(j.val+1)) • slotInsertion e f r (mergeInputs v j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val<r.val
    · simp only [hj,ite_true,show ¬r.val≤j.val by omega,ite_false,sub_self]
    · simp only [hj,ite_false,show r.val≤j.val by omega,ite_true,zero_sub,
        sign_succ (j.val+1),neg_smul]
  rw [hm,sign_succ r.val,sign_succ (n+1),neg_smul,neg_smul] at h
  have h' : ((-1:ℂ)^r.val) • (f v-normalAt e f r v)=
      differentialValue (slotInsertion e f r) v-
        prefixDifferential (slotInsertion e f r) r.val v := by
    simp only [differentialValue,prefixDifferential_apply,smul_sub]
    linear_combination (norm := module) h
  have h'' := congrArg (fun x : M => ((-1:ℂ)^r.val) • x) h'
  rw [smul_smul,← mul_pow,neg_mul_neg,one_mul,one_pow,one_smul] at h''
  simp only [smul_sub] at h''
  simp only [slotRemainder,sub_apply,smul_apply,differential_apply]
  linear_combination (norm := module) h''

end BoundedHochschild

namespace BoundedHochschild
open HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma UnitZeroBefore.apply {n : ℕ} {f : Cochain M (n+1)} {r : ℕ}
    (hU : UnitZeroBefore f r) (v : Fin (n+1) → M) (i : Fin (n+1))
    (hi : i.val<r) (hv : v i=1) : f v=0 := by
  rw [← Fin.insertNth_self_removeNth i v,hv]
  exact hU i hi _

lemma normalAt_preserves_unitZero {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (hU : UnitZeroBefore f r.val) : UnitZeroBefore (normalAt e f r) r.val := by
  intro i hi w
  let v : Fin (n+1) → M := i.insertNth (1:M) w
  have hir : i≠r := by intro hh; have := congrArg Fin.val hh; omega
  have hs : sliceAt f r (r.removeNth v)=0 := by
    ext a
    simp only [sliceAt_apply,Fin.insertNth_removeNth,zero_apply]
    apply hU.apply _ i hi
    rw [Function.update_of_ne hir]
    exact Fin.insertNth_apply_same _ _ _
  change normalAt e f r v=0
  rw [← Fin.insertNth_self_removeNth r v,normalAt_insert,hs,map_zero,zero_apply]

lemma insertion_preserves_unitZero {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (hU : UnitZeroBefore f r.val) : UnitZeroBefore (slotInsertion e f r) r.val := by
  have hN := normalAt_preserves_unitZero e f r hU
  intro i hi v
  change normalAt e f r (r.insertNth 1 (i.insertNth 1 v))=0
  apply hN.apply _ i.castSucc hi
  rw [tupleInsert_lt _ _ _ _ hi]
  exact Fin.insertNth_apply_same _ _ _

def pairSlice {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (i : Fin (n+1)) (v : Fin n → M) : M →L[ℂ] M →L[ℂ] M :=
  (((f.curryMid r).flipMultilinear).curryMid i).flipMultilinear v

@[simp] lemma pairSlice_apply {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (i : Fin (n+1)) (v : Fin n → M) (a b : M) :
    pairSlice f r i v a b=f (r.insertNth b (i.insertNth a v)) := rfl

lemma pairSlice_flip {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (i : Fin (n+1)) (v : Fin n → M) (b : M) :
    (pairSlice f r i v).flip b=
      sliceAt f (r.succAbove i) ((r.succAbove i).removeNth (r.insertNth (α := fun _ => M) b (i.insertNth (α := fun _ => M) 0 v))) := by
  ext a
  simp only [ContinuousLinearMap.flip_apply,pairSlice_apply,sliceAt_apply,Fin.insertNth_removeNth]
  rw [← Fin.insertNth_update,Fin.update_insertNth]

lemma normalAt_pairSlice {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (i : Fin (n+1)) (v : Fin n → M) :
    pairSlice (normalAt e f r) r i v=(operatorNormalPart e).comp (pairSlice f r i v) := by
  ext a b
  simp only [pairSlice_apply,ContinuousLinearMap.comp_apply,normalAt_insert]
  congr 1

omit [CompleteSpace X] in
lemma HasPreadjoint.smul {T : M →L[ℂ] M} (hT : HasPreadjoint e T) (c : ℂ) :
    HasPreadjoint e (c • T) := by
  rw [hasPreadjoint_iff_scalar] at hT ⊢
  intro z
  simpa only [ContinuousLinearMap.comp_smul] using (normalDual e).smul_mem c (hT z)

lemma insertion_before_normal {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (hN : NormalBefore e (normalAt e f r) r.val) :
    NormalBefore e (slotInsertion e f r) r.val := by
  intro i hi v
  have hs : r.succAbove i=i.castSucc :=
    Fin.succAbove_of_castSucc_lt _ _ (by simpa only [Fin.lt_def,Fin.val_castSucc] using hi)
  have he : sliceAt (slotInsertion e f r) i v=(pairSlice (normalAt e f r) r i v).flip 1 := by
    ext a
    rfl
  rw [he,pairSlice_flip]
  exact hN _ (by rw [hs]; exact hi) _

lemma slotRemainder_normal {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+1))
    (hr : 0<r.val) (hf : ∀ v,differentialValue f v=0)
    (hN : NormalBefore e f r.val) (hU : UnitZeroBefore f r.val)
    (hNN : NormalBefore e (normalAt e f r.castSucc) r.val) :
    NormalBefore e (slotRemainder e f r.castSucc) (r.val+1) := by
  have hh := insertion_before_normal e f r.castSucc hNN
  intro j hj v
  let i : Fin (n+1) := ⟨j.val,by omega⟩
  have hji : i.castSucc=j := rfl
  have hs : sliceAt (slotRemainder e f r.castSucc) j v=
      sliceAt (normalAt e f r.castSucc) j v - ((-1:ℂ)^r.val) •
        sliceAt (prefixDifferential (slotInsertion e f r.castSucc) r.val) j v := by
    ext a
    simpa only [sliceAt_apply,sub_apply,smul_apply,Fin.val_castSucc]
      using slotRemainder_apply e f r.castSucc hr hf hN hU (j.insertNth a v)
  rw [hs]
  apply HasPreadjoint.sub e _
    ((prefixDifferential_before_normal e _ r.val hh i (by dsimp [i]; omega) v).smul e _)
  by_cases hjr : j.val<r.val
  · exact hNN j hjr v
  · have hjr : j=r.castSucc := Fin.ext (by simp only [Fin.val_castSucc]; omega)
    rw [hjr]
    exact normalAt_normal e f r.castSucc v

lemma slotRemainder_unitZero {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+1))
    (hr : 0<r.val) (hf : ∀ v,differentialValue f v=0)
    (hN : NormalBefore e f r.val) (hU : UnitZeroBefore f r.val) :
    UnitZeroBefore (slotRemainder e f r.castSucc) (r.val+1) := by
  have hh := insertion_preserves_unitZero e f r.castSucc hU
  have hn := normalAt_preserves_unitZero e f r.castSucc hU
  intro j hj v
  let i : Fin (n+1) := ⟨j.val,by omega⟩
  have hji : i.castSucc=j := rfl
  rw [slotRemainder_apply e f r.castSucc hr hf hN hU]
  simp only [Fin.val_castSucc]
  by_cases hjr : j.val<r.val
  · rw [hn j hjr v,← hji,prefixDifferential_unit_before _ r.val hh i hjr v,smul_zero,sub_zero]
  · have hjr : j=r.castSucc := Fin.ext (by simp only [Fin.val_castSucc]; omega)
    rw [hjr]
    rw [prefixDifferential_unit_at _ r hh v]
    change slotInsertion e f r.castSucc v-(((-1:ℂ)^r.val) • (((-1:ℂ)^r.val) • _))=0
    rw [smul_smul,← mul_pow,neg_mul_neg,one_mul,one_pow,one_smul,sub_self]
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace HochschildNormalPart
universe u
variable (M : Type u) [CStarAlgebra M]

attribute [instance] SharedHilbertFactor.group SharedHilbertFactor.inner SharedHilbertFactor.complete

end HochschildNormalPart

namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma firstRemainder_before_normal {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v,differentialValue f v=0) : NormalBefore e (firstNormalRemainderN e f) 1 := by
  intro i hi v
  have he : i=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
  subst i
  have hs : sliceAt (firstNormalRemainderN e f) 0 v=firstSliceN (normalFirst e f) v-
      (ContinuousLinearMap.mul ℂ M).flip (normalFirst e f (Fin.cons 1 v)) := by
    ext a
    simp only [sliceAt_apply,sub_apply,firstSliceN_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.mul_apply',Fin.insertNth_zero']
    simpa only [Fin.cons_zero,Fin.cons_succ] using firstNormalRemainderN_apply e f hf (Fin.cons a v)
  rw [hs]
  exact (normalFirst_normal e f v).sub e ((HochschildSakai.abstract_multiplication_normal e).2 _)

lemma firstRemainder_before_unitZero {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v,differentialValue f v=0) : UnitZeroBefore (firstNormalRemainderN e f) 1 := by
  intro i hi v
  have he : i=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
  subst i
  rw [Fin.insertNth_zero']
  exact firstNormalRemainderN_one e f hf v

omit [CompleteSpace X] in
lemma separatelyNormal_iff_slices {n : ℕ} (f : Cochain M (n+1)) :
    SeparatelyNormal e f ↔ ∀ i v,HasPreadjoint e (sliceAt f i v) := by
  constructor
  · intro h i v z
    obtain ⟨w,hw⟩ := h i (i.insertNth 0 v) z
    refine ⟨w,fun a => ?_⟩
    simpa only [Fin.update_insertNth,sliceAt_apply] using hw a
  · intro h i v z
    obtain ⟨w,hw⟩ := h i (i.removeNth v) z
    refine ⟨w,fun a => ?_⟩
    simpa only [sliceAt_apply,Fin.insertNth_removeNth] using hw a

end BoundedHochschild

namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def BilinearNormalPartPreservation : Prop :=
  ∀ f : Cochain M 2, (∀ v,HasPreadjoint e (firstSliceN f v)) →
    ∀ v,HasPreadjoint e (firstSliceN (normalLast e f) v)

def bilinearCochain (B : M →L[ℂ] M →L[ℂ] M) : Cochain M 2 :=
  ((continuousMultilinearCurryFin1 ℂ M (M →L[ℂ] M)).symm B).uncurryRight

@[simp] lemma bilinearCochain_apply (B : M →L[ℂ] M →L[ℂ] M) (v : Fin 2 → M) :
    bilinearCochain B v=B (v 0) (v 1) := rfl

lemma bilinearCochain_firstSlice (B : M →L[ℂ] M →L[ℂ] M) (v : Fin 1 → M) :
    firstSliceN (bilinearCochain B) v=B.flip (v 0) := by
  ext a
  rw [firstSliceN_apply]
  rfl

lemma bilinearCochain_normalLast (B : M →L[ℂ] M →L[ℂ] M) :
    normalLast e (bilinearCochain B)=bilinearCochain ((operatorNormalPart e).comp B) := by
  ext v
  simp only [normalLast_apply]
  congr 1

lemma bilinear_preservation_iff : BilinearNormalPartPreservation e ↔
    ∀ (B : M →L[ℂ] M →L[ℂ] M), (∀ b,HasPreadjoint e (B.flip b)) →
      ∀ b,HasPreadjoint e (((operatorNormalPart e).comp B).flip b) := by
  constructor
  · intro h B hn b
    have h' := h (bilinearCochain B) (fun v => by
      rw [bilinearCochain_firstSlice]
      exact hn _) (fun _ => b)
    rwa [bilinearCochain_normalLast,bilinearCochain_firstSlice] at h'
  · intro h f hn v
    let B : M →L[ℂ] M →L[ℂ] M := (continuousMultilinearCurryFin1 ℂ M (M →L[ℂ] M)) f.curryRight
    have hf : bilinearCochain B=f := by
      unfold bilinearCochain B
      rw [LinearIsometryEquiv.symm_apply_apply]
      exact ContinuousMultilinearMap.uncurry_curryRight f
    rw [← hf,bilinearCochain_normalLast,bilinearCochain_firstSlice]
    apply h B
    intro b
    have hn' := hn (fun _ => b)
    rwa [← hf,bilinearCochain_firstSlice] at hn'

lemma normalAt_old_slice_of_preservation
    (hP : BilinearNormalPartPreservation e)
    {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (i : Fin (n+1)) (w : Fin (n+1) → M)
    (hN : ∀ w,HasPreadjoint e (sliceAt f (r.succAbove i) w)) :
    HasPreadjoint e (sliceAt (normalAt e f r) (r.succAbove i) w) := by
  let v₀ : Fin (n+2) → M := (r.succAbove i).insertNth 0 w
  let q := r.removeNth v₀
  let t := i.removeNth q
  have hq : i.insertNth (α := fun _ => M) 0 t=q := by
    have hz : q i=0 := by
      simp only [q,Fin.removeNth,v₀,Fin.insertNth_apply_same]
    rw [← hz]
    exact Fin.insertNth_self_removeNth i q
  have hv : r.insertNth (α := fun _ => M) (v₀ r) (i.insertNth (α := fun _ => M) 0 t)=v₀ := by
    rw [hq]
    exact Fin.insertNth_self_removeNth r v₀
  have h := (bilinear_preservation_iff e).mp hP (pairSlice f r i t)
    (fun b => by rw [pairSlice_flip]; exact hN _) (v₀ r)
  rw [← normalAt_pairSlice,pairSlice_flip,hv] at h
  simpa only [v₀,Fin.removeNth_insertNth] using h

lemma normalAt_before_normal_of_preservation
    (hP : BilinearNormalPartPreservation e)
    {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (hN : NormalBefore e f r.val) :
    NormalBefore e (normalAt e f r) r.val := by
  intro j hj w
  let i : Fin (n+1) := ⟨j.val,by omega⟩
  have hs : r.succAbove i=j := by
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def,Fin.val_castSucc]; exact hj)]
    rfl
  rw [← hs]
  exact normalAt_old_slice_of_preservation e hP f r i w (by rw [hs]; exact hN j hj)
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
namespace HochschildApproximation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem mem_closure_image_ball (L : E →L[ℂ] F)
    (z : StrongDual ℂ (StrongDual ℂ E)) (w : F)
    (hp : ∀ f : StrongDual ℂ F, f w = z (f.comp L))
    {R : ℝ} (hR : 0 < R) (hz : ‖z‖ ≤ R) :
    w ∈ closure (L '' Metric.closedBall (0 : E) R) := by
  by_contra hn
  have hc : Convex ℝ (L '' Metric.closedBall (0 : E) R) :=
    (convex_closedBall (0 : E) R).linear_image (L.restrictScalars ℝ).toLinearMap
  obtain ⟨f,r,hr,hwr⟩ := RCLike.geometric_hahn_banach_closed_point
    (𝕜 := ℂ) hc.closure isClosed_closure hn
  have hr0 : 0 < r := by
    have h := hr 0 (subset_closure (show (0 : F) ∈ L '' Metric.closedBall 0 R from
      ⟨0, by simpa using hR.le, map_zero L⟩))
    simpa using h
  let g := f.comp L
  have hgn : ‖(R : ℂ) • g‖ ≤ r := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hr0.le
    intro a ha
    obtain ⟨c,hc,he⟩ := Complex.exists_norm_eq_mul_self (g a)
    have hain : (R : ℂ) • c • a ∈ Metric.closedBall (0 : E) R := by
      simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR, hc, ha, mul_one, le_refl]
    have h := (hr (L ((R : ℂ) • c • a)) (subset_closure ⟨_,hain,rfl⟩)).le
    have he' : (g (c • a)) = (‖g a‖ : ℂ) := by
      simpa only [map_smul, smul_eq_mul] using he.symm
    change ‖(R : ℂ) • g a‖ ≤ r
    change (g ((R : ℂ) • c • a)).re ≤ r at h
    rw [map_smul, he', smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re] at h
    simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] using h
  have hg : R * ‖g‖ ≤ r := by
    simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] using hgn
  have hbound : (f w).re ≤ r := calc
    (f w).re = (z g).re := congrArg Complex.re (hp f)
    _ ≤ ‖z g‖ := Complex.re_le_norm _
    _ ≤ ‖z‖ * ‖g‖ := z.le_opNorm g
    _ ≤ R * ‖g‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg _)
    _ ≤ r := hg
  exact hwr.not_ge hbound

open Filter Topology

private lemma functional_prod (f : StrongDual ℂ (F × ℂ)) (a : F) (c : ℂ) :
    f (a,c) = f (a,0) + c * f (0,1) := by
  have he : (a,c) = (a,0) + c • ((0,1) : F × ℂ) := by simp
  rw [he, map_add, map_smul, smul_eq_mul]

theorem pair_representation (L : E →L[ℂ] F)
    (z : StrongDual ℂ (StrongDual ℂ E)) (w : F)
    (hw : ∀ f : StrongDual ℂ F, f w = z (f.comp L)) (g : StrongDual ℂ E) :
    ∀ f : StrongDual ℂ (F × ℂ), f (w,z g) = z (f.comp (L.prod g)) := by
  intro f
  let f₁ := f.comp (ContinuousLinearMap.inl ℂ F ℂ)
  have he : f.comp (L.prod g) = f₁.comp L + f (0,1) • g := by
    ext a
    change f (L a,g a) = f (L a,0) + f (0,1) * g a
    rw [functional_prod, mul_comm (g a)]
  rw [he, map_add, map_smul, smul_eq_mul, functional_prod]
  change f₁ w + z g * f (0,1) = z (f₁.comp L) + f (0,1) * z g
  rw [hw]; ring

theorem bounded_sequence_approximation (L : E →L[ℂ] F)
    (z : StrongDual ℂ (StrongDual ℂ E)) (w : F)
    (hw : ∀ f : StrongDual ℂ F, f w = z (f.comp L))
    {R : ℝ} (hR : 0 < R) (hz : ‖z‖ ≤ R) :
    ∃ a : ℕ → E, (∀ n, ‖a n‖ ≤ R) ∧ Tendsto (fun n => L (a n)) atTop (𝓝 w) := by
  have hm := mem_closure_image_ball L z w hw hR hz
  obtain ⟨s,hs,hlim⟩ := mem_closure_iff_seq_limit.mp hm
  choose a ha he using hs
  refine ⟨a, ?_, ?_⟩
  · intro n
    simpa only [Metric.mem_closedBall, dist_zero_right] using ha n
  · simpa only [he] using hlim

private lemma tendsto_of_fourth {ι : Type*} {l : Filter ι} {f : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) (h : Tendsto (fun i => (f i)^4) l (𝓝 0)) :
    Tendsto f l (𝓝 0) := by
  have hs := h.sqrt.sqrt
  have he (i : ι) : Real.sqrt (Real.sqrt ((f i)^4)) = f i := by
    rw [show (f i)^4 = ((f i)^2)^2 by ring, Real.sqrt_sq (sq_nonneg _),
      Real.sqrt_sq (hf i)]
  simpa only [he, Real.sqrt_zero] using hs

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

theorem quartic_tendsto_zero_bounded (T : E →L[ℂ] Y) (L : E →L[ℂ] F)
    {C : ℝ} (hC : 0 ≤ C)
    (hdom : ∀ a, ‖T a‖^4 ≤ C * ‖a‖^2 * ‖L a‖^2)
    {ι : Type*} {l : Filter ι} {a : ι → E} {R : ℝ} (_hR : 0 ≤ R)
    (ha : ∀ i, ‖a i‖ ≤ R) (hL : Tendsto (fun i => L (a i)) l (𝓝 0)) :
    Tendsto (fun i => T (a i)) l (𝓝 0) := by
  have hn : Tendsto (fun i => ‖L (a i)‖) l (𝓝 0) := by simpa using hL.norm
  have hu : Tendsto (fun i => (C * R^2) * ‖L (a i)‖^2) l (𝓝 0) := by
    simpa using (hn.pow 2).const_mul (C * R^2)
  have hp : Tendsto (fun i => ‖T (a i)‖^4) l (𝓝 0) := by
    apply squeeze_zero (fun i => pow_nonneg (norm_nonneg _) _) _ hu
    intro i
    calc
      ‖T (a i)‖^4 ≤ C * ‖a i‖^2 * ‖L (a i)‖^2 := hdom _
      _ ≤ C * R^2 * ‖L (a i)‖^2 := by gcongr; exact ha i
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_of_fourth (fun _ => norm_nonneg _) hp)

theorem closed_subspace_preserved_of_quartic [CompleteSpace Y]
    (T : E →L[ℂ] Y) (L : E →L[ℂ] F) {C : ℝ} (hC : 0 ≤ C)
    (hdom : ∀ a, ‖T a‖^4 ≤ C * ‖a‖^2 * ‖L a‖^2)
    (K : Submodule ℂ Y) (hK : IsClosed (K : Set Y)) (hT : ∀ a, T a ∈ K)
    (z : StrongDual ℂ (StrongDual ℂ E)) (w : F)
    (hw : ∀ f : StrongDual ℂ F, f w = z (f.comp L)) :
    ∃ y ∈ K, ∀ f : StrongDual ℂ Y, f y = z (f.comp T) := by
  let R := ‖z‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hz : ‖z‖ ≤ R := by dsimp [R]; linarith
  obtain ⟨a,ha,halim⟩ := bounded_sequence_approximation L z w hw hR hz
  have hdiff : Tendsto (fun p : ℕ × ℕ => L (a p.1 - a p.2)) atTop (𝓝 0) := by
    simpa only [map_sub, sub_self, Function.comp_apply] using
      (halim.comp (show Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop by
        rw [← prod_atTop_atTop_eq]; exact tendsto_fst)).sub (halim.comp (show Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop by
        rw [← prod_atTop_atTop_eq]; exact tendsto_snd))
  have hTd := quartic_tendsto_zero_bounded T L hC hdom (by positivity : 0 ≤ 2*R)
    (fun p : ℕ × ℕ => (norm_sub_le _ _).trans (show ‖a p.1‖ + ‖a p.2‖ ≤ 2*R by
      linarith [ha p.1,ha p.2])) hdiff
  have hc : CauchySeq (fun n => T (a n)) := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    simpa only [map_sub, norm_zero, dist_eq_norm] using hTd.norm
  obtain ⟨y,hy⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨y, hK.mem_of_tendsto hy (Eventually.of_forall (fun n => hT (a n))), ?_⟩
  intro f
  obtain ⟨b,hb,hblim⟩ := bounded_sequence_approximation (L.prod (f.comp T)) z
    (w,z (f.comp T)) (pair_representation L z w hw (f.comp T)) hR hz
  have hbL : Tendsto (fun n => L (b n)) atTop (𝓝 w) :=
    (continuous_fst.tendsto (w,z (f.comp T))).comp hblim
  have hbf : Tendsto (fun n => f (T (b n))) atTop (𝓝 (z (f.comp T))) :=
    (continuous_snd.tendsto (w,z (f.comp T))).comp hblim
  have hdL : Tendsto (fun n => L (a n - b n)) atTop (𝓝 0) := by
    simpa only [map_sub, sub_self] using halim.sub hbL
  have hdT := quartic_tendsto_zero_bounded T L hC hdom (by positivity : 0 ≤ 2*R)
    (fun n => (norm_sub_le _ _).trans (show ‖a n‖ + ‖b n‖ ≤ 2*R by
      linarith [ha n,hb n])) hdL
  have hbT : Tendsto (fun n => T (b n)) atTop (𝓝 y) := by
    simpa only [map_sub, sub_sub_cancel, sub_zero] using hy.sub hdT
  exact tendsto_nhds_unique (f.continuous.tendsto y |>.comp hbT) hbf
end HochschildApproximation
end
end OAI
end

section
namespace OAI

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

theorem scalar_bilinear_normal_preservation (B : M →L[ℂ] StrongDual ℂ M)
    (hn : ∀ b, B.flip b ∈ normalDual e) (b : M) :
    ((scalarNormalPart e).comp B).flip b ∈ normalDual e := by
  obtain ⟨H,hH,hI,hcomp,β,C,hC,hdom⟩ :=
    HochschildDomination.exists_quartic_hilbert_modulus B
  let := hH
  let := hI
  let := hcomp
  let z : StrongDual ℂ (StrongDual ℂ M) :=
    ((ContinuousLinearMap.apply ℂ ℂ) b).comp (scalarNormalPart e)
  let w : H := hilbertNormalPart e β b
  have hw (φ : StrongDual ℂ H) : φ w = z (φ.comp β) :=
    hilbertNormalPart_pairing e β b φ
  obtain ⟨y,hy,he⟩ := HochschildApproximation.closed_subspace_preserved_of_quartic
    B.flip β hC hdom (normalDual e) (normalDual_closed e) hn z w hw
  have hN : ((scalarNormalPart e).comp B).flip b = y := by
    ext a
    exact (he ((ContinuousLinearMap.apply ℂ ℂ) a)).symm
  rw [hN]
  exact hy

open BoundedHochschild in

theorem operator_bilinear_normal_preservation (B : M →L[ℂ] M →L[ℂ] M)
    (hn : ∀ b, HasPreadjoint e (B.flip b)) (b : M) :
    HasPreadjoint e (((operatorNormalPart e).comp B).flip b) := by
  rw [hasPreadjoint_iff_scalar]
  intro z
  let Bz : M →L[ℂ] StrongDual ℂ M :=
    (ContinuousLinearMap.compL ℂ M M ℂ (predualEmbedding e z)).comp B
  have hzn (c : M) : Bz.flip c ∈ normalDual e :=
    (hasPreadjoint_iff_scalar e (B.flip c)).mp (hn c) z
  have h := scalar_bilinear_normal_preservation e Bz hzn b
  have heq : (predualEmbedding e z).comp (((operatorNormalPart e).comp B).flip b) =
      ((scalarNormalPart e).comp Bz).flip b := by
    ext a
    exact operatorNormalPart_pairing e (B a) b z
  rw [heq]
  exact h
end HochschildNormalPart
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def updateSlice {n : ℕ} (f : Cochain M (n + 1)) (i : Fin (n + 1))
    (v : Fin (n + 1) → M) : M →L[ℂ] M := sliceAt f i (i.removeNth v)

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma updateSlice_apply {n : ℕ} (f : Cochain M (n + 1)) (i : Fin (n + 1))
    (v : Fin (n + 1) → M) (a : M) : updateSlice f i v a = f (Function.update v i a) := by
  simp only [updateSlice, sliceAt_apply, Fin.insertNth_removeNth]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

private def multiplyBoth (a b : M) : M →L[ℂ] M :=
  ((ContinuousLinearMap.mul ℂ M).flip b).comp (ContinuousLinearMap.mul ℂ M a)

private lemma multiplyBoth_apply (a b x : M) : multiplyBoth a b x = a * x * b := rfl

private lemma multiplyBoth_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a b : M) :
    HasPreadjoint e (multiplyBoth a b) :=
  ((HochschildSakai.abstract_multiplication_normal e).2 b).comp e
    ((HochschildSakai.abstract_multiplication_normal e).1 a)

def cochainSandwich {n : ℕ} (a b : Fin n → M) (c d : M) (f : Cochain M n) : Cochain M n :=
  (multiplyBoth c d).compContinuousMultilinearMap
    (f.compContinuousLinearMap (fun i => multiplyBoth (a i) (b i)))

@[simp] lemma cochainSandwich_apply {n : ℕ} (a b : Fin n → M) (c d : M)
    (f : Cochain M n) (x : Fin n → M) :
    cochainSandwich a b c d f x = c * f (fun i => a i * x i * b i) * d := rfl

private lemma sandwich_update {n : ℕ} (a b x : Fin (n + 1) → M) (i : Fin (n + 1)) (z : M) :
    (fun j => a j * Function.update x i z j * b j) =
      Function.update (fun j => a j * x j * b j) i (a i * z * b i) := by
  ext j
  by_cases hji : j = i <;> simp [hji]

private lemma sandwich_slice {n : ℕ} (a b : Fin (n + 1) → M) (c d : M)
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) (x : Fin (n + 1) → M) :
    updateSlice (cochainSandwich a b c d f) i x =
      (multiplyBoth c d).comp
        ((updateSlice f i (fun j => a j * x j * b j)).comp (multiplyBoth (a i) (b i))) := by
  ext z
  simp only [updateSlice_apply, cochainSandwich_apply, sandwich_update,
    ContinuousLinearMap.comp_apply, multiplyBoth_apply]

lemma normalAt_value (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ}
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) (x : Fin (n + 1) → M) :
    normalAt e f i x = HochschildNormalPart.operatorNormalPart e (updateSlice f i x) (x i) := by
  calc
    _ = normalAt e f i (i.insertNth (x i) (i.removeNth x)) :=
      congrArg (normalAt e f i) (Fin.insertNth_self_removeNth i x).symm
    _ = _ := normalAt_insert e f i (i.removeNth x) (x i)

lemma normalAt_cochainSandwich (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ}
    (a b : Fin (n + 1) → M) (c d : M) (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    normalAt e (cochainSandwich a b c d f) i = cochainSandwich a b c d (normalAt e f i) := by
  ext x
  rw [normalAt_value, sandwich_slice,
    HochschildNormalPart.operatorNormalPart_comp_normal e _ _ (multiplyBoth_normal e c d)]
  have hin (T : M →L[ℂ] M) :
      HochschildNormalPart.operatorNormalPart e (T.comp (multiplyBoth (a i) (b i))) =
        (HochschildNormalPart.operatorNormalPart e T).comp (multiplyBoth (a i) (b i)) := by
    unfold multiplyBoth
    rw [← ContinuousLinearMap.comp_assoc,
      HochschildNormalPart.operatorNormalPart_comp_left,
      HochschildNormalPart.operatorNormalPart_comp_right,
      ContinuousLinearMap.comp_assoc]
  rw [hin]
  simp only [cochainSandwich_apply, normalAt_value,
    ContinuousLinearMap.comp_apply, multiplyBoth_apply]

lemma cochainSandwich_leftInput {n : ℕ} (f : Cochain M (n + 1)) (k : Fin (n + 1))
    (r : M) (x : Fin (n + 1) → M) :
    cochainSandwich (Function.update (fun _ => 1) k r) (fun _ => 1) 1 1 f x =
      f (Function.update x k (r * x k)) := by
  rw [cochainSandwich_apply, one_mul, mul_one]
  congr 1
  ext j
  by_cases hj : j = k <;> simp [hj]

lemma cochainSandwich_rightInput {n : ℕ} (f : Cochain M (n + 1)) (k : Fin (n + 1))
    (r : M) (x : Fin (n + 1) → M) :
    cochainSandwich (fun _ => 1) (Function.update (fun _ => 1) k r) 1 1 f x =
      f (Function.update x k (x k * r)) := by
  rw [cochainSandwich_apply, one_mul, mul_one]
  congr 1
  ext j
  by_cases hj : j = k <;> simp [hj]

lemma cochainSandwich_leftOutput {n : ℕ} (f : Cochain M n) (r : M) (x : Fin n → M) :
    cochainSandwich (fun _ => 1) (fun _ => 1) r 1 f x = r * f x := by
  simp only [cochainSandwich_apply, one_mul, mul_one]

lemma cochainSandwich_rightOutput {n : ℕ} (f : Cochain M n) (r : M) (x : Fin n → M) :
    cochainSandwich (fun _ => 1) (fun _ => 1) 1 r f x = f x * r := by
  simp only [cochainSandwich_apply, one_mul, mul_one]

lemma normalAt_multimodularAt (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ}
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) (r : M) (hf : MultimodularAt f r) :
    MultimodularAt (normalAt e f i) r := by
  constructor
  · intro x
    have h : cochainSandwich (Function.update (fun _ => 1) 0 r) (fun _ => 1) 1 1 f =
        cochainSandwich (fun _ => 1) (fun _ => 1) r 1 f := by
      ext y
      simpa only [cochainSandwich_leftInput, cochainSandwich_leftOutput] using hf.left y
    have hh := congrArg (fun F : Cochain M (n + 1) => normalAt e F i) h
    simp only [normalAt_cochainSandwich] at hh
    simpa only [cochainSandwich_leftInput, cochainSandwich_leftOutput] using
      congrArg (fun F : Cochain M (n + 1) => F x) hh
  · intro x
    have h : cochainSandwich (fun _ => 1) (Function.update (fun _ => 1) (Fin.last n) r) 1 1 f =
        cochainSandwich (fun _ => 1) (fun _ => 1) 1 r f := by
      ext y
      simpa only [cochainSandwich_rightInput, cochainSandwich_rightOutput] using hf.right y
    have hh := congrArg (fun F : Cochain M (n + 1) => normalAt e F i) h
    simp only [normalAt_cochainSandwich] at hh
    simpa only [cochainSandwich_rightInput, cochainSandwich_rightOutput] using
      congrArg (fun F : Cochain M (n + 1) => F x) hh
  · intro x j
    have h : cochainSandwich (fun _ => 1) (Function.update (fun _ => 1) j.castSucc r) 1 1 f =
        cochainSandwich (Function.update (fun _ => 1) j.succ r) (fun _ => 1) 1 1 f := by
      ext y
      simpa only [cochainSandwich_rightInput, cochainSandwich_leftInput] using hf.balance y j
    have hh := congrArg (fun F : Cochain M (n + 1) => normalAt e F i) h
    simp only [normalAt_cochainSandwich] at hh
    simpa only [cochainSandwich_rightInput, cochainSandwich_leftInput] using
      congrArg (fun F : Cochain M (n + 1) => F x) hh
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma multimodularAt_curryMid_one {n : ℕ} (f : Cochain M (n + 2)) (r : M)
    (hf : MultimodularAt f r) (k : Fin (n + 2)) :
    MultimodularAt (f.curryMid k 1) r := by
  constructor
  · intro x
    change f (k.insertNth 1 (Function.update x 0 (r * x 0))) = r * f (k.insertNth (α := fun _ => M) 1 x)
    rw [Fin.insertNth_update]
    by_cases hk : k = 0
    · subst k
      have h := hf.balance ((0 : Fin (n + 2)).insertNth 1 x) (0 : Fin (n + 1))
      have hl := hf.left ((0 : Fin (n + 2)).insertNth 1 x)
      simp only [Fin.succAbove_zero, Fin.insertNth_zero', Fin.cons_zero,
        Fin.castSucc_zero, one_mul, mul_one] at h hl ⊢
      exact h.symm.trans hl
    · have hs : k.succAbove (0 : Fin (n + 1)) = 0 := Fin.succAbove_ne_zero_zero hk
      have hv : k.insertNth (α := fun _ => M) 1 x 0 = x 0 := by
        rw [← hs]
        exact Fin.insertNth_apply_succAbove (α := fun _ => M) k 1 x 0
      simpa only [hs, hv] using hf.left (k.insertNth (α := fun _ => M) 1 x)
  · intro x
    change f (k.insertNth 1 (Function.update x (Fin.last n) (x (Fin.last n) * r))) =
      f (k.insertNth (α := fun _ => M) 1 x) * r
    rw [Fin.insertNth_update]
    by_cases hk : k = Fin.last (n + 1)
    · subst k
      have h := hf.balance ((Fin.last (n + 1)).insertNth 1 x) (Fin.last n)
      have hr := hf.right ((Fin.last (n + 1)).insertNth 1 x)
      simp only [Fin.succAbove_last, Fin.insertNth_last', Fin.snoc_last,
        Fin.snoc_castSucc, Fin.succ_last, one_mul, mul_one] at h hr ⊢
      exact h.trans hr
    · have hs := Fin.succAbove_ne_last_last hk
      have hv : k.insertNth (α := fun _ => M) 1 x (Fin.last (n + 1)) = x (Fin.last n) := by
        rw [← hs]
        exact Fin.insertNth_apply_succAbove (α := fun _ => M) k 1 x (Fin.last n)
      simpa only [hs, hv] using hf.right (k.insertNth (α := fun _ => M) 1 x)
  · intro x j
    change f (k.insertNth 1 (Function.update x j.castSucc (x j.castSucc * r))) =
      f (k.insertNth 1 (Function.update x j.succ (r * x j.succ)))
    rw [Fin.insertNth_update, Fin.insertNth_update]
    let y := k.insertNth (α := fun _ => M) 1 x
    have hv (i : Fin (n + 1)) : y (k.succAbove i) = x i :=
      Fin.insertNth_apply_succAbove (α := fun _ => M) k 1 x i
    by_cases hk : k.val ≤ j.val
    · have hs₀ : k.succAbove j.castSucc = j.castSucc.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simpa only [Fin.le_def, Fin.val_castSucc] using hk)
      have hs₁ : k.succAbove j.succ = j.succ.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)
      have h₀ : y j.succ.castSucc = x j.castSucc := by
        simpa only [hs₀, Fin.castSucc_succ] using hv j.castSucc
      have h₁ : y j.succ.succ = x j.succ := by simpa only [hs₁] using hv j.succ
      simpa only [hs₀, hs₁, ← Fin.castSucc_succ, h₀, h₁] using hf.balance y j.succ
    · by_cases hk' : k.val = j.val + 1
      · have he : k = j.castSucc.succ := Fin.ext hk'
        have hs₀ : k.succAbove j.castSucc = j.castSucc.castSucc :=
          Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def, Fin.val_castSucc]; omega)
        have hs₁ : k.succAbove j.succ = j.succ.succ :=
          Fin.succAbove_of_le_castSucc _ _ (by simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)
        have h₀ : y j.castSucc.castSucc = x j.castSucc := by simpa only [hs₀] using hv j.castSucc
        have h₁ : y j.succ.succ = x j.succ := by simpa only [hs₁] using hv j.succ
        have hmid : y j.castSucc.succ = 1 := by rw [← he]; exact Fin.insertNth_apply_same (α := fun _ => M) k 1 x
        have ha := hf.balance y j.castSucc
        have hb := hf.balance y j.succ
        simp only [h₀, hmid, mul_one] at ha
        simp only [Fin.castSucc_succ, hmid, h₁, one_mul] at hb
        simpa only [hs₀, hs₁] using ha.trans hb
      · have hs₀ : k.succAbove j.castSucc = j.castSucc.castSucc :=
          Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def, Fin.val_castSucc]; omega)
        have hs₁ : k.succAbove j.succ = j.succ.castSucc :=
          Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega)
        have h₀ : y j.castSucc.castSucc = x j.castSucc := by simpa only [hs₀] using hv j.castSucc
        have h₁ : y j.castSucc.succ = x j.succ := by simpa only [hs₁, Fin.castSucc_succ] using hv j.succ
        simpa only [hs₀, hs₁, Fin.castSucc_succ, h₀, h₁] using hf.balance y j.castSucc
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma MultimodularAt.add {n : ℕ} {f g : Cochain M (n + 1)} {r : M}
    (hf : MultimodularAt f r) (hg : MultimodularAt g r) : MultimodularAt (f + g) r := by
  constructor
  · intro x
    simp only [add_apply, hf.left, hg.left, mul_add]
  · intro x
    simp only [add_apply, hf.right, hg.right, add_mul]
  · intro x j
    simp only [add_apply, hf.balance x j, hg.balance x j]

lemma MultimodularAt.smul {n : ℕ} {f : Cochain M (n + 1)} {r : M}
    (hf : MultimodularAt f r) (z : ℂ) : MultimodularAt (z • f) r := by
  constructor
  · intro x
    simp only [smul_apply, hf.left, mul_smul_comm]
  · intro x
    simp only [smul_apply, hf.right, smul_mul_assoc]
  · intro x j
    simp only [smul_apply, hf.balance x j]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma MultimodularAt.sub {n : ℕ} {f g : Cochain M (n + 1)} {r : M}
    (hf : MultimodularAt f r) (hg : MultimodularAt g r) : MultimodularAt (f - g) r := by
  simpa only [neg_one_smul, ← sub_eq_add_neg] using hf.add (hg.smul (-1))

lemma multimodularOver_iff_at {n : ℕ} (R : StarSubalgebra ℂ M) (f : Cochain M (n + 1)) :
    MultimodularOver R f ↔ ∀ r ∈ R, MultimodularAt f r := by
  constructor
  · intro h r hr
    exact ⟨h.left r hr, h.right r hr, h.balance r hr⟩
  · intro h
    exact ⟨fun r hr => (h r hr).left, fun r hr => (h r hr).right,
      fun r hr => (h r hr).balance⟩

lemma normalFirst_eq_normalAt_zero (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (f : Cochain M (n + 1)) : normalFirst e f = normalAt e f 0 := by
  ext x
  rw [← Fin.cons_self_tail x, normalFirst_cons]
  have h := normalAt_insert e f 0 (Fin.tail x) (x 0)
  simp only [Fin.insertNth_zero'] at h
  rw [h]
  have hs : firstSliceN f (Fin.tail x) = sliceAt f 0 (Fin.tail x) := by
    ext a
    simp only [sliceAt_apply, Fin.insertNth_zero', firstSliceN_apply]
  rw [hs]

lemma multimodularAt_firstNormalCorrection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (f : Cochain M (n + 2)) (r : M) (hf : MultimodularAt f r) :
    MultimodularAt (firstNormalCorrectionN e f) r := by
  have hn : MultimodularAt (normalFirst e f) r := by
    rw [normalFirst_eq_normalAt_zero]
    exact normalAt_multimodularAt e f 0 r hf
  have he : firstNormalCorrectionN e f = (normalFirst e f).curryMid 0 1 := by
    ext x
    change normalFirst e f (Fin.cons 1 x) = normalFirst e f ((0 : Fin (n + 2)).insertNth 1 x)
    rw [Fin.insertNth_zero']
  rw [he]
  exact multimodularAt_curryMid_one _ r hn 0

lemma multimodularAt_firstNormalRemainder (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (f : Cochain M (n + 2)) (r : M) (hf : MultimodularAt f r) :
    MultimodularAt (firstNormalRemainderN e f) r := by
  exact hf.sub (multimodularAt_differential _ r (multimodularAt_firstNormalCorrection e f r hf))

lemma multimodularAt_slotInsertion (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (f : Cochain M (n + 2)) (i : Fin (n + 2)) (r : M)
    (hf : MultimodularAt f r) : MultimodularAt (slotInsertion e f i) r :=
  multimodularAt_curryMid_one _ r (normalAt_multimodularAt e f i r hf) i

lemma multimodularAt_slotRemainder (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (f : Cochain M (n + 2)) (i : Fin (n + 2)) (r : M)
    (hf : MultimodularAt f r) : MultimodularAt (slotRemainder e f i) r :=
  hf.sub ((multimodularAt_differential _ r (multimodularAt_slotInsertion e f i r hf)).smul _)

lemma multimodularOver_firstNormalRemainder (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (R : StarSubalgebra ℂ M) (f : Cochain M (n + 2)) (hf : MultimodularOver R f) :
    MultimodularOver R (firstNormalRemainderN e f) := by
  rw [multimodularOver_iff_at] at hf ⊢
  exact fun r hr => multimodularAt_firstNormalRemainder e f r (hf r hr)

lemma multimodularOver_slotRemainder (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (R : StarSubalgebra ℂ M) (f : Cochain M (n + 2)) (i : Fin (n + 2))
    (hf : MultimodularOver R f) : MultimodularOver R (slotRemainder e f i) := by
  rw [multimodularOver_iff_at] at hf ⊢
  exact fun r hr => multimodularAt_slotRemainder e f i r (hf r hr)

lemma normal_before_multimodular (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hP : BilinearNormalPartPreservation e) {n : ℕ} (R : StarSubalgebra ℂ M)
    (f : Cochain M (n + 2)) (hf : ∀ x, differentialValue f x = 0)
    (hM : MultimodularOver R f) (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n + 1) :
    ∃ (F : Cochain M (n + 2)) (b : Cochain M (n + 1)),
      (∀ x, differentialValue F x = 0) ∧ (∀ x, f x = F x + differentialValue b x) ∧
      NormalBefore e F r ∧ UnitZeroBefore F r ∧ MultimodularOver R F := by
  induction r with
  | zero => omega
  | succ r ih =>
      by_cases hz : r = 0
      · subst r
        exact ⟨firstNormalRemainderN e f, firstNormalCorrectionN e f,
          firstNormalRemainderN_cocycle e f hf, firstNormalRemainderN_identity e f,
          firstRemainder_before_normal e f hf, firstRemainder_before_unitZero e f hf,
          multimodularOver_firstNormalRemainder e R f hM⟩
      · obtain ⟨F, b, hFc, hid, hFN, hFU, hFM⟩ := ih (by omega) (by omega)
        let i : Fin (n + 1) := ⟨r, by omega⟩
        have hi : 0 < i.val := by dsimp [i]; omega
        have hNN := normalAt_before_normal_of_preservation e hP F i.castSucc hFN
        refine ⟨slotRemainder e F i.castSucc, b + slotCorrection e F i.castSucc,
          slotRemainder_cocycle e F i.castSucc hFc, ?_,
          slotRemainder_normal e F i hi hFc hFN hFU hNN,
          slotRemainder_unitZero e F i hi hFc hFN hFU,
          multimodularOver_slotRemainder e R F i.castSucc hFM⟩
        intro x
        rw [hid x, slotRemainder_identity e F i.castSucc x, differentialValue_add]
        abel

theorem normal_reduction_multimodular (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (R : StarSubalgebra ℂ M) (f : Cochain M (n + 2))
    (hf : ∀ x, differentialValue f x = 0) (hM : MultimodularOver R f) :
    ∃ (F : Cochain M (n + 2)) (b : Cochain M (n + 1)),
      SeparatelyNormal e F ∧ MultimodularOver R F ∧
      (∀ x, differentialValue F x = 0) ∧ (∀ x, f x = F x + differentialValue b x) := by
  have hP : BilinearNormalPartPreservation e :=
    (bilinear_preservation_iff e).mpr (HochschildNormalPart.operator_bilinear_normal_preservation e)
  obtain ⟨F, b, hFc, hid, hFN, _, hFM⟩ :=
    normal_before_multimodular e hP R f hf hM (n + 1) (by omega) le_rfl
  exact ⟨F, b, (separatelyNormal_iff_slices e F).mpr
    (all_normal_of_before_penultimate e F hFc hFN), hFM, hFc, hid⟩
end BoundedHochschild.KadisonRingrose
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.KadisonRingrose.normal_reduction_multimodular.{u} := @OAI.BoundedHochschild.KadisonRingrose.normal_reduction_multimodular.{u}
