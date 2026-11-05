-- Prove2me | solution 1 for OAI.BoundedHochschild.all_normal_of_before_penultimate
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:55:07.265994+00:00
-- url     : https://prove2.me/submissions/8ff0c0e4-59d7-4a9e-b64e-c7ef413eddc2

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_HochschildNormalPart_normalProjection_fixes_normal
import Theorems.Thm_OAI_HochschildNormalPart_normalProjection_sum
import Theorems.Thm_OAI_HochschildNormalPart_functionalModel_nonempty

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

noncomputable def insertLast {n : ℕ} (f : Cochain M (n + 1)) (u : M) : Cochain M n :=
  ((ContinuousLinearMap.apply ℂ M) u).compContinuousMultilinearMap f.curryRight

@[simp] theorem insertLast_apply {n : ℕ} (f : Cochain M (n + 1)) (u : M)
    (v : Fin n → M) : insertLast f u v = f (Fin.snoc v u) := rfl

end AlgebraicAveraging

section TupleIdentities
variable {M : Type*}

theorem snoc_succ_tuple {n : ℕ} (v : Fin (n + 1) → M) (u : M) :
    (fun i : Fin (n + 1) => (Fin.snoc v u : Fin (n + 2) → M) i.succ) =
      Fin.snoc (fun i : Fin n => v i.succ) u := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp only [← Fin.castSucc_succ, Fin.snoc_castSucc]

theorem snoc_castSucc_tuple {n : ℕ} (v : Fin n → M) (u : M) :
    (fun i : Fin n => (Fin.snoc v u : Fin (n + 1) → M) i.castSucc) = v := by
  funext i
  exact Fin.snoc_castSucc (α := fun _ => M) u v i

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

section CocycleIdentity
variable {M : Type*} [NormedRing M] [NormedAlgebra ℂ M]

theorem differentialValue_snoc {n : ℕ} (f : Cochain M (n + 1))
    (v : Fin (n + 1) → M) (u : M) :
    differentialValue f (Fin.snoc v u) =
      v 0 * f (Fin.snoc (fun i : Fin n => v i.succ) u) +
      (∑ j : Fin n, ((-1 : ℂ) ^ (j.val + 1)) • f (Fin.snoc (mergeInputs v j) u)) +
      ((-1 : ℂ) ^ (n + 1)) •
        f (Fin.snoc (fun i : Fin n => v i.castSucc) (v (Fin.last n) * u)) +
      ((-1 : ℂ) ^ (n + 2)) • (f v * u) := by
  rw [differentialValue, snoc_succ_tuple, snoc_castSucc_tuple, Fin.sum_univ_castSucc]
  simp only [mergeInputs_snoc_castSucc, Fin.val_castSucc, mergeInputs_snoc_last,
    Fin.val_last, Fin.snoc_last]
  have hzero : (Fin.snoc v u : Fin (n + 2) → M) 0 = v 0 := by
    exact Fin.snoc_castSucc (α := fun _ => M) u v 0
  rw [hzero]
  abel
end CocycleIdentity
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

lemma sign_succ (k : ℕ) : (-1:ℂ)^(k+1) = -((-1:ℂ)^k) := by
  rw [pow_succ]
  ring
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

end BoundedHochschild

namespace BoundedHochschild
open HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

end BoundedHochschild

namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def penultimateSlice {n : ℕ} (f : Cochain M (n+2))
    (v : Fin n → M) (c : M) : M →L[ℂ] M :=
  (insertLast f c).curryRight v

@[simp] lemma penultimateSlice_apply {n : ℕ} (f : Cochain M (n+2))
    (v : Fin n → M) (c b : M) :
    penultimateSlice f v c b=f (Fin.snoc (Fin.snoc v b) c) := rfl

lemma differentialValue_snoc_snoc {n : ℕ} (f : Cochain M (n+2))
    (v : Fin (n+1) → M) (b c : M) :
    differentialValue f (Fin.snoc (Fin.snoc v b) c)=
      v 0*f (Fin.snoc (Fin.snoc (fun i : Fin n => v i.succ) b) c)+
      (∑ j : Fin n,((-1:ℂ)^(j.val+1)) •
        f (Fin.snoc (Fin.snoc (mergeInputs v j) b) c))+
      ((-1:ℂ)^(n+1)) •
        f (Fin.snoc (Fin.snoc (fun i : Fin n => v i.castSucc) (v (Fin.last n)*b)) c)+
      ((-1:ℂ)^(n+2)) • f (Fin.snoc v (b*c))+
      ((-1:ℂ)^(n+3)) • (f (Fin.snoc v b)*c) := by
  rw [differentialValue_snoc,Fin.sum_univ_castSucc]
  have hzero : (Fin.snoc v b : Fin (n+2) → M) 0=v 0 :=
    Fin.snoc_castSucc (α := fun _ => M) b v 0
  simp only [hzero,snoc_succ_tuple,mergeInputs_snoc_castSucc,Fin.val_castSucc,
    mergeInputs_snoc_last,Fin.val_last,snoc_castSucc_tuple,Fin.snoc_last]
  abel

theorem cocycle_last_normal_of_penultimate_normal {n : ℕ}
    (f : Cochain M (n+2)) (hf : ∀ z,differentialValue f z=0)
    (hN : ∀ v c,HasPreadjoint e (penultimateSlice f v c)) :
    ∀ v,HasPreadjoint e (f.curryRight v) := by
  intro v
  let S : M →L[ℂ] M := f.curryRight v
  let P := operatorNormalPart e S
  let L := ContinuousLinearMap.mul ℂ M
  let R := (ContinuousLinearMap.mul ℂ M).flip
  have hrec (b c : M) :
      v 0*f (Fin.snoc (Fin.snoc (fun i : Fin n => v i.succ) b) c)+
      (∑ j : Fin n,((-1:ℂ)^(j.val+1)) •
        f (Fin.snoc (Fin.snoc (mergeInputs v j) b) c))+
      ((-1:ℂ)^(n+1)) •
        f (Fin.snoc (Fin.snoc (fun i : Fin n => v i.castSucc) (v (Fin.last n)*b)) c)+
      ((-1:ℂ)^(n+2)) • P (b*c)+
      ((-1:ℂ)^(n+3)) • (P b*c)=0 := by
    have hop :
        (L (v 0)).comp (penultimateSlice f (fun i : Fin n => v i.succ) c)+
        (∑ j : Fin n,((-1:ℂ)^(j.val+1)) • penultimateSlice f (mergeInputs v j) c)+
        ((-1:ℂ)^(n+1)) •
          (penultimateSlice f (fun i : Fin n => v i.castSucc) c).comp (L (v (Fin.last n)))+
        ((-1:ℂ)^(n+2)) • S.comp (R c)+
        ((-1:ℂ)^(n+3)) • (R c).comp S=0 := by
      ext x
      simpa only [L,R,S,ContinuousLinearMap.comp_apply,ContinuousLinearMap.mul_apply',
        ContinuousLinearMap.flip_apply,penultimateSlice_apply,add_apply,
        sum_apply,smul_apply,zero_apply,ContinuousMultilinearMap.curryRight_apply,
        differentialValue_snoc_snoc] using hf (Fin.snoc (Fin.snoc v x) c)
    have h := congrArg (fun T : M →L[ℂ] M => operatorNormalPart e T b) hop
    dsimp only [L,R] at h
    simp only [map_add,map_sum,map_smul,map_zero,add_apply,sum_apply,smul_apply,zero_apply,
      operatorNormalPart_comp_normal e _ _ ((HochschildSakai.abstract_multiplication_normal e).1 (v 0)),
      operatorNormalPart_comp_normal e _ _ ((HochschildSakai.abstract_multiplication_normal e).2 c),
      operatorNormalPart_comp_left,operatorNormalPart_comp_right,
      operatorNormalPart_fixes e _ (hN _ _),ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mul_apply',ContinuousLinearMap.flip_apply,penultimateSlice_apply] at h
    exact h
  have hmodule (c : M) : (S-P) c=(S-P) 1*c := by
    have h := hf (Fin.snoc (Fin.snoc v (1:M)) c)
    rw [differentialValue_snoc_snoc] at h
    have h' := hrec 1 c
    rw [sign_succ (n+2)] at h h'
    simp only [one_mul,neg_smul] at h h'
    have hh : ((-1:ℂ)^(n+2)) • ((S-P) c-(S-P) 1*c)=0 := by
      simp only [S,sub_apply,ContinuousMultilinearMap.curryRight_apply,sub_mul,smul_sub]
      linear_combination (norm := module) h-h'
    exact sub_eq_zero.mp ((smul_eq_zero.mp hh).resolve_left (pow_ne_zero _ (by norm_num)))
  have he : S-P=ContinuousLinearMap.mul ℂ M ((S-P) 1) := by
    ext c
    exact hmodule c
  have hz : operatorNormalPart e (S-P)=0 := by
    rw [map_sub,operatorNormalPart_fixes e P (operatorNormalPart_normal e S),sub_self]
  rw [operatorNormalPart_fixes e (S-P) (by
    rw [he]
    exact (HochschildSakai.abstract_multiplication_normal e).1 _)] at hz
  have hSP : S=P := sub_eq_zero.mp hz
  change HasPreadjoint e S
  rw [hSP]
  exact operatorNormalPart_normal e S
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

lemma penultimateSlice_eq_sliceAt {n : ℕ} (f : Cochain M (n+2))
    (v : Fin n → M) (c : M) :
    penultimateSlice f v c=sliceAt f (Fin.last n).castSucc (Fin.snoc v c) := by
  ext a
  rw [penultimateSlice_apply,sliceAt_apply]
  congr 1
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    rw [tupleInsert_gt _ _ _ _ (by simp)]
    symm
    exact Fin.snoc_last (α := fun _ => M) c v
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [Fin.snoc_castSucc,Fin.snoc_last,Fin.insertNth_apply_same]
    · rw [Fin.snoc_castSucc,Fin.snoc_castSucc,tupleInsert_lt _ _ _ _ (by simp)]
      symm
      exact Fin.snoc_castSucc (α := fun _ => M) c v k

lemma all_normal_of_before_penultimate {n : ℕ} (f : Cochain M (n+2))
    (hf : ∀ v,differentialValue f v=0) (hN : NormalBefore e f (n+1)) :
    ∀ (i : Fin (n+2)) v,HasPreadjoint e (sliceAt f i v) := by
  have hpen (v : Fin n → M) (c : M) : HasPreadjoint e (penultimateSlice f v c) := by
    rw [penultimateSlice_eq_sliceAt]
    exact hN _ (by simp) _
  have hlast := cocycle_last_normal_of_penultimate_normal e f hf hpen
  intro i v
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have he : sliceAt f (Fin.last (n+1)) v=f.curryRight v := by
      ext a
      simp only [sliceAt_apply,Fin.insertNth_last',ContinuousMultilinearMap.curryRight_apply]
    rw [he]
    exact hlast v
  · exact hN j.castSucc j.isLt v
end BoundedHochschild
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.all_normal_of_before_penultimate.{u} := @OAI.BoundedHochschild.all_normal_of_before_penultimate.{u}
