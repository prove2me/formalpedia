-- Prove2me | solution 1 for OAI.BoundedHochschild.arbitrary_typeII_ordinary_primitive
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:17:48.562311+00:00
-- url     : https://prove2.me/submissions/7b3ca44c-7b57-412e-a1f1-489d5c747bbb

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_HochschildNormalPart_normalProjection_fixes_normal
import Theorems.Thm_OAI_HochschildNormalPart_normalProjection_sum
import Theorems.Thm_OAI_HochschildNormalPart_functionalModel_nonempty
import Theorems.Thm_OAI_BoundedHochschild_arbitrary_typeII_last_normal_primitive

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

theorem norm_insertLast_le {n : ℕ} (f : Cochain M (n + 1)) (u : M) :
    ‖insertLast f u‖ ≤ ‖f‖ * ‖u‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  simpa [mul_assoc, mul_left_comm, mul_comm] using f.norm_map_snoc_le v u

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

lemma normalLast_normal {n : ℕ} (f : Cochain M (n+1)) (v : Fin n → M) :
    HasPreadjoint e ((normalLast e f).curryRight v) := by
  have h : (normalLast e f).curryRight v=operatorNormalPart e (f.curryRight v) := by
    ext a
    simp only [ContinuousMultilinearMap.curryRight_apply,normalLast_snoc]
  rw [h]
  exact operatorNormalPart_normal e (f.curryRight v)

lemma normalLast_identity {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v,differentialValue f v=0) (v : Fin (n+1) → M) (a : M) :
    v 0*normalLast e f (Fin.snoc (fun i : Fin n => v i.succ) a)+
      (∑ j : Fin n,((-1:ℂ)^(j.val+1)) • normalLast e f (Fin.snoc (mergeInputs v j) a))+
      ((-1:ℂ)^(n+1)) • normalLast e f (Fin.snoc (fun i : Fin n => v i.castSucc) (v (Fin.last n)*a))+
      ((-1:ℂ)^(n+2)) • (f v*a)=0 := by
  let L := ContinuousLinearMap.mul ℂ M
  have h : (L (v 0)).comp (f.curryRight (fun i : Fin n => v i.succ))+
      (∑ j : Fin n,((-1:ℂ)^(j.val+1)) • f.curryRight (mergeInputs v j))+
      ((-1:ℂ)^(n+1)) • (f.curryRight (fun i : Fin n => v i.castSucc)).comp (L (v (Fin.last n)))+
      ((-1:ℂ)^(n+2)) • L (f v)=0 := by
    ext b
    have h := hf (Fin.snoc v b)
    rw [differentialValue_snoc] at h
    simpa only [L,add_apply,sum_apply,smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mul_apply',ContinuousMultilinearMap.curryRight_apply,zero_apply] using h
  have h' := congrArg (fun T : M →L[ℂ] M => operatorNormalPart e T a) h
  dsimp only [L] at h'
  simp only [map_add,map_sum,map_smul,map_zero,zero_apply,
    operatorNormalPart_comp_normal e _ _ ((HochschildSakai.abstract_multiplication_normal e).1 (v 0)),
    operatorNormalPart_comp_left,
    operatorNormalPart_fixes e _ ((HochschildSakai.abstract_multiplication_normal e).1 (f v)),
    add_apply,sum_apply,smul_apply,ContinuousLinearMap.comp_apply] at h'
  simpa only [normalLast_snoc,ContinuousLinearMap.mul_apply'] using h'

def reducedNormalCocycle {n : ℕ} (f : Cochain M (n+1)) : Cochain M (n+1) :=
  normalLast e f-rightCoboundary (insertLast (normalLast e f) 1)

def normalCorrection {n : ℕ} (f : Cochain M (n+1)) : Cochain M n :=
  ((-1:ℂ)^(n+1)) • insertLast (normalLast e f) 1

lemma sign_square (k : ℕ) : (-1:ℂ)^k*(-1:ℂ)^k=1 := by
  rw [← mul_pow]
  simp

lemma sign_succ (k : ℕ) : (-1:ℂ)^(k+1) = -((-1:ℂ)^k) := by
  rw [pow_succ]
  ring

lemma normal_correction_identity {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v,differentialValue f v=0) (v : Fin (n+1) → M) :
    f v=reducedNormalCocycle e f v+differentialValue (normalCorrection e f) v := by
  let F := normalLast e f
  let h := insertLast F 1
  let s := (-1:ℂ)^(n+1)
  have he := normalLast_identity e f hf v 1
  have hs : (-1:ℂ)^(n+2) = -s := sign_succ (n+1)
  have hv : Fin.snoc (fun i : Fin n => v i.castSucc) (v (Fin.last n))=v := Fin.snoc_init_self v
  simp only [mul_one,hv,hs] at he
  have hA : differentialValue h v+s • (F v-rightCoboundary h v)-s • f v=0 := by
    change v 0*F (Fin.snoc (fun i : Fin n => v i.succ) 1)+
      (∑ j : Fin n,((-1:ℂ)^(j.val+1)) • F (Fin.snoc (mergeInputs v j) 1))+
      s • F v+(-s) • f v=0 at he
    dsimp only [h]
    simp only [differentialValue,insertLast_apply,rightCoboundary_apply,smul_sub,neg_smul] at *
    linear_combination (norm := module) he
  have hB : differentialValue h v+s • (F v-rightCoboundary h v)=s • f v := sub_eq_zero.mp hA
  have hC := congrArg (fun b : M => s • b) hB
  simp only [smul_add,smul_smul,show s*s=1 from sign_square (n+1),one_smul] at hC
  rw [normalCorrection,differentialValue_smul]
  change f v=(F v-rightCoboundary h v)+s • differentialValue h v
  exact hC.symm.trans (add_comm _ _)

lemma reducedNormalCocycle_normal {n : ℕ} (f : Cochain M (n+1)) (v : Fin n → M) :
    HasPreadjoint e ((reducedNormalCocycle e f).curryRight v) := by
  intro z
  obtain ⟨z₁,hz₁⟩ := normalLast_normal e f v z
  obtain ⟨z₂,hz₂⟩ := (HochschildSakai.abstract_multiplication_normal e).1
    (insertLast (normalLast e f) 1 v) z
  refine ⟨z₁-z₂,?_⟩
  intro a
  simp only [reducedNormalCocycle,ContinuousMultilinearMap.curryRight_apply,
    sub_apply,rightCoboundary_apply,Fin.snoc_castSucc,Fin.snoc_last]
  change e.symm (normalLast e f (Fin.snoc v a) - insertLast (normalLast e f) 1 v*a) z =
    e.symm a (z₁-z₂)
  rw [map_sub,sub_apply,map_sub]
  exact congrArg₂ (·-·) (hz₁ a) (hz₂ a)

lemma differentialValue_sub {n : ℕ} (f g : Cochain M n) (v : Fin (n+1) → M) :
    differentialValue (f-g) v=differentialValue f v-differentialValue g v := by
  rw [sub_eq_add_neg,show -g=(-1:ℂ) • g by simp,differentialValue_add,differentialValue_smul]
  simp [sub_eq_add_neg]

lemma rightCoboundary_differential {n : ℕ} (h : Cochain M n)
    (v : Fin (n+1) → M) (a : M) :
    differentialValue (rightCoboundary h) (Fin.snoc v a)=
      (differentialValue h v-((-1:ℂ)^(n+1)) • rightCoboundary h v)*a := by
  rw [differentialValue_snoc,sign_succ (n+1)]
  simp only [rightCoboundary_apply,Fin.snoc_castSucc,Fin.snoc_last,differentialValue,
    add_mul,sub_mul,Finset.sum_mul,smul_mul_assoc,mul_assoc,neg_smul]
  abel

lemma reducedNormalCocycle_cocycle {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v,differentialValue f v=0) (x : Fin (n+2) → M) :
    differentialValue (reducedNormalCocycle e f) x=0 := by
  let v : Fin (n+1) → M := fun i => x i.castSucc
  let a := x (Fin.last (n+1))
  have hx : x=Fin.snoc v a := (Fin.snoc_init_self x).symm
  rw [hx,reducedNormalCocycle,differentialValue_sub,rightCoboundary_differential,differentialValue_snoc]
  have h := normalLast_identity e f hf v a
  have hv := normal_correction_identity e f hf v
  rw [reducedNormalCocycle,sub_apply,normalCorrection,differentialValue_smul] at hv
  have hs : (-1:ℂ)^(n+2) = -((-1:ℂ)^(n+1)) := sign_succ (n+1)
  rw [hs] at h ⊢
  rw [hv] at h
  simp only [add_mul,sub_mul,smul_mul_assoc,smul_add,smul_sub,neg_smul,smul_smul,
    neg_mul,sign_square,one_smul] at h ⊢
  linear_combination (norm := module) h

lemma normalLast_norm {n : ℕ} (f : Cochain M (n+1)) : ‖normalLast e f‖≤4*‖f‖ := by
  have hN : ‖operatorNormalPart e‖≤4 :=
    LinearMap.mkContinuous_norm_le _ (by norm_num) (normalOperator_norm e)
  rw [normalLast,ContinuousMultilinearMap.uncurryRight_norm]
  calc
    _ ≤ ‖operatorNormalPart e‖*‖f.curryRight‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 4*‖f‖ := by rw [ContinuousMultilinearMap.curryRight_norm]; gcongr

lemma rightCoboundary_norm {n : ℕ} (f : Cochain M n) : ‖rightCoboundary f‖≤‖f‖ := by
  rw [rightCoboundary,ContinuousMultilinearMap.uncurryRight_norm]
  calc
    _ ≤ ‖ContinuousLinearMap.mul ℂ M‖*‖f‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1*‖f‖ := mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℂ M) (norm_nonneg _)
    _ = _ := one_mul _

lemma insertLast_one_norm {n : ℕ} (f : Cochain M (n+1)) : ‖insertLast f 1‖≤‖f‖ := by
  have h : ‖(1:M)‖≤1 := by
    rcases subsingleton_or_nontrivial M with h|h
    · simp [Subsingleton.elim (1:M) 0]
    · simp
  exact (norm_insertLast_le f 1).trans ((mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (mul_one _))

lemma reducedNormalCocycle_norm {n : ℕ} (f : Cochain M (n+1)) :
    ‖reducedNormalCocycle e f‖≤8*‖f‖ := by
  have h := (rightCoboundary_norm (insertLast (normalLast e f) 1)).trans (insertLast_one_norm _)
  have hN := normalLast_norm e f
  exact (norm_sub_le _ _).trans (by linarith)

lemma normalCorrection_norm {n : ℕ} (f : Cochain M (n+1)) : ‖normalCorrection e f‖≤4*‖f‖ := by
  simpa only [normalCorrection,norm_smul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    using (insertLast_one_norm (normalLast e f)).trans (normalLast_norm e f)
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace BoundedHochschild
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hII : PopaTypeII.NoAbelianCorners M)

include e τ hτ htr hfaith h1 hII

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace PopaSeparable
open BoundedHochschild PopaCenter PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
variable (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
  (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
  (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

end PopaSeparable

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hII : PopaTypeII.NoAbelianCorners M)
include e hτ htr hfaith h1 hII

theorem arbitrary_typeII_ordinary_primitive {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v, differentialValue f v=0) :
    ∃ g : Cochain M n, ‖g‖≤12*‖f‖ ∧ ∀ v, differentialValue g v=f v := by
  obtain ⟨g,hg,hgf⟩ := arbitrary_typeII_last_normal_primitive e τ hτ htr hfaith h1 hII
    (reducedNormalCocycle e f) (reducedNormalCocycle_cocycle e f hf)
    (reducedNormalCocycle_normal e f)
  refine ⟨g+normalCorrection e f, ?_, ?_⟩
  · have hF := reducedNormalCocycle_norm e f
    have hh := normalCorrection_norm e f
    exact (norm_add_le _ _).trans (by linarith)
  · intro v
    rw [differentialValue_add,hgf]
    exact (normal_correction_identity e f hf v).symm
end BoundedHochschild
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.arbitrary_typeII_ordinary_primitive.{u} := @OAI.BoundedHochschild.arbitrary_typeII_ordinary_primitive.{u}
