-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.properlyInfiniteVanishingInput
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:26:44.484813+00:00
-- url     : https://prove2.me/submissions/66973699-6675-4c44-9909-04ebe7d03e1c

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_exists_countable_isometries
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_primitive_of_algebraic_matrix_multimodular

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
variable {M X I : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

theorem bounded_cochain_ultralimit {n : ℕ} (u : Ultrafilter I)
    (F : I → Cochain M n) (C : ℝ) (hC : 0 ≤ C) (hF : ∀ i, ‖F i‖ ≤ C) :
    ∃ G : Cochain M n, ‖G‖ ≤ C ∧
      ∀ x, PredualTendsto e (fun i => F i x) u (G x) := by
  classical
  have hex (x : Fin n → M) : ∃ b : M, ‖b‖ ≤ C * ∏ k, ‖x k‖ ∧
      PredualTendsto e (fun i => F i x) u b :=
    exists_predual_ultralimit e u (fun i => F i x) _ (fun i =>
      (F i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hF i)
        (Finset.prod_nonneg (fun k _ => norm_nonneg (x k)))))
  choose b hb ht using hex
  let G₀ : MultilinearMap ℂ (fun _ : Fin n => M) M :=
    { toFun := b
      map_update_add' := fun x k a c => by
        apply predual_tendsto_unique e (ht (Function.update x k (a+c)))
        simpa only [ContinuousMultilinearMap.map_update_add] using
          predual_tendsto_add e (ht (Function.update x k a)) (ht (Function.update x k c))
      map_update_smul' := fun x k c a => by
        apply predual_tendsto_unique e (ht (Function.update x k (c • a)))
        simpa only [ContinuousMultilinearMap.map_update_smul] using
          predual_tendsto_smul e (ht (Function.update x k a)) c }
  exact ⟨G₀.mkContinuous C hb, G₀.mkContinuous_norm_le hC hb, ht⟩

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M X I J : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma predual_tendsto_sum {a : I → J → M} {b : J → M} (l : Filter I) (s : Finset J)
    (h : ∀ j ∈ s, PredualTendsto e (fun i => a i j) l (b j)) :
    PredualTendsto e (fun i => ∑ j ∈ s, a i j) l (∑ j ∈ s, b j) := by
  intro z
  simpa only [map_sum,sum_apply] using
    tendsto_finsetSum s (fun j hj => h j hj z)
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
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

end BoundedHochschild

namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity HochschildLiouville TracialUltrapower
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))

include h1 htr

end BoundedHochschild

open MeasureTheory Filter Topology
open scoped ENNReal
namespace HochschildWalk
variable {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]

end HochschildWalk

namespace BoundedHochschild
open HochschildWalk
variable {M : Type*} [CStarAlgebra M]
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableSingletonClass G]

end BoundedHochschild

open MeasureTheory Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildWalk HochschildLiouville TracialUltrapower
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma predual_tendsto_differential
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    {n : ℕ} {F : I → Cochain M n} {G : Cochain M n} {l : Filter I}
    (ht : ∀ x, PredualTendsto e (fun i => F i x) l (G x))
    (x : Fin (n+1) → M) :
    PredualTendsto e (fun i => differentialValue (F i) x) l (differentialValue G x) := by
  simp only [differentialValue]
  apply predual_tendsto_add e
  · apply predual_tendsto_add e
    · exact (hL (x 0)).tendsto e (ht _)
    · apply predual_tendsto_sum e l Finset.univ
      intro j _
      exact predual_tendsto_smul e (ht _) _
  · exact predual_tendsto_smul e ((hR (x (Fin.last n))).tendsto e (ht _)) _
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
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped ComplexOrder
namespace HochschildComparison
variable {M : Type*} [CStarAlgebra M]

namespace PartialIso

lemma final_mul (v : PartialIso M) : v.final * (v : M) = v := v.mul_star_mul

lemma final_proj (v : PartialIso M) : IsStarProjection v.final := by
  refine ⟨?_, IsSelfAdjoint.mul_star_self _⟩
  change ((v : M) * star (v : M)) * ((v : M) * star (v : M)) = (v : M) * star (v : M)
  calc
    _ = ((v : M) * star (v : M) * v) * star (v : M) := by simp only [mul_assoc]
    _ = _ := by rw [v.mul_star_mul]

variable [PartialOrder M]

variable [StarOrderedRing M]

section
omit [PartialOrder M] [StarOrderedRing M]

lemma star_mul_eq_zero_of_final_orthogonal {v w : PartialIso M}
    (h : v.final*w.final=0) : star (v : M)*w=0 := by
  have hv : star (v : M)*v.final=star (v : M) := by
    simpa only [star_mul,star_star,v.final_proj.isSelfAdjoint.star_eq]
      using congrArg star v.final_mul
  calc
    star (v : M)*w = (star (v : M)*v.final)*(w.final*(w : M)) := by
      rw [hv,w.final_mul]
    _ = star (v : M)*(v.final*w.final)*(w : M) := by simp only [mul_assoc]
    _ = 0 := by rw [h,mul_zero,zero_mul]
end
end PartialIso
end HochschildComparison
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {I : Type v}

omit [PartialOrder M] [StarOrderedRing M] in
lemma orthogonal_projection_finset_sum (p : I → M)
    (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i * p j = 0) (s : Finset I) :
    IsStarProjection (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      rw [Finset.sum_insert his]
      apply (hp i).add ih
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact horth i j (fun hij => his (hij ▸ hj))
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped BigOperators

namespace HochschildMatrixSystems
namespace MatrixSystem

variable {M : Type*} [CStarAlgebra M] {n : ℕ} (E : MatrixSystem M n)

def signScalar (b : Bool) : ℂ := if b then -1 else 1

lemma signScalar_xor (a b : Bool) : signScalar (a ^^ b) = signScalar a * signScalar b := by
  cases a <;> cases b <;> norm_num [signScalar]

@[simp] lemma signScalar_star (a : Bool) : star (signScalar a) = signScalar a := by
  cases a <;> simp [signScalar]

def signedPermutation (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) : M :=
  ∑ i, signScalar (s i) • E.entry (σ i) i

lemma signedPermutation_one : E.signedPermutation 1 (fun _ => false) = 1 := by
  simpa only [signedPermutation, signScalar, Bool.false_eq_true, ↓reduceIte,
    one_smul, Equiv.Perm.one_apply] using E.sum_diagonal

lemma signedPermutation_mul (σ τ : Equiv.Perm (Fin n)) (s t : Fin n → Bool) :
    E.signedPermutation σ s * E.signedPermutation τ t =
      E.signedPermutation (σ * τ) (fun i => s (τ i) ^^ t i) := by
  classical
  simp only [signedPermutation, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm,
    E.entry_mul, smul_ite, smul_zero]
  simp [signScalar_xor, Equiv.Perm.mul_apply]

lemma signedPermutation_star (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) :
    star (E.signedPermutation σ s) =
      E.signedPermutation σ⁻¹ (fun i => s (σ⁻¹ i)) := by
  classical
  simp only [signedPermutation, star_sum, star_smul, signScalar_star, E.star_entry]
  apply Fintype.sum_equiv σ _ _
  intro i
  simp

lemma signedPermutation_mem_unitary (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) :
    E.signedPermutation σ s ∈ unitary M := by
  constructor
  · rw [E.signedPermutation_star, E.signedPermutation_mul, inv_mul_cancel]
    simpa using E.signedPermutation_one
  · rw [E.signedPermutation_star, E.signedPermutation_mul, mul_inv_cancel]
    simpa only [Bool.xor_self] using E.signedPermutation_one

def signedPermutationUnitary (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) : unitary M :=
  ⟨E.signedPermutation σ s, E.signedPermutation_mem_unitary σ s⟩

def signedPermutationGroup : Subgroup (unitary M) where
  carrier := Set.range (fun p : Equiv.Perm (Fin n) × (Fin n → Bool) =>
    E.signedPermutationUnitary p.1 p.2)
  one_mem' := ⟨(1, fun _ => false), Subtype.ext E.signedPermutation_one⟩
  mul_mem' := by
    rintro _ _ ⟨⟨σ, s⟩, rfl⟩ ⟨⟨τ, t⟩, rfl⟩
    exact ⟨(σ * τ, fun i => s (τ i) ^^ t i), Subtype.ext (E.signedPermutation_mul σ τ s t).symm⟩
  inv_mem' := by
    rintro _ ⟨⟨σ, s⟩, rfl⟩
    exact ⟨(σ⁻¹, fun i => s (σ⁻¹ i)), Subtype.ext (E.signedPermutation_star σ s).symm⟩

instance signedPermutationGroup_finite : Finite E.signedPermutationGroup :=
  (Set.finite_range _).to_subtype

lemma signedPermutation_flip (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    E.signedPermutation σ (fun _ => false) -
      E.signedPermutation σ (fun k => decide (k = j)) = (2 : ℂ) • E.entry (σ j) j := by
  classical
  simp only [signedPermutation, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single j]
  · simp [signScalar, two_smul]
  · intro k _ hkj
    simp [signScalar, hkj]
  · simp
end MatrixSystem
end HochschildMatrixSystems
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild

variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

theorem predual_tendsto_differential_of_predual
    {n : ℕ} {F : I → Cochain M n} {G : Cochain M n} {l : Filter I}
    (h : ∀ x, PredualTendsto e (fun i => F i x) l (G x))
    (x : Fin (n + 1) → M) :
    PredualTendsto e (fun i => differentialValue (F i) x) l (differentialValue G x) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  exact predual_tendsto_differential e (HochschildSakai.mul_hasPreadjoint e)
    (HochschildSakai.mul_right_hasPreadjoint e) h x
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma countableColumn_star_mul (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) (i j : ℕ) :
    star (c i : M) * (c j : M) = if i = j then 1 else 0 := by
  split_ifs with h
  · subst j; exact hi i
  · exact PartialIso.star_mul_eq_zero_of_final_orthogonal (ho i j h)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped Pointwise

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M]

def countableMatrixUnit (c : ℕ → PartialIso M) (i j : ℕ) : M :=
  (c i : M) * star (c j : M)

@[simp] lemma countableMatrixUnit_star (c : ℕ → PartialIso M) (i j : ℕ) :
    star (countableMatrixUnit c i j) = countableMatrixUnit c j i := by
  simp [countableMatrixUnit]

lemma countableMatrixUnit_mul (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) (i j k l : ℕ) :
    countableMatrixUnit c i j * countableMatrixUnit c k l =
      if j = k then countableMatrixUnit c i l else 0 := by
  calc
    _ = (c i : M) * (star (c j : M) * (c k : M)) * star (c l : M) := by
      simp only [countableMatrixUnit, mul_assoc]
    _ = _ := by rw [countableColumn_star_mul c hi ho]; split_ifs <;> simp [countableMatrixUnit]

def countableMatrixWordMonoid (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) : Submonoid M where
  carrier := {a | a = 0 ∨ a = 1 ∨ ∃ i j, a = countableMatrixUnit c i j}
  one_mem' := Or.inr (Or.inl rfl)
  mul_mem' := by
    rintro a b (rfl | rfl | ⟨i, j, rfl⟩) hb
    · exact Or.inl (zero_mul b)
    · simpa only [one_mul] using hb
    · rcases hb with rfl | rfl | ⟨k, l, rfl⟩
      · exact Or.inl (mul_zero _)
      · exact Or.inr (Or.inr ⟨i, j, mul_one _⟩)
      · rw [countableMatrixUnit_mul c hi ho]
        split_ifs
        · exact Or.inr (Or.inr ⟨i, l, rfl⟩)
        · exact Or.inl rfl

lemma countableMatrixWordMonoid_star (c : ℕ → PartialIso M) (hi ho)
    {a : M} (ha : a ∈ countableMatrixWordMonoid c hi ho) :
    star a ∈ countableMatrixWordMonoid c hi ho := by
  rcases ha with rfl | rfl | ⟨i, j, rfl⟩
  · exact Or.inl (star_zero M)
  · exact Or.inr (Or.inl (star_one M))
  · exact Or.inr (Or.inr ⟨j, i, countableMatrixUnit_star c i j⟩)

theorem countableMatrixAlgebra_eq_span (c : ℕ → PartialIso M)
    (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) :
    (countableMatrixAlgebra c).toSubalgebra.toSubmodule =
      Submodule.span ℂ ({1} ∪ Set.range (fun p : ℕ × ℕ => countableMatrixUnit c p.1 p.2)) := by
  let S := Set.range (fun p : ℕ × ℕ => countableMatrixUnit c p.1 p.2)
  let P := Submodule.span ℂ ({1} ∪ S)
  have hS : S ⊆ countableMatrixWordMonoid c hi ho := by
    rintro a ⟨⟨i, j⟩, rfl⟩
    exact Or.inr (Or.inr ⟨i, j, rfl⟩)
  have hgen : S ∪ star S ⊆ countableMatrixWordMonoid c hi ho := by
    intro a ha
    rcases ha with ha | ha
    · exact hS ha
    · have ha' : star a ∈ S := by simpa only [Set.mem_star] using ha
      have hstar := countableMatrixWordMonoid_star c hi ho (hS ha')
      change star (star a) = 0 ∨ star (star a) = 1 ∨
        ∃ i j, star (star a) = countableMatrixUnit c i j at hstar
      change a = 0 ∨ a = 1 ∨ ∃ i j, a = countableMatrixUnit c i j
      simpa only [star_star] using hstar
  have hwords : Submonoid.closure (S ∪ star S) ≤ countableMatrixWordMonoid c hi ho :=
    Submonoid.closure_le.mpr hgen
  apply le_antisymm
  · change (StarAlgebra.adjoin ℂ S).toSubalgebra.toSubmodule ≤ P
    rw [StarAlgebra.adjoin_eq_span]
    apply Submodule.span_le.mpr
    intro a ha
    rcases hwords ha with rfl | rfl | ⟨i, j, rfl⟩
    · exact P.zero_mem
    · exact Submodule.subset_span (Or.inl (Set.mem_singleton 1))
    · exact Submodule.subset_span (Or.inr ⟨(i, j), rfl⟩)
  · apply Submodule.span_le.mpr
    intro a ha
    rcases ha with ha | ha
    · have ha1 : a = 1 := Set.mem_singleton_iff.mp ha
      subst a
      exact (countableMatrixAlgebra c).one_mem
    · exact StarAlgebra.subset_adjoin ℂ S ha
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] {n : ℕ}
variable (c : Fin n → PartialIso M) (hi : ∀ i, (c i).initial = 1)
  (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
  (hs : ∑ i, (c i).final = 1)

include hi ho in
lemma column_star_mul (i j : Fin n) :
    star (c i : M) * (c j : M) = if i = j then 1 else 0 := by
  split_ifs with h
  · subst j
    exact hi i
  · exact PartialIso.star_mul_eq_zero_of_final_orthogonal (ho i j h)
end BoundedHochschild.KadisonRingrose
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

variable {M : Type*} [CStarAlgebra M]

lemma multimodularAt_one {n : ℕ} (f : Cochain M (n + 1)) : MultimodularAt f 1 := by
  constructor <;> intros <;> simp

lemma linear_maps_eq_on_span (S : Set M) (T U : M →L[ℂ] M)
    (h : ∀ r ∈ S, T r = U r) {a : M} (ha : a ∈ Submodule.span ℂ S) : T a = U a := by
  have hker : Submodule.span ℂ S ≤ (T - U).ker := by
    apply Submodule.span_le.mpr
    intro r hr
    change T r - U r = 0
    exact sub_eq_zero.mpr (h r hr)
  have hzero := hker ha
  change T a - U a = 0 at hzero
  exact sub_eq_zero.mp hzero

lemma multimodularAt_of_span {n : ℕ} (f : Cochain M (n + 1)) (S : Set M)
    (hS : ∀ r ∈ S, MultimodularAt f r) {a : M} (ha : a ∈ Submodule.span ℂ S) :
    MultimodularAt f a := by
  constructor
  · intro x
    have h := linear_maps_eq_on_span S
      ((updateSlice f 0 x).comp ((ContinuousLinearMap.mul ℂ M).flip (x 0)))
      ((ContinuousLinearMap.mul ℂ M).flip (f x))
      (fun r hr => by simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using (hS r hr).left x) ha
    simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using h
  · intro x
    have h := linear_maps_eq_on_span S
      ((updateSlice f (Fin.last n) x).comp (ContinuousLinearMap.mul ℂ M (x (Fin.last n))))
      (ContinuousLinearMap.mul ℂ M (f x))
      (fun r hr => by simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
        ContinuousLinearMap.mul_apply'] using (hS r hr).right x) ha
    simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
      ContinuousLinearMap.mul_apply'] using h
  · intro x j
    have h := linear_maps_eq_on_span S
      ((updateSlice f j.castSucc x).comp (ContinuousLinearMap.mul ℂ M (x j.castSucc)))
      ((updateSlice f j.succ x).comp ((ContinuousLinearMap.mul ℂ M).flip (x j.succ)))
      (fun r hr => by simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using (hS r hr).balance x j) ha
    simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using h

theorem multimodular_of_matrixUnits (c : ℕ → HochschildComparison.PartialIso M)
    (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f : Cochain M (n + 1)) (hf : ∀ i j, MultimodularAt f (countableMatrixUnit c i j)) :
    MultimodularOver (countableMatrixAlgebra c) f := by
  have hS : ∀ r ∈ ({1} ∪ Set.range (fun p : ℕ × ℕ => countableMatrixUnit c p.1 p.2)),
      MultimodularAt f r := by
    intro r hr
    rcases hr with hr | ⟨⟨i, j⟩, rfl⟩
    · have hr1 : r = 1 := Set.mem_singleton_iff.mp hr
      subst r
      exact multimodularAt_one f
    · exact hf i j
  have hA : ∀ r ∈ countableMatrixAlgebra c, MultimodularAt f r := by
    intro r hr
    apply multimodularAt_of_span f _ hS
    rw [← countableMatrixAlgebra_eq_span c hi ho]
    exact hr
  exact ⟨fun r hr => (hA r hr).left, fun r hr => (hA r hr).right,
    fun r hr => (hA r hr).balance⟩
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u v
variable {M : Type u} [CStarAlgebra M]

private def unitaryBimultiply (u v : unitary M) : M →L[ℂ] M :=
  (ContinuousLinearMap.mul ℂ M (u : M)).comp
    ((ContinuousLinearMap.mul ℂ M).flip (v : M))

private lemma unitaryBimultiply_apply (u v : unitary M) (a : M) :
    unitaryBimultiply u v a = (u : M) * a * (v : M) := by
  simp only [unitaryBimultiply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply, mul_assoc]

def cochainUnitaryTuple {n : ℕ} (u : Fin (n + 1) → unitary M) (x : Fin n → M) : Fin n → M :=
  fun i => (u i.castSucc : M) * x i * star (u i.succ : M)

def cochainUnitaryTransport {n : ℕ} (u : Fin (n + 1) → unitary M)
    (f : Cochain M n) : Cochain M n :=
  (unitaryBimultiply (star (u 0)) (u (Fin.last n))).compContinuousMultilinearMap
    (f.compContinuousLinearMap (fun i => unitaryBimultiply (u i.castSucc) (star (u i.succ))))

@[simp] lemma cochainUnitaryTransport_apply {n : ℕ} (u : Fin (n + 1) → unitary M)
    (f : Cochain M n) (x : Fin n → M) :
    cochainUnitaryTransport u f x =
      star (u 0 : M) * f (cochainUnitaryTuple u x) * (u (Fin.last n) : M) := by
  change unitaryBimultiply _ _ (f (fun i => unitaryBimultiply _ _ (x i))) = _
  simp only [unitaryBimultiply_apply, Unitary.coe_star]
  rfl

lemma cochainUnitaryTransport_norm {n : ℕ} (u : Fin (n + 1) → unitary M)
    (f : Cochain M n) : ‖cochainUnitaryTransport u f‖ ≤ ‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  rw [cochainUnitaryTransport_apply]
  change ‖((star (u 0) : unitary M) : M) * f (cochainUnitaryTuple u x) *
    (u (Fin.last n) : M)‖ ≤ _
  rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  have hp : (∏ i, ‖cochainUnitaryTuple u x i‖) = ∏ i, ‖x i‖ := by
    apply Finset.prod_congr rfl
    intro i _
    change ‖(u i.castSucc : M) * x i * ((star (u i.succ) : unitary M) : M)‖ = ‖x i‖
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  have hb := f.le_opNorm (cochainUnitaryTuple u x)
  rwa [hp] at hb

lemma cochainUnitaryTransport_add {n : ℕ} (u : Fin (n + 1) → unitary M)
    (f g : Cochain M n) :
    cochainUnitaryTransport u (f + g) = cochainUnitaryTransport u f + cochainUnitaryTransport u g := by
  ext x
  simp only [cochainUnitaryTransport_apply, add_apply, mul_add, add_mul]

lemma cochainUnitaryTransport_smul {n : ℕ} (u : Fin (n + 1) → unitary M)
    (z : ℂ) (f : Cochain M n) :
    cochainUnitaryTransport u (z • f) = z • cochainUnitaryTransport u f := by
  ext x
  simp only [cochainUnitaryTransport_apply, smul_apply, mul_smul_comm, smul_mul_assoc]

def cochainUnitaryTransportCLM {n : ℕ} (u : Fin (n + 1) → unitary M) :
    Cochain M n →L[ℂ] Cochain M n :=
  LinearMap.mkContinuous
    { toFun := cochainUnitaryTransport u
      map_add' := cochainUnitaryTransport_add u
      map_smul' := cochainUnitaryTransport_smul u }
    1 (fun f => by
      change ‖cochainUnitaryTransport u f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using cochainUnitaryTransport_norm u f)

@[simp] lemma cochainUnitaryTransportCLM_apply {n : ℕ} (u : Fin (n + 1) → unitary M)
    (f : Cochain M n) : cochainUnitaryTransportCLM u f = cochainUnitaryTransport u f := rfl

lemma cochainUnitaryTransport_comp {n : ℕ} (u v : Fin (n + 1) → unitary M)
    (f : Cochain M n) :
    cochainUnitaryTransport u (cochainUnitaryTransport v f) =
      cochainUnitaryTransport (v * u) f := by
  ext x
  simp only [cochainUnitaryTransport_apply, Pi.mul_apply, Submonoid.coe_mul, star_mul]
  have ht : cochainUnitaryTuple v (cochainUnitaryTuple u x) = cochainUnitaryTuple (v * u) x := by
    ext i
    simp only [cochainUnitaryTuple, Pi.mul_apply, Submonoid.coe_mul, star_mul, mul_assoc]
  rw [ht]
  simp only [mul_assoc]

variable {G : Type v} [Group G] [Fintype G]

def finiteGroupCochainAverage {n : ℕ} (ρ : G →* unitary M) (f : Cochain M n) : Cochain M n :=
  (Fintype.card (Fin (n + 1) → G) : ℂ)⁻¹ •
    ∑ g : Fin (n + 1) → G, cochainUnitaryTransport (fun i => ρ (g i)) f

lemma finiteGroupCochainAverage_norm {n : ℕ} (ρ : G →* unitary M) (f : Cochain M n) :
    ‖finiteGroupCochainAverage ρ f‖ ≤ ‖f‖ := by
  let K := Fin (n + 1) → G
  have hc : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  rw [finiteGroupCochainAverage, norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card K : ℝ)⁻¹ * ((Fintype.card K : ℝ) * ‖f‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      exact (norm_sum_le _ _).trans (by
        simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
          Finset.sum_le_sum (s := Finset.univ) (fun (g : Fin (n + 1) → G) _ =>
            cochainUnitaryTransport_norm (fun i => ρ (g i)) f))
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]

lemma finiteGroupCochainAverage_invariant {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M n) (h : Fin (n + 1) → G) :
    cochainUnitaryTransport (fun i => ρ (h i)) (finiteGroupCochainAverage ρ f) =
      finiteGroupCochainAverage ρ f := by
  change cochainUnitaryTransportCLM (fun i => ρ (h i)) _ = _
  rw [finiteGroupCochainAverage, map_smul, map_sum]
  congr 1
  calc
    _ = ∑ g : Fin (n + 1) → G, cochainUnitaryTransport (fun i => ρ ((g * h) i)) f := by
      apply Finset.sum_congr rfl
      intro g _
      rw [cochainUnitaryTransportCLM_apply, cochainUnitaryTransport_comp]
      congr 1
      funext i
      exact (map_mul ρ (g i) (h i)).symm
    _ = _ := by
      apply Fintype.sum_equiv (Equiv.mulRight h) _ _
      intro g
      rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u v
variable {M : Type u} [CStarAlgebra M]

lemma cochainUnitaryTransport_fixed_value {n : ℕ} (u : Fin (n + 1) → unitary M)
    (f : Cochain M n) (hf : cochainUnitaryTransport u f = f) (x : Fin n → M) :
    f (cochainUnitaryTuple u x) = (u 0 : M) * f x * star (u (Fin.last n) : M) := by
  have h := congrArg (fun F : Cochain M n => (u 0 : M) * F x * star (u (Fin.last n) : M)) hf
  simp only [cochainUnitaryTransport_apply, mul_assoc,
    Unitary.mul_star_self_of_mem (u (Fin.last n)).property, mul_one] at h
  rw [← mul_assoc, Unitary.mul_star_self_of_mem (u 0).property, one_mul] at h
  simpa only [mul_assoc] using h

lemma cochainUnitaryTuple_left {n : ℕ} (u : unitary M) (x : Fin (n + 1) → M) :
    cochainUnitaryTuple (Function.update (fun _ : Fin (n + 2) => 1) 0 u) x =
      Function.update x 0 ((u : M) * x 0) := by
  ext i
  by_cases hi : i = 0
  · subst i
    simp [cochainUnitaryTuple]
  · have hi0 : i.castSucc ≠ (0 : Fin (n + 2)) := by
      intro h
      exact hi (Fin.ext (congrArg (fun z : Fin (n + 2) => z.val) h))
    simp [cochainUnitaryTuple, hi, hi0]

lemma cochainUnitaryTuple_right {n : ℕ} (u : unitary M) (x : Fin (n + 1) → M) :
    cochainUnitaryTuple (Function.update (fun _ : Fin (n + 2) => 1) (Fin.last (n + 1)) u) x =
      Function.update x (Fin.last n) (x (Fin.last n) * star (u : M)) := by
  ext i
  by_cases hi : i = Fin.last n
  · subst i
    simp [cochainUnitaryTuple]
  · have hiL : i.succ ≠ Fin.last (n + 1) := by
      intro h
      apply hi
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_last] at hv ⊢
      omega
    simp [cochainUnitaryTuple, hi, hiL]

lemma cochainUnitaryTuple_internal {n : ℕ} (u : unitary M) (x : Fin (n + 1) → M) (j : Fin n) :
    cochainUnitaryTuple (Function.update (fun _ : Fin (n + 2) => 1) j.castSucc.succ u) x =
      Function.update (Function.update x j.castSucc (x j.castSucc * star (u : M)))
        j.succ ((u : M) * x j.succ) := by
  have hjs : j.castSucc ≠ j.succ := ne_of_lt Fin.castSucc_lt_succ
  ext i
  by_cases hi : i = j.castSucc
  · subst i
    have hne : j.castSucc.castSucc ≠ j.castSucc.succ := ne_of_lt Fin.castSucc_lt_succ
    simp only [cochainUnitaryTuple, Function.update_of_ne hne, Function.update_self,
      Function.update_of_ne hjs, OneMemClass.coe_one, one_mul]
  · by_cases hi' : i = j.succ
    · subst i
      have hne : j.succ.succ ≠ j.castSucc.succ := by
        simpa only [ne_eq, Fin.succ_inj] using hjs.symm
      have heq : j.succ.castSucc = j.castSucc.succ := Fin.castSucc_succ j
      simp only [cochainUnitaryTuple, heq, Function.update_self, Function.update_of_ne hne,
        OneMemClass.coe_one, star_one, mul_one]
    · have hneL : i.castSucc ≠ j.castSucc.succ := by
        simpa only [← Fin.castSucc_succ, ne_eq, Fin.castSucc_inj] using hi'
      have hneR : i.succ ≠ j.castSucc.succ := by
        simpa only [ne_eq, Fin.succ_inj] using hi
      simp only [cochainUnitaryTuple, Function.update_of_ne hneL, Function.update_of_ne hneR,
        Function.update_of_ne hi, Function.update_of_ne hi', OneMemClass.coe_one,
        star_one, one_mul, mul_one]

variable {G : Type v} [Group G] [Fintype G]

lemma finiteGroupCochainAverage_multimodularAt {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) (g : G) :
    MultimodularAt (finiteGroupCochainAverage ρ f) (ρ g : M) := by
  let F := finiteGroupCochainAverage ρ f
  have hvalue (h : Fin (n + 2) → G) (x : Fin (n + 1) → M) :
      F (cochainUnitaryTuple (fun i => ρ (h i)) x) =
        (ρ (h 0) : M) * F x * star (ρ (h (Fin.last (n + 1))) : M) :=
    cochainUnitaryTransport_fixed_value _ F (finiteGroupCochainAverage_invariant ρ f h) x
  have hρ (i : Fin (n + 2)) (h : G) :
      (fun k => ρ (Function.update (fun _ : Fin (n + 2) => (1 : G)) i h k)) =
        Function.update (fun _ : Fin (n + 2) => 1) i (ρ h) := by
    ext k
    by_cases hk : k = i <;> simp [hk]
  constructor
  · intro x
    have h := hvalue (Function.update (fun _ => 1) 0 g) x
    rw [hρ, cochainUnitaryTuple_left] at h
    simpa using h
  · intro x
    have h := hvalue (Function.update (fun _ => 1) (Fin.last (n + 1)) g⁻¹) x
    rw [hρ, cochainUnitaryTuple_right] at h
    have hu : star (ρ g⁻¹ : M) = (ρ g : M) := by
      rw [map_inv]
      change star (star (ρ g : M)) = (ρ g : M)
      exact star_star _
    simpa only [Function.update_self, map_one, OneMemClass.coe_one, one_mul,
      Function.update_of_ne (by simp : (0 : Fin (n + 2)) ≠ Fin.last (n + 1)), hu] using h
  · intro x j
    let y := Function.update x j.castSucc (x j.castSucc * (ρ g : M))
    have h := hvalue (Function.update (fun _ => 1) j.castSucc.succ g) y
    rw [hρ, cochainUnitaryTuple_internal] at h
    have hz : Function.update
        (Function.update y j.castSucc (y j.castSucc * star (ρ g : M)))
        j.succ ((ρ g : M) * y j.succ) =
        Function.update x j.succ ((ρ g : M) * x j.succ) := by
      have hu := Unitary.mul_star_self_of_mem (ρ g).property
      simp only [y, Function.update_self, mul_assoc, hu, mul_one,
        Function.update_idem, Function.update_eq_self]
      simp [ne_of_gt (Fin.castSucc_lt_succ (i := j))]
    rw [hz] at h
    have hfirst : (0 : Fin (n + 2)) ≠ j.castSucc.succ := by
      intro hh
      have hv := congrArg Fin.val hh
      simp at hv
    have hlast : Fin.last (n + 1) ≠ j.castSucc.succ := by
      exact Ne.symm (ne_of_lt (Fin.castSucc_lt_last j.succ))
    simpa only [Function.update_of_ne hfirst, Function.update_of_ne hlast,
      map_one, OneMemClass.coe_one, star_one, one_mul, mul_one] using h.symm

lemma finiteGroupCochainAverage_span {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) {a : M}
    (ha : a ∈ Submodule.span ℂ (Set.range (fun g => (ρ g : M)))) :
    MultimodularAt (finiteGroupCochainAverage ρ f) a := by
  apply multimodularAt_of_span _ _ _ ha
  rintro _ ⟨g, rfl⟩
  exact finiteGroupCochainAverage_multimodularAt ρ f g
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison HochschildCorners HochschildMatrixSystems

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  {n : ℕ} (c : Fin n → PartialIso M) (hi : ∀ i, (c i).initial = 1)
  (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)

def finiteColumnProjection : M := ∑ i, (c i).final

omit [PartialOrder M] [StarOrderedRing M] in
include ho in
lemma finiteColumnProjection_isProjection : IsStarProjection (finiteColumnProjection c) :=
  orthogonal_projection_finset_sum (fun i => (c i).final) (fun i => (c i).final_proj)
    ho Finset.univ

omit [PartialOrder M] [StarOrderedRing M] in
include hi ho in
lemma finiteColumnProjection_mul_column (j : Fin n) :
    finiteColumnProjection c * (c j : M) = (c j : M) := by
  classical
  simp only [finiteColumnProjection, PartialIso.final, Finset.sum_mul, mul_assoc]
  simp [column_star_mul c hi ho]

omit [PartialOrder M] [StarOrderedRing M] in
include hi ho in
lemma column_star_mul_finiteColumnProjection (j : Fin n) :
    star (c j : M) * finiteColumnProjection c = star (c j : M) := by
  have h := congrArg star (finiteColumnProjection_mul_column c hi ho j)
  simpa only [star_mul, finiteColumnProjection, star_sum, PartialIso.final, star_star] using h

def finiteColumnMatrixSystem :
    MatrixSystem (Corner (finiteColumnProjection c) (finiteColumnProjection_isProjection c ho)) n where
  entry i j := ⟨(c i : M) * star (c j : M), by
    constructor
    · rw [← mul_assoc, finiteColumnProjection_mul_column c hi ho]
    · rw [mul_assoc, column_star_mul_finiteColumnProjection c hi ho]⟩
  star_entry i j := Subtype.ext (by
    change star ((c i : M) * star (c j : M)) = (c j : M) * star (c i : M)
    simp only [star_mul, star_star])
  entry_mul i j k l := by
    apply Subtype.ext
    change ((c i : M) * star (c j : M)) * ((c k : M) * star (c l : M)) = _
    calc
      _ = (c i : M) * (star (c j : M) * (c k : M)) * star (c l : M) := by
        simp only [mul_assoc]
      _ = _ := by rw [column_star_mul c hi ho]; split_ifs <;> simp
  sum_diagonal := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma finiteColumnMatrixSystem_entry (i j : Fin n) :
    ((finiteColumnMatrixSystem c hi ho).entry i j : M) = (c i : M) * star (c j : M) := rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildCorners

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma corner_complement_left {p : M} (hp : IsStarProjection p) (a : Corner p hp) :
    (1 - p) * (a : M) = 0 := by
  rw [sub_mul, one_mul, a.property.1, sub_self]

omit [PartialOrder M] [StarOrderedRing M] in
lemma corner_complement_right {p : M} (hp : IsStarProjection p) (a : Corner p hp) :
    (a : M) * (1 - p) = 0 := by
  rw [mul_sub, mul_one, a.property.2, sub_self]

omit [PartialOrder M] [StarOrderedRing M] in
lemma cornerUnitaryExtension_mem {p : M} (hp : IsStarProjection p) (u : unitary (Corner p hp)) :
    (((u : Corner p hp) : M) + (1 - p)) ∈ unitary M := by
  let a : M := ((u : Corner p hp) : M)
  have hstar : star a * a = p := congrArg Subtype.val (Unitary.coe_star_mul_self u)
  have hmul : a * star a = p := congrArg Subtype.val (Unitary.coe_mul_star_self u)
  have hleft : (1 - p) * a = 0 := corner_complement_left hp (u : Corner p hp)
  have hright : a * (1 - p) = 0 := corner_complement_right hp (u : Corner p hp)
  have hstarleft : (1 - p) * star a = 0 := corner_complement_left hp (star (u : Corner p hp))
  have hstarright : star a * (1 - p) = 0 := corner_complement_right hp (star (u : Corner p hp))
  constructor
  · change star (a + (1 - p)) * (a + (1 - p)) = 1
    rw [star_add, hp.one_sub.isSelfAdjoint.star_eq, add_mul, mul_add, mul_add,
      hstar, hstarright, hleft, hp.one_sub.isIdempotentElem.eq]
    abel
  · change (a + (1 - p)) * star (a + (1 - p)) = 1
    rw [star_add, hp.one_sub.isSelfAdjoint.star_eq, add_mul, mul_add, mul_add,
      hmul, hright, hstarleft, hp.one_sub.isIdempotentElem.eq]
    abel

def cornerUnitaryExtension {p : M} (hp : IsStarProjection p) :
    unitary (Corner p hp) →* unitary M where
  toFun u := ⟨_, cornerUnitaryExtension_mem hp u⟩
  map_one' := Subtype.ext (by change p + (1 - p) = 1; abel)
  map_mul' u v := by
    apply Subtype.ext
    change (((u : Corner p hp) : M) * ((v : Corner p hp) : M)) + (1 - p) =
      (((u : Corner p hp) : M) + (1 - p)) * (((v : Corner p hp) : M) + (1 - p))
    rw [add_mul, mul_add, mul_add, corner_complement_right hp, corner_complement_left hp,
      hp.one_sub.isIdempotentElem.eq]
    abel

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma cornerUnitaryExtension_apply {p : M} (hp : IsStarProjection p)
    (u : unitary (Corner p hp)) :
    (cornerUnitaryExtension hp u : M) = ((u : Corner p hp) : M) + (1 - p) := rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildCorners HochschildMatrixSystems

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  {p : M} (hp : IsStarProjection p) {n : ℕ} (E : MatrixSystem (Corner p hp) n)

def finiteCornerGroupHom : E.signedPermutationGroup →* unitary M :=
  (cornerUnitaryExtension hp).comp E.signedPermutationGroup.subtype

omit [PartialOrder M] [StarOrderedRing M] in
lemma corner_matrixUnit_mem_group_span (i j : Fin n) :
    (E.entry i j : M) ∈ Submodule.span ℂ
      (Set.range (fun g : E.signedPermutationGroup => (finiteCornerGroupHom hp E g : M))) := by
  classical
  let P := Submodule.span ℂ
    (Set.range (fun g : E.signedPermutationGroup => (finiteCornerGroupHom hp E g : M)))
  let σ := Equiv.swap j i
  let g₀ : E.signedPermutationGroup :=
    ⟨E.signedPermutationUnitary σ (fun _ => false), ⟨(σ, fun _ => false), rfl⟩⟩
  let g₁ : E.signedPermutationGroup :=
    ⟨E.signedPermutationUnitary σ (fun k => decide (k = j)),
      ⟨(σ, fun k => decide (k = j)), rfl⟩⟩
  have hm (g : E.signedPermutationGroup) : (finiteCornerGroupHom hp E g : M) ∈ P :=
    Submodule.subset_span ⟨g, rfl⟩
  have hdiff : (finiteCornerGroupHom hp E g₀ : M) - (finiteCornerGroupHom hp E g₁ : M) =
      (2 : ℂ) • (E.entry i j : M) := by
    change ((E.signedPermutation σ (fun _ => false) : M) + (1 - p)) -
      ((E.signedPermutation σ (fun k => decide (k = j)) : M) + (1 - p)) = _
    calc
      _ = ((E.signedPermutation σ (fun _ => false) -
          E.signedPermutation σ (fun k => decide (k = j)) : Corner p hp) : M) := by
        change (_ + (1 - p)) - (_ + (1 - p)) = _ - _
        abel
      _ = _ := by rw [E.signedPermutation_flip]; simp [σ]
  have hh := P.smul_mem (2⁻¹ : ℂ) (P.sub_mem (hm g₀) (hm g₁))
  rw [hdiff, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul] at hh
  exact hh

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteCornerGroupHom_mem (R : StarSubalgebra ℂ M)
    (hE : ∀ i j, (E.entry i j : M) ∈ R) (g : E.signedPermutationGroup) :
    (finiteCornerGroupHom hp E g : M) ∈ R := by
  classical
  have hpR : p ∈ R := by
    have he := congrArg (fun a : Corner p hp => (a : M)) E.sum_diagonal
    have hm := R.sum_mem (fun i (_ : i ∈ Finset.univ) => hE i i)
    rw [AddSubmonoidClass.coe_finsetSum, corner_coe_one] at he
    rwa [← he]
  rcases g with ⟨u, ⟨⟨σ, s⟩, rfl⟩⟩
  change (E.signedPermutation σ s : M) + (1 - p) ∈ R
  apply R.add_mem _ (R.sub_mem R.one_mem hpR)
  change ((∑ i, MatrixSystem.signScalar (s i) • E.entry (σ i) i : Corner p hp) : M) ∈ R
  simpa using R.sum_mem (fun i (_ : i ∈ Finset.univ) => R.smul_mem (hE (σ i) i) _)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma cochainUnitaryTransport_leftCoboundary {n : ℕ}
    (u : Fin (n + 2) → unitary M) (f : Cochain M n) :
    cochainUnitaryTransport u (leftCoboundary f) =
      leftCoboundary (cochainUnitaryTransport (Fin.tail u) f) := by
  ext x
  have ht : (fun i : Fin n => cochainUnitaryTuple u x i.succ) =
      cochainUnitaryTuple (Fin.tail u) (Fin.tail x) := by
    ext i
    simp only [cochainUnitaryTuple, Fin.tail, Fin.castSucc_succ]
  simp only [cochainUnitaryTransport_apply, leftCoboundary_apply]
  rw [ht]
  change star (u 0 : M) *
      (((u 0 : M) * x 0 * star (u (0 : Fin (n + 1)).succ : M)) *
        f (cochainUnitaryTuple (Fin.tail u) (Fin.tail x))) * (u (Fin.last (n + 1)) : M) =
    x 0 * (star (u (0 : Fin (n + 1)).succ : M) *
      f (cochainUnitaryTuple (Fin.tail u) (Fin.tail x)) * (u (Fin.last (n + 1)) : M))
  calc
    _ = (star (u 0 : M) * (u 0 : M)) * (x 0 *
        (star (u (0 : Fin (n + 1)).succ : M) *
          f (cochainUnitaryTuple (Fin.tail u) (Fin.tail x)) * (u (Fin.last (n + 1)) : M))) := by
      simp only [mul_assoc]
    _ = _ := by rw [Unitary.star_mul_self_of_mem (u 0).property, one_mul]

lemma cochainUnitaryTransport_rightCoboundary {n : ℕ}
    (u : Fin (n + 2) → unitary M) (f : Cochain M n) :
    cochainUnitaryTransport u (rightCoboundary f) =
      rightCoboundary (cochainUnitaryTransport (fun i => u i.castSucc) f) := by
  ext x
  have ht : (fun i : Fin n => cochainUnitaryTuple u x i.castSucc) =
      cochainUnitaryTuple (fun i => u i.castSucc) (fun i => x i.castSucc) := by
    ext i
    simp only [cochainUnitaryTuple, Fin.castSucc_succ]
  simp only [cochainUnitaryTransport_apply, rightCoboundary_apply]
  rw [ht]
  change star (u 0 : M) *
      (f (cochainUnitaryTuple (fun i => u i.castSucc) (fun i => x i.castSucc)) *
        ((u (Fin.last n).castSucc : M) * x (Fin.last n) * star (u (Fin.last (n + 1)) : M))) *
          (u (Fin.last (n + 1)) : M) =
    (star (u 0 : M) * f (cochainUnitaryTuple (fun i => u i.castSucc) (fun i => x i.castSucc)) *
      (u (Fin.last n).castSucc : M)) * x (Fin.last n)
  simp only [mul_assoc, Unitary.star_mul_self_of_mem (u (Fin.last (n + 1))).property, mul_one]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma cochainUnitaryTuple_merge {n : ℕ} (u : Fin (n + 3) → unitary M)
    (x : Fin (n + 2) → M) (k : Fin (n + 1)) :
    mergeInputs (cochainUnitaryTuple u x) k =
      cochainUnitaryTuple (k.castSucc.succ.removeNth u) (mergeInputs x k) := by
  let p : Fin (n + 3) := k.castSucc.succ
  have hbefore (j : Fin (n + 2)) (hj : j.val < p.val) : p.removeNth u j = u j.castSucc := by
    rw [Fin.removeNth, Fin.succAbove_of_castSucc_lt _ _ hj]
  have hafter (j : Fin (n + 2)) (hj : p.val ≤ j.val) : p.removeNth u j = u j.succ := by
    rw [Fin.removeNth, Fin.succAbove_of_le_castSucc _ _ hj]
  change mergeInputs (cochainUnitaryTuple u x) k = cochainUnitaryTuple (p.removeNth u) (mergeInputs x k)
  ext i
  by_cases hik : i < k
  · have hi : i.val < k.val := hik
    simp only [mergeInputs, ite_eq_left hik, cochainUnitaryTuple]
    rw [hbefore i.castSucc (by dsimp [p]; omega),
      hbefore i.succ (by dsimp [p]; omega)]
    rfl
  · by_cases hie : i = k
    · subst i
      simp only [mergeInputs, lt_self_iff_false, ite_false, ite_true, cochainUnitaryTuple]
      rw [hbefore k.castSucc (by dsimp [p]; simp), hafter k.succ (by dsimp [p]; simp)]
      simp only [Fin.castSucc_succ, mul_assoc]
      rw [← mul_assoc (star (u k.castSucc.succ : M)) (u k.castSucc.succ : M),
        Unitary.star_mul_self_of_mem (u k.castSucc.succ).property, one_mul]
    · have hi : k.val < i.val := by
        have hne : i.val ≠ k.val := fun h => hie (Fin.ext h)
        omega
      simp only [mergeInputs, ite_eq_right hik, ite_eq_right hie, cochainUnitaryTuple]
      rw [hafter i.castSucc (by dsimp [p]; omega),
        hafter i.succ (by dsimp [p]; omega)]
      rfl

lemma cochainUnitaryTransport_middleCoboundary {n : ℕ}
    (u : Fin (n + 3) → unitary M) (f : Cochain M (n + 1)) (k : Fin (n + 1)) :
    cochainUnitaryTransport u (middleCoboundary f k) =
      middleCoboundary (cochainUnitaryTransport (k.castSucc.succ.removeNth u) f) k := by
  ext x
  simp only [cochainUnitaryTransport_apply, middleCoboundary_apply, cochainUnitaryTuple_merge]
  have hzero : k.castSucc.succ ≠ (0 : Fin (n + 3)) := Fin.succ_ne_zero _
  have hlast : k.castSucc.succ ≠ Fin.last (n + 2) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hv
    omega
  simp only [Fin.removeNth, Fin.succAbove_ne_zero_zero hzero,
    Fin.succAbove_ne_last_last hlast]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {G V : Type*} [Fintype G] [Nonempty G] [AddCommGroup V] [Module ℂ V]

omit [Nonempty G] in
lemma sum_removeNth {n : ℕ} (k : Fin (n + 1)) (F : (Fin n → G) → V) :
    (∑ u : Fin (n + 1) → G, F (k.removeNth u)) =
      (Fintype.card G : ℂ) • ∑ v : Fin n → G, F v := by
  calc
    _ = ∑ p : G × (Fin n → G), F p.2 := by
      apply Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => G) k).symm _ _
      intro u
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

lemma normalized_sum_removeNth {n : ℕ} (k : Fin (n + 1)) (F : (Fin n → G) → V) :
    (Fintype.card (Fin (n + 1) → G) : ℂ)⁻¹ • (∑ u : Fin (n + 1) → G, F (k.removeNth u)) =
      (Fintype.card (Fin n → G) : ℂ)⁻¹ • ∑ v : Fin n → G, F v := by
  rw [sum_removeNth, smul_smul]
  congr 1
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, pow_succ, Nat.cast_mul]
  field_simp
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u v
variable {M : Type u} [CStarAlgebra M] {G : Type v} [Group G] [Fintype G]

lemma finiteGroupCochainAverage_add {n : ℕ} (ρ : G →* unitary M) (f g : Cochain M n) :
    finiteGroupCochainAverage ρ (f + g) = finiteGroupCochainAverage ρ f + finiteGroupCochainAverage ρ g := by
  simp only [finiteGroupCochainAverage, cochainUnitaryTransport_add, Finset.sum_add_distrib, smul_add]

lemma finiteGroupCochainAverage_smul {n : ℕ} (ρ : G →* unitary M) (z : ℂ) (f : Cochain M n) :
    finiteGroupCochainAverage ρ (z • f) = z • finiteGroupCochainAverage ρ f := by
  simp only [finiteGroupCochainAverage, cochainUnitaryTransport_smul, ← Finset.smul_sum]
  exact smul_comm _ _ _

def finiteGroupCochainAverageLinear {n : ℕ} (ρ : G →* unitary M) : Cochain M n →ₗ[ℂ] Cochain M n where
  toFun := finiteGroupCochainAverage ρ
  map_add' := finiteGroupCochainAverage_add ρ
  map_smul' := finiteGroupCochainAverage_smul ρ

lemma finiteGroupCochainAverage_sum {I : Type*} {n : ℕ} (ρ : G →* unitary M)
    (s : Finset I) (f : I → Cochain M n) :
    finiteGroupCochainAverage ρ (∑ i ∈ s, f i) = ∑ i ∈ s, finiteGroupCochainAverage ρ (f i) :=
  map_sum (finiteGroupCochainAverageLinear ρ) f s

def leftFaceLinear (n : ℕ) : Cochain M n →ₗ[ℂ] Cochain M (n + 1) where
  toFun := leftCoboundary
  map_add' f g := by ext x; simp only [leftCoboundary_apply, add_apply, mul_add]
  map_smul' z f := by ext x; simp only [leftCoboundary_apply, smul_apply, mul_smul_comm, RingHom.id_apply]

def rightFaceLinear (n : ℕ) : Cochain M n →ₗ[ℂ] Cochain M (n + 1) where
  toFun := rightCoboundary
  map_add' f g := by ext x; simp only [rightCoboundary_apply, add_apply, add_mul]
  map_smul' z f := by ext x; simp only [rightCoboundary_apply, smul_apply, smul_mul_assoc, RingHom.id_apply]

def middleFaceLinear {n : ℕ} (k : Fin (n + 1)) :
    Cochain M (n + 1) →ₗ[ℂ] Cochain M (n + 2) where
  toFun f := middleCoboundary f k
  map_add' f g := by ext x; simp only [middleCoboundary_apply, add_apply]
  map_smul' z f := by ext x; simp only [middleCoboundary_apply, smul_apply, RingHom.id_apply]

lemma finiteGroupCochainAverage_face {n : ℕ} (ρ : G →* unitary M)
    (L : Cochain M n →ₗ[ℂ] Cochain M (n + 1)) (k : Fin (n + 2)) (f : Cochain M n)
    (hL : ∀ u : Fin (n + 2) → unitary M,
      cochainUnitaryTransport u (L f) = L (cochainUnitaryTransport (k.removeNth u) f)) :
    finiteGroupCochainAverage ρ (L f) = L (finiteGroupCochainAverage ρ f) := by
  have ht (u : Fin (n + 2) → G) :
      cochainUnitaryTransport (fun i => ρ (u i)) (L f) =
        L (cochainUnitaryTransport (fun i => ρ (k.removeNth u i)) f) := hL (fun i => ρ (u i))
  unfold finiteGroupCochainAverage
  simp_rw [ht]
  rw [← map_sum, ← map_smul]
  congr 1
  exact normalized_sum_removeNth k (fun u => cochainUnitaryTransport (fun i => ρ (u i)) f)

lemma finiteGroupCochainAverage_leftCoboundary {n : ℕ} (ρ : G →* unitary M) (f : Cochain M n) :
    finiteGroupCochainAverage ρ (leftCoboundary f) = leftCoboundary (finiteGroupCochainAverage ρ f) := by
  apply finiteGroupCochainAverage_face ρ (leftFaceLinear n) 0 f
  intro u
  simpa only [leftFaceLinear, LinearMap.coe_mk, AddHom.coe_mk, Fin.removeNth_zero] using
    cochainUnitaryTransport_leftCoboundary u f

lemma finiteGroupCochainAverage_rightCoboundary {n : ℕ} (ρ : G →* unitary M) (f : Cochain M n) :
    finiteGroupCochainAverage ρ (rightCoboundary f) = rightCoboundary (finiteGroupCochainAverage ρ f) := by
  apply finiteGroupCochainAverage_face ρ (rightFaceLinear n) (Fin.last (n + 1)) f
  intro u
  change cochainUnitaryTransport u (rightCoboundary f) =
    rightCoboundary (cochainUnitaryTransport ((Fin.last (n + 1)).removeNth u) f)
  rw [Fin.removeNth_last, show Fin.init u = (fun i => u i.castSucc) from rfl]
  exact cochainUnitaryTransport_rightCoboundary u f

lemma finiteGroupCochainAverage_middleCoboundary {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) (k : Fin (n + 1)) :
    finiteGroupCochainAverage ρ (middleCoboundary f k) = middleCoboundary (finiteGroupCochainAverage ρ f) k := by
  apply finiteGroupCochainAverage_face ρ (middleFaceLinear k) k.castSucc.succ f
  intro u
  exact cochainUnitaryTransport_middleCoboundary u f k

lemma finiteGroupCochainAverage_differential {n : ℕ} (ρ : G →* unitary M) (f : Cochain M (n + 1)) :
    finiteGroupCochainAverage ρ (differential f) = differential (finiteGroupCochainAverage ρ f) := by
  change finiteGroupCochainAverage ρ
    (leftCoboundary f + ∑ j : Fin (n + 1), ((-1 : ℂ) ^ (j.val + 1)) • middleCoboundary f j +
      ((-1 : ℂ) ^ (n + 2)) • rightCoboundary f) = _
  simp only [finiteGroupCochainAverage_add, finiteGroupCochainAverage_sum,
    finiteGroupCochainAverage_smul, finiteGroupCochainAverage_leftCoboundary,
    finiteGroupCochainAverage_rightCoboundary, finiteGroupCochainAverage_middleCoboundary]
  rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M : Type u} [CStarAlgebra M]

structure MatrixSectionGroup (c : ℕ → PartialIso M) (k : ℕ) where
  carrier : Type u
  [group : Group carrier]
  [finite : Fintype carrier]
  representation : carrier →* unitary M
  mem : ∀ g, (representation g : M) ∈ countableMatrixAlgebra c
  spans : ∀ i j : Fin k, countableMatrixUnit c i.val j.val ∈
    Submodule.span ℂ (Set.range (fun g => (representation g : M)))

attribute [instance] MatrixSectionGroup.group MatrixSectionGroup.finite

lemma matrixSectionGroup_nonempty (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) (k : ℕ) :
    Nonempty (MatrixSectionGroup c k) := by
  let d : Fin k → PartialIso M := fun i => c i.val
  have hd : ∀ i, (d i).initial = 1 := fun i => hi i.val
  have hdo : ∀ i j, i ≠ j → (d i).final * (d j).final = 0 := by
    intro i j hij
    exact ho i.val j.val (fun h => hij (Fin.ext h))
  let hp := finiteColumnProjection_isProjection d hdo
  let E := finiteColumnMatrixSystem d hd hdo
  let : Fintype E.signedPermutationGroup := Fintype.ofFinite _
  refine ⟨{ carrier := E.signedPermutationGroup
            representation := finiteCornerGroupHom hp E
            mem := ?_
            spans := ?_ }⟩
  · apply finiteCornerGroupHom_mem
    intro i j
    change (c i.val : M) * star (c j.val : M) ∈ countableMatrixAlgebra c
    exact StarAlgebra.subset_adjoin ℂ _ ⟨(i.val, j.val), rfl⟩
  · intro i j
    exact corner_matrixUnit_mem_group_span hp E i j

def matrixSectionGroup (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) (k : ℕ) : MatrixSectionGroup c k :=
  Classical.choice (matrixSectionGroup_nonempty c hi ho k)

def matrixSectionAverage (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    {n : ℕ} (f : Cochain M n) (k : ℕ) : Cochain M n :=
  finiteGroupCochainAverage (matrixSectionGroup c hi ho k).representation f

lemma matrixSectionAverage_norm (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    {n : ℕ} (f : Cochain M n) (k : ℕ) : ‖matrixSectionAverage c hi ho f k‖ ≤ ‖f‖ :=
  finiteGroupCochainAverage_norm _ f

lemma matrixSectionAverage_module (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    {n : ℕ} (f : Cochain M (n + 1)) (k : ℕ) (i j : Fin k) :
    MultimodularAt (matrixSectionAverage c hi ho f k) (countableMatrixUnit c i.val j.val) :=
  finiteGroupCochainAverage_span _ f ((matrixSectionGroup c hi ho k).spans i j)

lemma matrixSectionAverage_add (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    {n : ℕ} (f g : Cochain M n) (k : ℕ) :
    matrixSectionAverage c hi ho (f + g) k = matrixSectionAverage c hi ho f k + matrixSectionAverage c hi ho g k :=
  finiteGroupCochainAverage_add _ f g

lemma matrixSectionAverage_smul (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    {n : ℕ} (z : ℂ) (f : Cochain M n) (k : ℕ) :
    matrixSectionAverage c hi ho (z • f) k = z • matrixSectionAverage c hi ho f k :=
  finiteGroupCochainAverage_smul _ z f

lemma matrixSectionAverage_differential (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    {n : ℕ} (f : Cochain M (n + 1)) (k : ℕ) :
    matrixSectionAverage c hi ho (differential f) k = differential (matrixSectionAverage c hi ho f k) :=
  finiteGroupCochainAverage_differential _ f
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology

namespace BoundedHochschild.KadisonRingrose

universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
lemma predualTendsto_congr_eventually (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {I : Type v} {l : Filter I} {a b : I → M} {c : M}
    (hab : a =ᶠ[l] b) (ha : PredualTendsto e a l c) : PredualTendsto e b l c := by
  intro z
  exact (ha z).congr' (hab.mono (fun i hi => congrArg (fun d : M => e.symm d z) hi))

lemma multimodularAt_of_predualTendsto (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {I : Type v} {l : Filter I} [l.NeBot] {n : ℕ}
    (F : I → Cochain M (n + 1)) (f : Cochain M (n + 1)) (r : M)
    (ht : ∀ x, PredualTendsto e (fun i => F i x) l (f x))
    (hF : ∀ᶠ i in l, MultimodularAt (F i) r) : MultimodularAt f r := by
  have hL := (HochschildSakai.abstract_multiplication_normal e).1
  have hR := (HochschildSakai.abstract_multiplication_normal e).2
  constructor
  · intro x
    apply predual_tendsto_unique e (ht (Function.update x 0 (r * x 0)))
    exact predualTendsto_congr_eventually e
      (hF.mono (fun i hi => (hi.left x).symm)) ((hL r).tendsto e (ht x))
  · intro x
    apply predual_tendsto_unique e (ht (Function.update x (Fin.last n) (x (Fin.last n) * r)))
    exact predualTendsto_congr_eventually e
      (hF.mono (fun i hi => (hi.right x).symm)) ((hR r).tendsto e (ht x))
  · intro x j
    apply predual_tendsto_unique e (ht (Function.update x j.castSucc (x j.castSucc * r)))
    exact predualTendsto_congr_eventually e
      (hF.mono (fun i hi => (hi.balance x j).symm))
      (ht (Function.update x j.succ (r * x j.succ)))
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

def matrixAverageUltrafilter : Ultrafilter ℕ := Ultrafilter.of atTop

private lemma matrix_average_limit_exists (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M n) :
    ∃ A : Cochain M n, ‖A‖ ≤ ‖f‖ ∧ ∀ x,
      PredualTendsto e (fun k => matrixSectionAverage c hi ho f k x) matrixAverageUltrafilter (A x) :=
  bounded_cochain_ultralimit e matrixAverageUltrafilter (matrixSectionAverage c hi ho f)
    ‖f‖ (norm_nonneg _) (matrixSectionAverage_norm c hi ho f)

def countableMatrixAverage (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M n) : Cochain M n :=
  Classical.choose (matrix_average_limit_exists e c hi ho f)

lemma countableMatrixAverage_norm (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M n) :
    ‖countableMatrixAverage e c hi ho f‖ ≤ ‖f‖ :=
  (Classical.choose_spec (matrix_average_limit_exists e c hi ho f)).1

lemma countableMatrixAverage_tendsto (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M n) (x : Fin n → M) :
    PredualTendsto e (fun k => matrixSectionAverage c hi ho f k x)
      matrixAverageUltrafilter (countableMatrixAverage e c hi ho f x) :=
  (Classical.choose_spec (matrix_average_limit_exists e c hi ho f)).2 x

lemma countableMatrixAverage_add (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f g : Cochain M n) :
    countableMatrixAverage e c hi ho (f + g) = countableMatrixAverage e c hi ho f + countableMatrixAverage e c hi ho g := by
  ext x
  apply predual_tendsto_unique e (countableMatrixAverage_tendsto e c hi ho (f + g) x)
  simpa only [matrixSectionAverage_add, add_apply] using predual_tendsto_add e
    (countableMatrixAverage_tendsto e c hi ho f x) (countableMatrixAverage_tendsto e c hi ho g x)

lemma countableMatrixAverage_smul (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (z : ℂ) (f : Cochain M n) :
    countableMatrixAverage e c hi ho (z • f) = z • countableMatrixAverage e c hi ho f := by
  ext x
  apply predual_tendsto_unique e (countableMatrixAverage_tendsto e c hi ho (z • f) x)
  simpa only [matrixSectionAverage_smul, smul_apply] using predual_tendsto_smul e
    (countableMatrixAverage_tendsto e c hi ho f x) z

def countableMatrixAverageCLM (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) (n : ℕ) :
    Cochain M n →L[ℂ] Cochain M n :=
  LinearMap.mkContinuous
    { toFun := countableMatrixAverage e c hi ho
      map_add' := countableMatrixAverage_add e c hi ho
      map_smul' := countableMatrixAverage_smul e c hi ho }
    1 (fun f => by
      change ‖countableMatrixAverage e c hi ho f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using countableMatrixAverage_norm e c hi ho f)

variable [CompleteSpace X]

lemma countableMatrixAverage_multimodular (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M (n + 1)) :
    MultimodularOver (countableMatrixAlgebra c) (countableMatrixAverage e c hi ho f) := by
  apply multimodular_of_matrixUnits c hi ho
  intro i j
  apply multimodularAt_of_predualTendsto e (matrixSectionAverage c hi ho f)
    (countableMatrixAverage e c hi ho f) _ (countableMatrixAverage_tendsto e c hi ho f)
  apply Ultrafilter.of_le atTop
  filter_upwards [eventually_gt_atTop (max i j)] with k hk
  exact matrixSectionAverage_module c hi ho f k
    ⟨i, lt_of_le_of_lt (le_max_left i j) hk⟩ ⟨j, lt_of_le_of_lt (le_max_right i j) hk⟩

lemma countableMatrixAverage_differential (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M (n + 1)) :
    countableMatrixAverage e c hi ho (differential f) = differential (countableMatrixAverage e c hi ho f) := by
  ext x
  apply predual_tendsto_unique e (countableMatrixAverage_tendsto e c hi ho (differential f) x)
  simpa only [matrixSectionAverage_differential, differential_apply] using
    predual_tendsto_differential_of_predual e (countableMatrixAverage_tendsto e c hi ho f) x

lemma countableMatrixAverage_cocycle (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M (n + 1))
    (hf : ∀ x, differentialValue f x = 0) :
    ∀ x, differentialValue (countableMatrixAverage e c hi ho f) x = 0 := by
  have hd : differential f = 0 := by
    ext x
    simpa only [differential_apply, zero_apply] using hf x
  have he := countableMatrixAverage_differential e c hi ho f
  rw [hd, show countableMatrixAverage e c hi ho (0 : Cochain M (n + 2)) = 0 from
    map_zero (countableMatrixAverageCLM e c hi ho (n + 2))] at he
  intro x
  simpa only [differential_apply, zero_apply] using
    congrArg (fun F : Cochain M (n + 2) => F x) he.symm

variable [PartialOrder M] [StarOrderedRing M]

theorem primitive_of_countableMatrixAverage [Nontrivial M]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) atTop 1)
    {n : ℕ} (f : Cochain M (n + 2)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ∀ x, differentialValue g x = countableMatrixAverage e c hi ho f x :=
  primitive_of_algebraic_matrix_multimodular e hno c hi ho ht _
    (countableMatrixAverage_multimodular e c hi ho f) (countableMatrixAverage_cocycle e c hi ho f hf)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma cochainUnitaryTransport_one {n : ℕ} (f : Cochain M n) :
    cochainUnitaryTransport (fun _ => 1) f = f := by
  ext x
  simp only [cochainUnitaryTransport_apply, OneMemClass.coe_one, star_one, one_mul, mul_one]
  congr 1
  funext i
  simp only [cochainUnitaryTuple, OneMemClass.coe_one, star_one, one_mul, mul_one]

def unitaryPrefix {n : ℕ} (u : Fin (n + 1) → unitary M) (k : ℕ) : Fin (n + 1) → unitary M :=
  fun i => if i.val < k then u i else 1
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma curryMid_one_norm_le {n : ℕ} (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    ‖f.curryMid i 1‖ ≤ ‖f‖ := by
  have h1 : ‖(1 : M)‖ ≤ 1 := by
    rcases subsingleton_or_nontrivial M with h | h
    · simp [Subsingleton.elim (1 : M) 0]
    · simp
  calc
    _ ≤ ‖f.curryMid i‖ * ‖(1 : M)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖f‖ * 1 := by rw [ContinuousMultilinearMap.norm_curryMid]; gcongr
    _ = _ := mul_one _

def barInsertion {n : ℕ} (u : Fin (n + 2) → unitary M) (i : Fin (n + 1))
    (f : Cochain M (n + 1)) : Cochain M n :=
  (cochainUnitaryTransport (unitaryPrefix u (i.val + 1)) f).curryMid i 1

@[simp] lemma barInsertion_apply {n : ℕ} (u : Fin (n + 2) → unitary M) (i : Fin (n + 1))
    (f : Cochain M (n + 1)) (x : Fin n → M) :
    barInsertion u i f x = cochainUnitaryTransport (unitaryPrefix u (i.val + 1)) f (i.insertNth 1 x) := rfl

lemma barInsertion_norm {n : ℕ} (u : Fin (n + 2) → unitary M) (i : Fin (n + 1))
    (f : Cochain M (n + 1)) : ‖barInsertion u i f‖ ≤ ‖f‖ :=
  (curryMid_one_norm_le _ i).trans (cochainUnitaryTransport_norm _ f)

lemma barInsertion_add {n : ℕ} (u : Fin (n + 2) → unitary M) (i : Fin (n + 1))
    (f g : Cochain M (n + 1)) : barInsertion u i (f + g) = barInsertion u i f + barInsertion u i g := by
  ext x
  simp only [barInsertion_apply, cochainUnitaryTransport_add, add_apply]

lemma barInsertion_smul {n : ℕ} (u : Fin (n + 2) → unitary M) (i : Fin (n + 1))
    (z : ℂ) (f : Cochain M (n + 1)) : barInsertion u i (z • f) = z • barInsertion u i f := by
  ext x
  simp only [barInsertion_apply, cochainUnitaryTransport_smul, smul_apply]

variable {G : Type*} [Group G] [Fintype G]

def finiteGroupBarInsertion {n : ℕ} (ρ : G →* unitary M) (i : Fin (n + 1))
    (f : Cochain M (n + 1)) : Cochain M n :=
  (Fintype.card (Fin (n + 2) → G) : ℂ)⁻¹ •
    ∑ g : Fin (n + 2) → G, barInsertion (fun j => ρ (g j)) i f

lemma finiteGroupBarInsertion_norm {n : ℕ} (ρ : G →* unitary M) (i : Fin (n + 1))
    (f : Cochain M (n + 1)) : ‖finiteGroupBarInsertion ρ i f‖ ≤ ‖f‖ := by
  let K := Fin (n + 2) → G
  have hc : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  rw [finiteGroupBarInsertion, norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card K : ℝ)⁻¹ * ((Fintype.card K : ℝ) * ‖f‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      exact (norm_sum_le _ _).trans (by
        simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
          Finset.sum_le_sum (s := Finset.univ) (fun (g : Fin (n + 2) → G) _ =>
            barInsertion_norm (fun j => ρ (g j)) i f))
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]

def finiteGroupBarOperator {n : ℕ} (ρ : G →* unitary M) (f : Cochain M (n + 1)) : Cochain M n :=
  ∑ i : Fin (n + 1), ((-1 : ℂ) ^ i.val) • finiteGroupBarInsertion ρ i f

lemma finiteGroupBarOperator_norm {n : ℕ} (ρ : G →* unitary M) (f : Cochain M (n + 1)) :
    ‖finiteGroupBarOperator ρ f‖ ≤ (n + 1 : ℝ) * ‖f‖ := by
  unfold finiteGroupBarOperator
  calc
    _ ≤ ∑ i : Fin (n + 1), ‖((-1 : ℂ) ^ i.val) • finiteGroupBarInsertion ρ i f‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (n + 1), ‖f‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using
        finiteGroupBarInsertion_norm ρ i f
    _ = _ := by simp [nsmul_eq_mul]

lemma finiteGroupBarInsertion_add {n : ℕ} (ρ : G →* unitary M) (i : Fin (n + 1))
    (f g : Cochain M (n + 1)) :
    finiteGroupBarInsertion ρ i (f + g) = finiteGroupBarInsertion ρ i f + finiteGroupBarInsertion ρ i g := by
  simp only [finiteGroupBarInsertion, barInsertion_add, Finset.sum_add_distrib, smul_add]

lemma finiteGroupBarInsertion_smul {n : ℕ} (ρ : G →* unitary M) (i : Fin (n + 1))
    (z : ℂ) (f : Cochain M (n + 1)) :
    finiteGroupBarInsertion ρ i (z • f) = z • finiteGroupBarInsertion ρ i f := by
  simp only [finiteGroupBarInsertion, barInsertion_smul, ← Finset.smul_sum]
  exact smul_comm _ _ _

lemma finiteGroupBarOperator_add {n : ℕ} (ρ : G →* unitary M) (f g : Cochain M (n + 1)) :
    finiteGroupBarOperator ρ (f + g) = finiteGroupBarOperator ρ f + finiteGroupBarOperator ρ g := by
  simp only [finiteGroupBarOperator, finiteGroupBarInsertion_add, smul_add, Finset.sum_add_distrib]

lemma finiteGroupBarOperator_smul {n : ℕ} (ρ : G →* unitary M) (z : ℂ) (f : Cochain M (n + 1)) :
    finiteGroupBarOperator ρ (z • f) = z • finiteGroupBarOperator ρ f := by
  simp only [finiteGroupBarOperator, finiteGroupBarInsertion_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm _ _ _

def finiteGroupBarOperatorCLM (ρ : G →* unitary M) (n : ℕ) :
    Cochain M (n + 1) →L[ℂ] Cochain M n :=
  LinearMap.mkContinuous
    { toFun := finiteGroupBarOperator ρ
      map_add' := finiteGroupBarOperator_add ρ
      map_smul' := finiteGroupBarOperator_smul ρ }
    (n + 1) (fun f => by
      change ‖finiteGroupBarOperator ρ f‖ ≤ (n + 1 : ℝ) * ‖f‖
      exact finiteGroupBarOperator_norm ρ f)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

def matrixSectionBarOperator (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f : Cochain M (n + 1)) (k : ℕ) : Cochain M n :=
  finiteGroupBarOperator (matrixSectionGroup c hi ho k).representation f

lemma matrixSectionBarOperator_norm (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f : Cochain M (n + 1)) (k : ℕ) : ‖matrixSectionBarOperator c hi ho f k‖ ≤ (n + 1 : ℝ) * ‖f‖ :=
  finiteGroupBarOperator_norm _ f

lemma matrixSectionBarOperator_add (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f g : Cochain M (n + 1)) (k : ℕ) :
    matrixSectionBarOperator c hi ho (f + g) k = matrixSectionBarOperator c hi ho f k + matrixSectionBarOperator c hi ho g k :=
  finiteGroupBarOperator_add _ f g

lemma matrixSectionBarOperator_smul (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (z : ℂ) (f : Cochain M (n + 1)) (k : ℕ) :
    matrixSectionBarOperator c hi ho (z • f) k = z • matrixSectionBarOperator c hi ho f k :=
  finiteGroupBarOperator_smul _ z f

private lemma matrix_bar_limit_exists (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M (n + 1)) :
    ∃ H : Cochain M n, ‖H‖ ≤ (n + 1 : ℝ) * ‖f‖ ∧ ∀ x,
      PredualTendsto e (fun k => matrixSectionBarOperator c hi ho f k x)
        matrixAverageUltrafilter (H x) :=
  bounded_cochain_ultralimit e matrixAverageUltrafilter (matrixSectionBarOperator c hi ho f)
    ((n + 1 : ℝ) * ‖f‖) (by positivity) (matrixSectionBarOperator_norm c hi ho f)

def countableMatrixBarOperator (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M (n + 1)) : Cochain M n :=
  Classical.choose (matrix_bar_limit_exists e c hi ho f)

lemma countableMatrixBarOperator_norm (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M (n + 1)) :
    ‖countableMatrixBarOperator e c hi ho f‖ ≤ (n + 1 : ℝ) * ‖f‖ :=
  (Classical.choose_spec (matrix_bar_limit_exists e c hi ho f)).1

lemma countableMatrixBarOperator_tendsto (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M (n + 1)) (x : Fin n → M) :
    PredualTendsto e (fun k => matrixSectionBarOperator c hi ho f k x)
      matrixAverageUltrafilter (countableMatrixBarOperator e c hi ho f x) :=
  (Classical.choose_spec (matrix_bar_limit_exists e c hi ho f)).2 x

lemma countableMatrixBarOperator_add (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f g : Cochain M (n + 1)) :
    countableMatrixBarOperator e c hi ho (f + g) = countableMatrixBarOperator e c hi ho f + countableMatrixBarOperator e c hi ho g := by
  ext x
  apply predual_tendsto_unique e (countableMatrixBarOperator_tendsto e c hi ho (f + g) x)
  simpa only [matrixSectionBarOperator_add, add_apply] using predual_tendsto_add e
    (countableMatrixBarOperator_tendsto e c hi ho f x) (countableMatrixBarOperator_tendsto e c hi ho g x)

lemma countableMatrixBarOperator_smul (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (z : ℂ) (f : Cochain M (n + 1)) :
    countableMatrixBarOperator e c hi ho (z • f) = z • countableMatrixBarOperator e c hi ho f := by
  ext x
  apply predual_tendsto_unique e (countableMatrixBarOperator_tendsto e c hi ho (z • f) x)
  simpa only [matrixSectionBarOperator_smul, smul_apply] using predual_tendsto_smul e
    (countableMatrixBarOperator_tendsto e c hi ho f x) z

def countableMatrixBarOperatorCLM (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) (n : ℕ) :
    Cochain M (n + 1) →L[ℂ] Cochain M n :=
  LinearMap.mkContinuous
    { toFun := countableMatrixBarOperator e c hi ho
      map_add' := countableMatrixBarOperator_add e c hi ho
      map_smul' := countableMatrixBarOperator_smul e c hi ho }
    (n + 1) (fun f => by
      change ‖countableMatrixBarOperator e c hi ho f‖ ≤ (n + 1 : ℝ) * ‖f‖
      exact countableMatrixBarOperator_norm e c hi ho f)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def matrixSectionBarDefect (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f : Cochain M (n + 1)) (k : ℕ) : Cochain M (n + 1) :=
  differential (matrixSectionBarOperator c hi ho f k) +
    matrixSectionBarOperator c hi ho (differential f) k -
      (f - matrixSectionAverage c hi ho f k)

def countableMatrixBarDefect (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f : Cochain M (n + 1)) : Cochain M (n + 1) :=
  differential (countableMatrixBarOperator e c hi ho f) +
    countableMatrixBarOperator e c hi ho (differential f) -
      (f - countableMatrixAverage e c hi ho f)

lemma countableMatrixBarDefect_tendsto (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f : Cochain M (n + 1)) (x : Fin (n + 1) → M) :
    PredualTendsto e (fun k => matrixSectionBarDefect c hi ho f k x)
      matrixAverageUltrafilter (countableMatrixBarDefect e c hi ho f x) := by
  have hd := predual_tendsto_differential_of_predual e
    (countableMatrixBarOperator_tendsto e c hi ho f) x
  have hH := countableMatrixBarOperator_tendsto e c hi ho (differential f) x
  have hP := predual_tendsto_sub e
    (predual_tendsto_const e (f x) (matrixAverageUltrafilter : Filter ℕ))
    (countableMatrixAverage_tendsto e c hi ho f x)
  simpa only [matrixSectionBarDefect, countableMatrixBarDefect,
    add_apply, sub_apply, differential_apply] using
      predual_tendsto_sub e (predual_tendsto_add e hd hH) hP

lemma countableMatrixBarDefect_eq_zero_of_eventually
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f : Cochain M (n + 1))
    (h : ∀ᶠ k in (matrixAverageUltrafilter : Filter ℕ),
      matrixSectionBarDefect c hi ho f k = 0) :
    countableMatrixBarDefect e c hi ho f = 0 := by
  ext x
  apply predual_tendsto_unique e (countableMatrixBarDefect_tendsto e c hi ho f x)
  apply predualTendsto_congr_eventually e _ (predual_tendsto_const e 0 _)
  filter_upwards [h] with k hk
  simp only [hk, zero_apply]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma curryMid_leftCoboundary_zero {n : ℕ} (f : Cochain M n) :
    (leftCoboundary f).curryMid 0 1 = f := by
  ext x
  change (Fin.insertNth (α := fun _ => M) 0 1 x) 0 *
    f (fun j => (Fin.insertNth (α := fun _ => M) 0 1 x) j.succ) = f x
  simp only [Fin.insertNth_zero', Fin.cons_zero, Fin.cons_succ, one_mul]

lemma curryMid_leftCoboundary_succ {n : ℕ} (f : Cochain M (n + 1))
    (i : Fin (n + 1)) :
    (leftCoboundary f).curryMid i.succ 1 = leftCoboundary (f.curryMid i 1) := by
  ext x
  have h0 : i.succ.insertNth (α := fun _ => M) 1 x 0 = x 0 := by
    rw [tupleInsert_lt _ _ _ _ (by simp)]
    rfl
  have ht : (fun j : Fin (n + 1) => i.succ.insertNth (α := fun _ => M) 1 x j.succ) =
      i.insertNth 1 (Fin.tail x) := by
    apply (Fin.eq_insertNth_iff).mpr
    constructor
    · exact Fin.insertNth_apply_same (α := fun _ => M) i.succ 1 x
    · funext j
      change i.succ.insertNth (α := fun _ => M) 1 x (i.succAbove j).succ = x j.succ
      rw [← Fin.succ_succAbove_succ, Fin.insertNth_apply_succAbove]
  change i.succ.insertNth (α := fun _ => M) 1 x 0 *
    f (fun j => i.succ.insertNth (α := fun _ => M) 1 x j.succ) =
      x 0 * f (i.insertNth 1 (Fin.tail x))
  rw [h0, ht]

lemma curryMid_rightCoboundary_last {n : ℕ} (f : Cochain M n) :
    (rightCoboundary f).curryMid (Fin.last n) 1 = f := by
  ext x
  change f (fun j => (Fin.last n).insertNth (α := fun _ => M) 1 x j.castSucc) *
    ((Fin.last n).insertNth (α := fun _ => M) 1 x (Fin.last n)) = f x
  simp only [Fin.insertNth_last', Fin.snoc_castSucc, Fin.snoc_last, mul_one]

lemma curryMid_rightCoboundary_castSucc {n : ℕ} (f : Cochain M (n + 1))
    (i : Fin (n + 1)) :
    (rightCoboundary f).curryMid i.castSucc 1 = rightCoboundary (f.curryMid i 1) := by
  ext x
  change f (fun j => i.castSucc.insertNth (α := fun _ => M) 1 x j.castSucc) *
      (i.castSucc.insertNth (α := fun _ => M) 1 x (Fin.last (n + 1))) =
    f (i.insertNth 1 (fun j => x j.castSucc)) * x (Fin.last n)
  rw [init_insert, last_insert]

lemma curryMid_middleCoboundary_castSucc {n : ℕ} (f : Cochain M (n + 1))
    (i : Fin (n + 1)) :
    (middleCoboundary f i).curryMid i.castSucc 1 = f := by
  ext x
  change middleCoboundary f i (i.castSucc.insertNth (α := fun _ => M) 1 x) = f x
  rw [middleCoboundary_apply, merge_insert_same x i 1 (one_mul _)]

lemma merge_insert_succ_one {n : ℕ} (x : Fin (n + 1) → M) (i : Fin (n + 1)) :
    mergeInputs (i.succ.insertNth (α := fun _ => M) 1 x) i = x := by
  ext j
  by_cases hji : j < i
  · simp only [mergeInputs, hji, ite_true]
    rw [tupleInsert_lt _ _ _ _ (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)]
    rfl
  · by_cases he : j = i
    · subst j
      simp only [mergeInputs, lt_self_iff_false, ite_false, ite_true]
      rw [tupleInsert_lt _ _ _ _ (by simp), Fin.insertNth_apply_same, mul_one]
      rfl
    · have hij : i.val < j.val := by
        have hne : i.val ≠ j.val := fun h => he (Fin.ext h.symm)
        omega
      simp only [mergeInputs, hji, he, ite_false]
      rw [tupleInsert_gt _ _ _ _ (by simpa only [Fin.val_succ, Nat.add_lt_add_iff_right] using hij)]
      rfl

lemma curryMid_middleCoboundary_succ {n : ℕ} (f : Cochain M (n + 1))
    (i : Fin (n + 1)) :
    (middleCoboundary f i).curryMid i.succ 1 = f := by
  ext x
  change middleCoboundary f i (i.succ.insertNth (α := fun _ => M) 1 x) = f x
  rw [middleCoboundary_apply, merge_insert_succ_one]

lemma curryMid_middleCoboundary_after {n : ℕ} (f : Cochain M (n + 2))
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i.val ≤ j.val) :
    (middleCoboundary f j.succ).curryMid i.castSucc 1 =
      middleCoboundary (f.curryMid i 1) j := by
  ext x
  change middleCoboundary f j.succ (i.castSucc.insertNth (α := fun _ => M) 1 x) =
    middleCoboundary (f.curryMid i 1) j x
  simp only [middleCoboundary_apply]
  have hs : i.succAbove j = j.succ :=
    Fin.succAbove_of_le_castSucc i j (by simpa only [Fin.le_def, Fin.val_castSucc] using hij)
  rw [← hs, merge_insert_after x i 1 j hij]
  rfl

lemma merge_insert_succ_before {n : ℕ} (x : Fin (n + 1) → M)
    (i : Fin (n + 1)) (j : Fin n) (hji : j.val < i.val) :
    mergeInputs (i.succ.insertNth (α := fun _ => M) 1 x) j.castSucc =
      i.insertNth 1 (mergeInputs x j) := by
  funext k
  simp only [mergeInputs, ← tupleInsert_eq, tupleInsert, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ, Fin.ext_iff]
  split_ifs <;> try omega
  all_goals first | rfl | congr 1
  all_goals first | rfl | exact Fin.ext (by dsimp; omega)

lemma curryMid_middleCoboundary_before {n : ℕ} (f : Cochain M (n + 2))
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.val < i.val) :
    (middleCoboundary f j.castSucc).curryMid i.succ 1 =
      middleCoboundary (f.curryMid i 1) j := by
  ext x
  change middleCoboundary f j.castSucc (i.succ.insertNth (α := fun _ => M) 1 x) =
    middleCoboundary (f.curryMid i 1) j x
  rw [middleCoboundary_apply, middleCoboundary_apply, merge_insert_succ_before x i j hji]
  rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma unitaryPrefix_removeNth_before {n : ℕ} (u : Fin (n + 2) → unitary M)
    (p : Fin (n + 2)) (k : ℕ) (hpk : p.val < k) :
    p.removeNth (unitaryPrefix u k) = unitaryPrefix (p.removeNth u) (k - 1) := by
  funext j
  change (if (p.succAbove j).val < k then u (p.succAbove j) else 1) =
    (if j.val < k - 1 then u (p.succAbove j) else 1)
  by_cases hjp : j.castSucc < p
  · rw [Fin.succAbove_of_castSucc_lt p j hjp]
    have hj : j.val < p.val := hjp
    simp only [Fin.val_castSucc, show j.val < k by omega,
      show j.val < k - 1 by omega, ite_true]
  · rw [Fin.succAbove_of_le_castSucc p j (le_of_not_gt hjp)]
    have hpj : p.val ≤ j.val := le_of_not_gt hjp
    have he : j.val + 1 < k ↔ j.val < k - 1 := by omega
    simp only [Fin.val_succ, he]

lemma unitaryPrefix_removeNth_after {n : ℕ} (u : Fin (n + 2) → unitary M)
    (p : Fin (n + 2)) (k : ℕ) (hkp : k ≤ p.val) :
    p.removeNth (unitaryPrefix u k) = unitaryPrefix (p.removeNth u) k := by
  funext j
  change (if (p.succAbove j).val < k then u (p.succAbove j) else 1) =
    (if j.val < k then u (p.succAbove j) else 1)
  by_cases hjp : j.castSucc < p
  · rw [Fin.succAbove_of_castSucc_lt p j hjp]
    rfl
  · rw [Fin.succAbove_of_le_castSucc p j (le_of_not_gt hjp)]
    have hpj : p.val ≤ j.val := le_of_not_gt hjp
    simp only [Fin.val_succ, show ¬j.val + 1 < k by omega,
      show ¬j.val < k by omega, ite_false]

lemma unitaryPrefix_tail {n : ℕ} (u : Fin (n + 2) → unitary M) (k : ℕ) :
    Fin.tail (unitaryPrefix u (k + 1)) = unitaryPrefix (Fin.tail u) k := by
  simpa only [Fin.removeNth_zero, Nat.add_sub_cancel] using
    unitaryPrefix_removeNth_before u 0 (k + 1) (by simp)

lemma unitaryPrefix_init {n : ℕ} (u : Fin (n + 2) → unitary M) (k : ℕ) :
    Fin.init (unitaryPrefix u k) = unitaryPrefix (Fin.init u) k := by
  funext j
  rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma barInsertion_leftCoboundary_zero {n : ℕ} (u : Fin (n + 3) → unitary M)
    (f : Cochain M (n + 1)) : barInsertion u 0 (leftCoboundary f) = f := by
  unfold barInsertion
  rw [cochainUnitaryTransport_leftCoboundary, unitaryPrefix_tail]
  simp only [Fin.val_zero]
  have hp : unitaryPrefix (Fin.tail u) 0 = (fun _ => 1) := by
    funext j
    simp [unitaryPrefix]
  rw [hp, cochainUnitaryTransport_one, curryMid_leftCoboundary_zero]

lemma barInsertion_leftCoboundary_succ {n : ℕ} (u : Fin (n + 3) → unitary M)
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    barInsertion u i.succ (leftCoboundary f) =
      leftCoboundary (barInsertion (Fin.tail u) i f) := by
  unfold barInsertion
  rw [cochainUnitaryTransport_leftCoboundary, unitaryPrefix_tail,
    curryMid_leftCoboundary_succ]
  simp only [Fin.val_succ]

lemma barInsertion_rightCoboundary_last {n : ℕ} (u : Fin (n + 3) → unitary M)
    (f : Cochain M (n + 1)) :
    barInsertion u (Fin.last (n + 1)) (rightCoboundary f) =
      cochainUnitaryTransport (Fin.init u) f := by
  unfold barInsertion
  rw [cochainUnitaryTransport_rightCoboundary]
  change (rightCoboundary (cochainUnitaryTransport
    (Fin.init (unitaryPrefix u (n + 2))) f)).curryMid (Fin.last (n + 1)) 1 = _
  rw [unitaryPrefix_init, curryMid_rightCoboundary_last]
  have hp : unitaryPrefix (Fin.init u) (n + 2) = Fin.init u := by
    funext j
    simp only [unitaryPrefix, j.isLt, ite_true]
  rw [hp]

lemma barInsertion_rightCoboundary_castSucc {n : ℕ} (u : Fin (n + 3) → unitary M)
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    barInsertion u i.castSucc (rightCoboundary f) =
      rightCoboundary (barInsertion (Fin.init u) i f) := by
  unfold barInsertion
  rw [cochainUnitaryTransport_rightCoboundary]
  change (rightCoboundary (cochainUnitaryTransport
    (Fin.init (unitaryPrefix u (i.val + 1))) f)).curryMid i.castSucc 1 = _
  rw [unitaryPrefix_init, curryMid_rightCoboundary_castSucc]

lemma barInsertion_middleCoboundary_castSucc {n : ℕ}
    (u : Fin (n + 3) → unitary M) (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    barInsertion u i.castSucc (middleCoboundary f i) =
      cochainUnitaryTransport (unitaryPrefix (i.castSucc.succ.removeNth u) (i.val + 1)) f := by
  unfold barInsertion
  simp only [Fin.val_castSucc]
  rw [cochainUnitaryTransport_middleCoboundary,
    unitaryPrefix_removeNth_after u i.castSucc.succ (i.val + 1) (by simp),
    curryMid_middleCoboundary_castSucc]

lemma barInsertion_middleCoboundary_succ {n : ℕ}
    (u : Fin (n + 3) → unitary M) (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    barInsertion u i.succ (middleCoboundary f i) =
      cochainUnitaryTransport (unitaryPrefix (i.castSucc.succ.removeNth u) (i.val + 1)) f := by
  unfold barInsertion
  rw [cochainUnitaryTransport_middleCoboundary,
    unitaryPrefix_removeNth_before u i.castSucc.succ (i.succ.val + 1) (by simp),
    curryMid_middleCoboundary_succ]
  rfl

lemma barInsertion_middleCoboundary_after {n : ℕ}
    (u : Fin (n + 4) → unitary M) (f : Cochain M (n + 2))
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i.val ≤ j.val) :
    barInsertion u i.castSucc (middleCoboundary f j.succ) =
      middleCoboundary (barInsertion (j.succ.castSucc.succ.removeNth u) i f) j := by
  unfold barInsertion
  rw [cochainUnitaryTransport_middleCoboundary,
    unitaryPrefix_removeNth_after u j.succ.castSucc.succ (i.castSucc.val + 1)
      (by simp only [Fin.val_castSucc, Fin.val_succ]; omega),
    curryMid_middleCoboundary_after _ i j hij]
  simp only [Fin.val_castSucc]

lemma barInsertion_middleCoboundary_before {n : ℕ}
    (u : Fin (n + 4) → unitary M) (f : Cochain M (n + 2))
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.val < i.val) :
    barInsertion u i.succ (middleCoboundary f j.castSucc) =
      middleCoboundary (barInsertion (j.castSucc.castSucc.succ.removeNth u) i f) j := by
  unfold barInsertion
  rw [cochainUnitaryTransport_middleCoboundary,
    unitaryPrefix_removeNth_before u j.castSucc.castSucc.succ (i.succ.val + 1)
      (by simp only [Fin.val_castSucc, Fin.val_succ]; omega),
    curryMid_middleCoboundary_before _ i j hji]
  simp only [Fin.val_succ, Nat.add_sub_cancel]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M G : Type*} [CStarAlgebra M] [Group G] [Fintype G]

def finiteGroupPrefixAverage {n : ℕ} (ρ : G →* unitary M) (k : ℕ)
    (f : Cochain M n) : Cochain M n :=
  (Fintype.card (Fin (n + 1) → G) : ℂ)⁻¹ •
    ∑ g : Fin (n + 1) → G, cochainUnitaryTransport (unitaryPrefix (fun j => ρ (g j)) k) f
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u v
variable {M : Type u} [CStarAlgebra M] {G : Type v} [Group G] [Fintype G]

lemma finiteGroupBarInsertion_coface {n : ℕ} (ρ : G →* unitary M)
    (L : Cochain M (n + 1) →ₗ[ℂ] Cochain M (n + 2))
    (K : Cochain M n →ₗ[ℂ] Cochain M (n + 1))
    (i : Fin (n + 2)) (j : Fin (n + 1)) (p : Fin (n + 3))
    (f : Cochain M (n + 1))
    (h : ∀ u : Fin (n + 3) → unitary M,
      barInsertion u i (L f) = K (barInsertion (p.removeNth u) j f)) :
    finiteGroupBarInsertion ρ i (L f) = K (finiteGroupBarInsertion ρ j f) := by
  have ht (g : Fin (n + 3) → G) :
      barInsertion (fun k => ρ (g k)) i (L f) =
        K (barInsertion (fun k => ρ (p.removeNth g k)) j f) := h (fun k => ρ (g k))
  unfold finiteGroupBarInsertion
  simp_rw [ht]
  rw [← map_sum, ← map_smul]
  congr 1
  exact normalized_sum_removeNth p (fun g => barInsertion (fun k => ρ (g k)) j f)

lemma finiteGroupBarInsertion_left_zero {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) : finiteGroupBarInsertion ρ 0 (leftCoboundary f) = f := by
  simp only [finiteGroupBarInsertion, barInsertion_leftCoboundary_zero,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)), one_smul]

lemma finiteGroupBarInsertion_left_succ {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    finiteGroupBarInsertion ρ i.succ (leftCoboundary f) =
      leftCoboundary (finiteGroupBarInsertion ρ i f) := by
  apply finiteGroupBarInsertion_coface ρ (leftFaceLinear (n + 1)) (leftFaceLinear n) i.succ i 0 f
  intro u
  simpa only [leftFaceLinear, LinearMap.coe_mk, AddHom.coe_mk, Fin.removeNth_zero] using
    barInsertion_leftCoboundary_succ u f i

lemma finiteGroupBarInsertion_right_last {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) :
    finiteGroupBarInsertion ρ (Fin.last (n + 1)) (rightCoboundary f) =
      finiteGroupCochainAverage ρ f := by
  unfold finiteGroupBarInsertion
  simp only [barInsertion_rightCoboundary_last]
  change (Fintype.card (Fin (n + 3) → G) : ℂ)⁻¹ •
      (∑ g : Fin (n + 3) → G,
        cochainUnitaryTransport (fun k => ρ (Fin.init g k)) f) = _
  rw [show (fun g : Fin (n + 3) → G =>
      cochainUnitaryTransport (fun k => ρ (Fin.init g k)) f) =
    (fun g => cochainUnitaryTransport (fun k => ρ ((Fin.last (n + 2)).removeNth g k)) f) from by
      funext g
      rw [Fin.removeNth_last]]
  exact normalized_sum_removeNth (Fin.last (n + 2))
    (fun g => cochainUnitaryTransport (fun k => ρ (g k)) f)

lemma finiteGroupBarInsertion_right_castSucc {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    finiteGroupBarInsertion ρ i.castSucc (rightCoboundary f) =
      rightCoboundary (finiteGroupBarInsertion ρ i f) := by
  apply finiteGroupBarInsertion_coface ρ (rightFaceLinear (n + 1)) (rightFaceLinear n)
    i.castSucc i (Fin.last (n + 2)) f
  intro u
  simpa only [rightFaceLinear, LinearMap.coe_mk, AddHom.coe_mk, Fin.removeNth_last] using
    barInsertion_rightCoboundary_castSucc u f i

lemma finiteGroupBarInsertion_middle_castSucc {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    finiteGroupBarInsertion ρ i.castSucc (middleCoboundary f i) =
      finiteGroupPrefixAverage ρ (i.val + 1) f := by
  unfold finiteGroupBarInsertion
  simp only [barInsertion_middleCoboundary_castSucc]
  exact normalized_sum_removeNth i.castSucc.succ
    (fun g => cochainUnitaryTransport (unitaryPrefix (fun k => ρ (g k)) (i.val + 1)) f)

lemma finiteGroupBarInsertion_middle_succ {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    finiteGroupBarInsertion ρ i.succ (middleCoboundary f i) =
      finiteGroupPrefixAverage ρ (i.val + 1) f := by
  unfold finiteGroupBarInsertion
  simp only [barInsertion_middleCoboundary_succ]
  exact normalized_sum_removeNth i.castSucc.succ
    (fun g => cochainUnitaryTransport (unitaryPrefix (fun k => ρ (g k)) (i.val + 1)) f)

lemma finiteGroupBarInsertion_middle_after {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 2)) (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i.val ≤ j.val) :
    finiteGroupBarInsertion ρ i.castSucc (middleCoboundary f j.succ) =
      middleCoboundary (finiteGroupBarInsertion ρ i f) j := by
  apply finiteGroupBarInsertion_coface ρ (middleFaceLinear j.succ) (middleFaceLinear j)
    i.castSucc i j.succ.castSucc.succ f
  intro u
  exact barInsertion_middleCoboundary_after u f i j hij

lemma finiteGroupBarInsertion_middle_before {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 2)) (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.val < i.val) :
    finiteGroupBarInsertion ρ i.succ (middleCoboundary f j.castSucc) =
      middleCoboundary (finiteGroupBarInsertion ρ i f) j := by
  apply finiteGroupBarInsertion_coface ρ (middleFaceLinear j.castSucc) (middleFaceLinear j)
    i.succ i j.castSucc.castSucc.succ f
  intro u
  exact barInsertion_middleCoboundary_before u f i j hji
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M G : Type*} [CStarAlgebra M] [Group G] [Fintype G]

private def faceShuffle (n : ℕ) :
    (Fin (n + 2) × Fin (n + 1)) ≃ (Fin (n + 2) × Fin (n + 1)) where
  toFun p := (p.1.succAbove p.2, p.2.predAbove p.1)
  invFun p := (p.1.succAbove p.2, p.2.predAbove p.1)
  left_inv p := by
    exact Prod.ext (Fin.succAbove_succAbove_predAbove p.1 p.2)
      (Fin.predAbove_predAbove_succAbove p.1 p.2)
  right_inv p := by
    exact Prod.ext (Fin.succAbove_succAbove_predAbove p.1 p.2)
      (Fin.predAbove_predAbove_succAbove p.1 p.2)

private lemma sum_faceShuffle {n : ℕ} (F : Fin (n + 2) → Fin (n + 1) → Cochain M (n + 2)) :
    (∑ j : Fin (n + 2), ∑ k : Fin (n + 1), F (j.succAbove k) (k.predAbove j)) =
      ∑ i : Fin (n + 2), ∑ q : Fin (n + 1), F i q := by
  simpa only [Fintype.sum_prod_type] using
    Fintype.sum_equiv (faceShuffle n)
      (fun p => F (p.1.succAbove p.2) (p.2.predAbove p.1))
      (fun p => F p.1 p.2) (fun _ => rfl)

private lemma bar_middle_adjacent (ρ : G →* unitary M) {n : ℕ}
    (f : Cochain M (n + 2)) (j : Fin (n + 2)) :
    ((-1 : ℂ) ^ (j.val + j.val + 1)) •
        finiteGroupBarInsertion ρ j.castSucc (middleCoboundary f j) +
      ((-1 : ℂ) ^ (j.val + 1 + j.val + 1)) •
        finiteGroupBarInsertion ρ j.succ (middleCoboundary f j) = 0 := by
  rw [finiteGroupBarInsertion_middle_castSucc, finiteGroupBarInsertion_middle_succ]
  have h : j.val + 1 + j.val + 1 = (j.val + j.val + 1) + 1 := by omega
  have hp : (-1 : ℂ) ^ (j.val + 1 + j.val + 1) =
      -((-1 : ℂ) ^ (j.val + j.val + 1)) := by
    rw [h, pow_succ]
    ring
  rw [hp, neg_smul, add_neg_cancel]

private lemma bar_middle_off_face (ρ : G →* unitary M) {n : ℕ}
    (f : Cochain M (n + 2)) (j : Fin (n + 2)) (k : Fin (n + 1)) :
    finiteGroupBarInsertion ρ (j.castSucc.succAbove (j.succAbove k))
        (middleCoboundary f j) =
      middleCoboundary (finiteGroupBarInsertion ρ (j.succAbove k) f) (k.predAbove j) := by
  by_cases hkj : k.castSucc < j
  · have hj0 : j ≠ 0 := by
      intro hj
      subst j
      exact (not_lt_zero hkj)
    let q : Fin (n + 1) := j.pred hj0
    have hq : q.succ = j := Fin.succ_pred _ _
    have hi : j.succAbove k = k.castSucc := Fin.succAbove_of_castSucc_lt _ _ hkj
    have hp : k.predAbove j = q := Fin.predAbove_of_castSucc_lt _ _ hkj
    have ht : j.castSucc.succAbove (j.succAbove k) = k.castSucc.castSucc := by
      rw [hi, Fin.succAbove_of_castSucc_lt]
      exact hkj
    rw [ht, hi, hp, ← hq]
    exact finiteGroupBarInsertion_middle_after ρ f k.castSucc q (by
      have hv : k.val < j.val := hkj
      dsimp [q]
      omega)
  · have hjk : j.val ≤ k.val := le_of_not_gt hkj
    have hjlast : j ≠ Fin.last (n + 1) := by
      intro hj
      subst j
      have hk := k.isLt
      simp only [Fin.val_last] at hjk
      omega
    let q : Fin (n + 1) := j.castPred hjlast
    have hq : q.castSucc = j := Fin.castSucc_castPred _ _
    have hi : j.succAbove k = k.succ := Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hkj)
    have hp : k.predAbove j = q := Fin.predAbove_of_le_castSucc _ _ (le_of_not_gt hkj)
    have ht : j.castSucc.succAbove (j.succAbove k) = k.succ.succ := by
      rw [hi, Fin.succAbove_of_le_castSucc]
      simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]
      omega
    rw [ht, hi, hp, ← hq]
    exact finiteGroupBarInsertion_middle_before ρ f k.succ q (by
      dsimp [q]
      omega)

private lemma bar_middle_row (ρ : G →* unitary M) {n : ℕ}
    (f : Cochain M (n + 2)) (j : Fin (n + 2)) :
    (∑ i : Fin (n + 3), ((-1 : ℂ) ^ (i.val + j.val + 1)) •
      finiteGroupBarInsertion ρ i (middleCoboundary f j)) =
    ∑ k : Fin (n + 1),
      ((-1 : ℂ) ^ ((j.castSucc.succAbove (j.succAbove k)).val + j.val + 1)) •
        finiteGroupBarInsertion ρ (j.castSucc.succAbove (j.succAbove k))
          (middleCoboundary f j) := by
  rw [Fin.sum_univ_succAbove _ j.castSucc, Fin.sum_univ_succAbove _ j]
  simp only [Fin.succAbove_castSucc_self, Fin.val_castSucc, Fin.val_succ]
  rw [← add_assoc, bar_middle_adjacent, zero_add]

private lemma bar_middle_off_parity {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 1)) :
    (j.castSucc.succAbove (j.succAbove k)).val + j.val + 1 =
      (j.succAbove k).val + (k.predAbove j).val + 2 := by
  by_cases hkj : k.castSucc < j
  · rw [Fin.succAbove_of_castSucc_lt j k hkj,
      Fin.predAbove_of_castSucc_lt k j hkj,
      Fin.succAbove_of_castSucc_lt j.castSucc k.castSucc hkj]
    change k.val + j.val + 1 = k.val + (j.val - 1) + 2
    have hv : k.val < j.val := hkj
    omega
  · have hjk := le_of_not_gt hkj
    rw [Fin.succAbove_of_le_castSucc j k hjk,
      Fin.predAbove_of_le_castSucc k j hjk,
      Fin.succAbove_of_le_castSucc j.castSucc k.succ (by
        simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] at *
        omega)]
    change (k.val + 1 + 1) + j.val + 1 = (k.val + 1) + j.val + 2
    omega

private lemma bar_middle_off_signed (ρ : G →* unitary M) {n : ℕ}
    (f : Cochain M (n + 2)) (j : Fin (n + 2)) (k : Fin (n + 1)) :
    ((-1 : ℂ) ^ ((j.castSucc.succAbove (j.succAbove k)).val + j.val + 1)) •
        finiteGroupBarInsertion ρ (j.castSucc.succAbove (j.succAbove k))
          (middleCoboundary f j) =
    -(((-1 : ℂ) ^ ((j.succAbove k).val + (k.predAbove j).val + 1)) •
        middleCoboundary (finiteGroupBarInsertion ρ (j.succAbove k) f) (k.predAbove j)) := by
  rw [bar_middle_off_face, bar_middle_off_parity]
  have hp : (-1 : ℂ) ^ ((j.succAbove k).val + (k.predAbove j).val + 2) =
      -((-1 : ℂ) ^ ((j.succAbove k).val + (k.predAbove j).val + 1)) := by
    rw [show (j.succAbove k).val + (k.predAbove j).val + 2 =
      ((j.succAbove k).val + (k.predAbove j).val + 1) + 1 by omega, pow_succ]
    ring
  rw [hp, neg_smul]

lemma finite_bar_middle_double_sum (ρ : G →* unitary M) {n : ℕ}
    (f : Cochain M (n + 2)) :
    (∑ j : Fin (n + 2), ∑ i : Fin (n + 3),
      ((-1 : ℂ) ^ (i.val + j.val + 1)) • finiteGroupBarInsertion ρ i (middleCoboundary f j)) =
    -(∑ i : Fin (n + 2), ∑ q : Fin (n + 1),
      ((-1 : ℂ) ^ (i.val + q.val + 1)) •
        middleCoboundary (finiteGroupBarInsertion ρ i f) q) := by
  simp_rw [bar_middle_row, bar_middle_off_signed]
  simp only [Finset.sum_neg_distrib]
  congr 1
  exact sum_faceShuffle (fun i q => ((-1 : ℂ) ^ (i.val + q.val + 1)) •
    middleCoboundary (finiteGroupBarInsertion ρ i f) q)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M G : Type*} [CStarAlgebra M] [Group G] [Fintype G]

lemma finiteGroupBarOperator_sum {I : Type*} {n : ℕ} (ρ : G →* unitary M)
    (s : Finset I) (f : I → Cochain M (n + 1)) :
    finiteGroupBarOperator ρ (∑ i ∈ s, f i) = ∑ i ∈ s, finiteGroupBarOperator ρ (f i) :=
  map_sum (finiteGroupBarOperatorCLM ρ n) f s

lemma finiteGroupBarOperator_leftCoboundary {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) :
    finiteGroupBarOperator ρ (leftCoboundary f) =
      f - leftCoboundary (finiteGroupBarOperator ρ f) := by
  have he : leftCoboundary (finiteGroupBarOperator ρ f) =
      ∑ i : Fin (n + 1), ((-1 : ℂ) ^ i.val) •
        leftCoboundary (finiteGroupBarInsertion ρ i f) := by
    change leftFaceLinear n (∑ i : Fin (n + 1), ((-1 : ℂ) ^ i.val) •
      finiteGroupBarInsertion ρ i f) = _
    rw [map_sum]
    simp only [map_smul]
    rfl
  rw [he]
  change (∑ i : Fin (n + 2), ((-1 : ℂ) ^ i.val) •
    finiteGroupBarInsertion ρ i (leftCoboundary f)) = _
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, finiteGroupBarInsertion_left_zero,
    Fin.val_succ, finiteGroupBarInsertion_left_succ]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ, mul_neg, mul_one, neg_smul]

lemma finiteGroupBarOperator_rightCoboundary {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) :
    finiteGroupBarOperator ρ (rightCoboundary f) =
      rightCoboundary (finiteGroupBarOperator ρ f) +
        ((-1 : ℂ) ^ (n + 1)) • finiteGroupCochainAverage ρ f := by
  have he : rightCoboundary (finiteGroupBarOperator ρ f) =
      ∑ i : Fin (n + 1), ((-1 : ℂ) ^ i.val) •
        rightCoboundary (finiteGroupBarInsertion ρ i f) := by
    change rightFaceLinear n (∑ i : Fin (n + 1), ((-1 : ℂ) ^ i.val) •
      finiteGroupBarInsertion ρ i f) = _
    rw [map_sum]
    simp only [map_smul]
    rfl
  rw [he]
  change (∑ i : Fin (n + 2), ((-1 : ℂ) ^ i.val) •
    finiteGroupBarInsertion ρ i (rightCoboundary f)) = _
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, finiteGroupBarInsertion_right_castSucc,
    finiteGroupBarInsertion_right_last]

lemma finiteGroupBarOperator_middleSum {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 2)) :
    finiteGroupBarOperator ρ (∑ j : Fin (n + 2), ((-1 : ℂ) ^ (j.val + 1)) • middleCoboundary f j) =
      -(∑ q : Fin (n + 1), ((-1 : ℂ) ^ (q.val + 1)) •
        middleCoboundary (finiteGroupBarOperator ρ f) q) := by
  have he (q : Fin (n + 1)) : middleCoboundary (finiteGroupBarOperator ρ f) q =
      ∑ i : Fin (n + 2), ((-1 : ℂ) ^ i.val) •
        middleCoboundary (finiteGroupBarInsertion ρ i f) q := by
    change middleFaceLinear q (∑ i : Fin (n + 2), ((-1 : ℂ) ^ i.val) •
      finiteGroupBarInsertion ρ i f) = _
    rw [map_sum]
    simp only [map_smul]
    rfl
  simp_rw [he]
  rw [finiteGroupBarOperator_sum]
  simp_rw [finiteGroupBarOperator_smul]
  simp only [finiteGroupBarOperator,
    Finset.smul_sum, smul_smul, ← pow_add]
  have hleft (j : Fin (n + 2)) (i : Fin (n + 3)) : j.val + 1 + i.val = i.val + j.val + 1 := by omega
  have hright (q : Fin (n + 1)) (i : Fin (n + 2)) : q.val + 1 + i.val = i.val + q.val + 1 := by omega
  simp only [hleft, hright]
  rw [Finset.sum_comm (f := fun q : Fin (n + 1) => fun i : Fin (n + 2) =>
    ((-1 : ℂ) ^ (i.val + q.val + 1)) • middleCoboundary (finiteGroupBarInsertion ρ i f) q)]
  exact finite_bar_middle_double_sum ρ f

theorem finiteGroupBarOperator_homotopy {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 2)) :
    differential (finiteGroupBarOperator ρ f) + finiteGroupBarOperator ρ (differential f) =
      f - finiteGroupCochainAverage ρ f := by
  change (leftCoboundary (finiteGroupBarOperator ρ f) +
      (∑ q : Fin (n + 1), ((-1 : ℂ) ^ (q.val + 1)) •
        middleCoboundary (finiteGroupBarOperator ρ f) q) +
      ((-1 : ℂ) ^ (n + 2)) • rightCoboundary (finiteGroupBarOperator ρ f)) +
    finiteGroupBarOperator ρ (leftCoboundary f +
      (∑ j : Fin (n + 2), ((-1 : ℂ) ^ (j.val + 1)) • middleCoboundary f j) +
      ((-1 : ℂ) ^ (n + 3)) • rightCoboundary f) = _
  rw [finiteGroupBarOperator_add, finiteGroupBarOperator_add,
    finiteGroupBarOperator_smul, finiteGroupBarOperator_leftCoboundary,
    finiteGroupBarOperator_middleSum, finiteGroupBarOperator_rightCoboundary,
    smul_add, smul_smul]
  have hsign : (-1 : ℂ) ^ (n + 3) = -((-1 : ℂ) ^ (n + 2)) := by
    rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
    ring
  have hprod : (-1 : ℂ) ^ (n + 3) * (-1 : ℂ) ^ (n + 2) = -1 := by
    rw [hsign, neg_mul, ← mul_pow]
    norm_num
  rw [hprod, hsign, neg_smul, neg_one_smul]
  abel
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem countableMatrixBarOperator_homotopy (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f : Cochain M (n + 2)) :
    differential (countableMatrixBarOperator e c hi ho f) +
      countableMatrixBarOperator e c hi ho (differential f) =
        f - countableMatrixAverage e c hi ho f := by
  have hz : countableMatrixBarDefect e c hi ho f = 0 := by
    apply countableMatrixBarDefect_eq_zero_of_eventually
    filter_upwards [] with k
    unfold matrixSectionBarDefect matrixSectionBarOperator matrixSectionAverage
    rw [finiteGroupBarOperator_homotopy, sub_self]
  exact sub_eq_zero.mp hz

theorem countableMatrixBarOperator_cocycle (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f : Cochain M (n + 2)) (hf : ∀ x, differentialValue f x = 0) :
    differential (countableMatrixBarOperator e c hi ho f) =
      f - countableMatrixAverage e c hi ho f := by
  have hd : differential f = 0 := by
    ext x
    simpa only [differential_apply, zero_apply] using hf x
  have hzero : countableMatrixBarOperator e c hi ho (0 : Cochain M (n + 3)) = 0 :=
    map_zero (countableMatrixBarOperatorCLM e c hi ho (n + 2))
  have h := countableMatrixBarOperator_homotopy e c hi ho f
  simpa only [hd, hzero, add_zero] using h
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem properlyInfinite_primitive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) {n : ℕ} (f : Cochain M (n + 2))
    (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ∀ x, differentialValue g x = f x := by
  cases subsingleton_or_nontrivial M with
  | inl hM =>
      let := hM
      exact ⟨0, fun _ => Subsingleton.elim _ _⟩
  | inr hM =>
      let := hM
      obtain ⟨c, hi, ho, ht⟩ := exists_countable_isometries e hno
      obtain ⟨b, hb⟩ := primitive_of_countableMatrixAverage e hno c hi ho ht f hf
      have hH := countableMatrixBarOperator_cocycle e c hi ho f hf
      refine ⟨b + countableMatrixBarOperator e c hi ho f, fun x => ?_⟩
      have hx : differentialValue (countableMatrixBarOperator e c hi ho f) x =
          f x - countableMatrixAverage e c hi ho f x := by
        simpa only [differential_apply, sub_apply] using
          congrArg (fun F : Cochain M (n + 2) => F x) hH
      rw [differentialValue_add, hb, hx]
      abel

theorem properlyInfiniteVanishingInput : ProperlyInfiniteVanishingInput.{u} := by
  intro N hN hPO hSO hW hno n f hf
  let := hW
  obtain ⟨Y, hY, hYS, hYC, ⟨e⟩⟩ := WStarAlgebra.exists_predual (M := N)
  let := hY
  let := hYS
  let := hYC
  exact properlyInfinite_primitive e hno f hf
end BoundedHochschild.KadisonRingrose
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.KadisonRingrose.properlyInfiniteVanishingInput.{u} := @OAI.BoundedHochschild.KadisonRingrose.properlyInfiniteVanishingInput.{u}
