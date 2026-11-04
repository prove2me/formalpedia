-- Prove2me | solution 1 for OAI.SignedSweeps.pairTypeProjection_signed_commute
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T00:10:09.012543+00:00
-- url     : https://prove2.me/submissions/0973d6fb-e59c-4e0d-aca5-eea170a2aa78

-- Carved from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0),
-- lean/OAI/Probability/SignedSweeps/, ported to Lean 4.33.1 / Mathlib 0df444a.
-- The mathematics and the Lean code are OpenAI's.

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs
import Definitions.Def_OAISignedSweepsProofDefs2

section
-- module OAI.Probability.SignedSweeps.GroupAverage
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma representation_inner_inverse {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (g : G) (x y : E) :
    inner ℂ (ρ g x) y = inner ℂ x (ρ g⁻¹ y) := by
  let e : E →ₗᵢ[ℂ] E := ⟨ρ g, hρ g⟩
  have he : ρ g (ρ g⁻¹ y) = y := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  calc
    inner ℂ (ρ g x) y = inner ℂ (ρ g x) (ρ g (ρ g⁻¹ y)) := congrArg _ he.symm
    _ = inner ℂ x (ρ g⁻¹ y) := e.inner_map_map x (ρ g⁻¹ y)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.KernelTransition
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

lemma unitary_representation_adjoint {G : Type*} [Group G] (ρ : Representation ℂ G E)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (g : G) : (ρ g).adjoint = ρ g⁻¹ := by
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [LinearMap.adjoint_inner_right]
  exact representation_inner_inverse ρ hρ g y x

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.Isotypic
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E F : Type*} [Monoid G] [AddCommGroup E] [Module ℂ E]
  [AddCommGroup F] [Module ℂ F]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E F : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]
variable (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
  (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)

lemma submodule_projection_commute (S : Submodule ℂ F) (T : F →ₗ[ℂ] F)
    (hT : ∀ x ∈ S, T x ∈ S) (hT' : ∀ x ∈ S, T.adjoint x ∈ S) :
    S.starProjection.toLinearMap * T = T * S.starProjection.toLinearMap := by
  apply LinearMap.ext
  intro x
  change S.starProjection (T x) = T (S.starProjection x)
  apply S.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hT _ (S.starProjection_apply_mem x)
  · intro w hw
    change inner ℂ (T x - T (S.starProjection x)) w = 0
    rw [← map_sub, ← LinearMap.adjoint_inner_right]
    exact S.starProjection_inner_eq_zero x _ (hT' w hw)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordIsotypic
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

@[simp] lemma wordRepresentation_apply {p : ℕ} {C : Type*} [Fintype C]
    (g : SymmetricGroup p) (f : WordSpace p C) (w : Fin p → C) :
    wordRepresentation p C g f w = f (w ∘ g) := rfl

lemma wordRepresentation_norm {p : ℕ} {C : Type*} [Fintype C]
    (g : SymmetricGroup p) (f : WordSpace p C) :
    ‖wordRepresentation p C g f‖ = ‖f‖ := (wordIsometry g).norm_map f

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordEmbedding
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype J] in
lemma euclideanEmbeddingLinear_off (e : I ↪ J) (v : EuclideanSpace ℂ I)
    {j : J} (hj : j ∉ Set.range e) : euclideanEmbeddingLinear e v j = 0 := by
  rw [euclideanEmbeddingLinear_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (fun h => hj ⟨i, h⟩)

@[simp] lemma euclideanEmbedding_apply (e : I ↪ J) (v : EuclideanSpace ℂ I) :
    euclideanEmbedding e v = euclideanEmbeddingLinear e v := rfl

lemma euclideanEmbedding_single (e : I ↪ J) (i : I) :
    euclideanEmbedding e (EuclideanSpace.single i 1) = EuclideanSpace.single (e i) 1 := by
  ext j
  rw [euclideanEmbedding_apply, euclideanEmbeddingLinear_apply]
  simp only [PiLp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp [eq_comm]
  · intro k _ hki
    simp [hki]
  · simp

@[simp] lemma euclideanTensorEquiv_tmul (x : EuclideanSpace ℂ I) (y : EuclideanSpace ℂ J)
    (i : I) (j : J) : euclideanTensorEquiv (x ⊗ₜ[ℂ] y) (i,j) = x i * y j := by
  rw [euclideanTensorEquiv, OrthonormalBasis.tensorProduct_repr_tmul_apply]
  simp [mul_comm]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.HilbertBlocks
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

@[simp] lemma hilbertBlock_apply (j : E →ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) (x : F) :
    hilbertBlock j A x = j (A (j.toLinearMap.adjoint x)) := rfl

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {I J : Type*} [Fintype I] [Fintype J]

lemma euclideanTensorEquiv_single (i : I) (j : J) :
    euclideanTensorEquiv (EuclideanSpace.single i 1 ⊗ₜ[ℂ] EuclideanSpace.single j 1) =
      EuclideanSpace.single (i,j) 1 := by
  ext ⟨k,l⟩
  rw [euclideanTensorEquiv_tmul]
  simp only [PiLp.single_apply, Prod.mk.injEq]
  by_cases hk : k = i <;> by_cases hl : l = j <;> simp [hk, hl]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordAllocations
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma allocationEquiv_left_mem {u v p : ℕ} (h : u + v = p) (S : EvenAllocation u p) (i : Fin u) :
    allocationEquiv h S (Sum.inl i) ∈ S.1 :=
  ((Finset.equivFinOfCardEq S.2).symm i).2

lemma allocationEquiv_right_not_mem {u v p : ℕ} (h : u + v = p)
    (S : EvenAllocation u p) (i : Fin v) : allocationEquiv h S (Sum.inr i) ∉ S.1 :=
  ((Fintype.equivFinOfCardEq (allocation_complement_card h S)).symm i).2

lemma pairColorWord_evenSites {u v p : ℕ} {C : Type*} (h : u + v = p)
    (S : EvenAllocation u p) (w : (Fin u → C) × (Fin v → C)) :
    wordEvenSites (pairColorWord (allocationEquiv h S) w) = S.1 := by
  ext i
  obtain ⟨i, rfl⟩ := (allocationEquiv h S).surjective i
  cases i with
  | inl i =>
    simp only [mem_wordEvenSites, pairColorWord, Function.comp_apply,
      Equiv.symm_apply_apply, Sum.elim_inl, Sum.inl.injEq, exists_eq',
      allocationEquiv_left_mem, iff_self]
  | inr i =>
    simp only [mem_wordEvenSites, pairColorWord, Function.comp_apply,
      Equiv.symm_apply_apply, Sum.elim_inr, Sum.inr_ne_inl, exists_false,
      allocationEquiv_right_not_mem, iff_self]

lemma pairColorEmbedding_range {u v p : ℕ} {C : Type*} (h : u + v = p)
    (S : EvenAllocation u p) (w : Fin p → C ⊕ C) :
    w ∈ Set.range (pairColorEmbedding (C := C) (allocationEquiv h S)) ↔ wordEvenSites w = S.1 := by
  constructor
  · rintro ⟨z,rfl⟩
    exact pairColorWord_evenSites h S z
  · intro hw
    have he (i : Fin u) : ∃ c, w (allocationEquiv h S (Sum.inl i)) = Sum.inl c := by
      rw [← mem_wordEvenSites, hw]
      exact allocationEquiv_left_mem h S i
    have ho (j : Fin v) : ∃ c, w (allocationEquiv h S (Sum.inr j)) = Sum.inr c := by
      have hnot : allocationEquiv h S (Sum.inr j) ∉ wordEvenSites w := by
        rw [hw]; exact allocationEquiv_right_not_mem h S j
      cases hc : w (allocationEquiv h S (Sum.inr j)) with
      | inl c => exact False.elim (hnot ((mem_wordEvenSites _ _).mpr ⟨c,hc⟩))
      | inr c => exact ⟨c,rfl⟩
    choose z hz using he
    choose t ht using ho
    refine ⟨(z,t), ?_⟩
    funext i
    obtain ⟨i,rfl⟩ := (allocationEquiv h S).surjective i
    cases i with
    | inl i =>
      change Sum.elim (fun i => Sum.inl (z i)) (fun j => Sum.inr (t j))
        ((allocationEquiv h S).symm (allocationEquiv h S (Sum.inl i))) = _
      rw [Equiv.symm_apply_apply]
      exact (hz i).symm
    | inr j =>
      change Sum.elim (fun i => Sum.inl (z i)) (fun j => Sum.inr (t j))
        ((allocationEquiv h S).symm (allocationEquiv h S (Sum.inr j))) = _
      rw [Equiv.symm_apply_apply]
      exact (ht j).symm

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SignedWords
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
open Module
local instance (priority := 2000) signedWordsFunctionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) signedWordsSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

@[simp] lemma signedWordRepresentation_apply {p : ℕ} {C : Type*} [Fintype C]
    (g : SymmetricGroup p) (f : WordSpace p (C ⊕ C)) (w : Fin p → C ⊕ C) :
    signedWordRepresentation p C g f w = wordPhase g w * f (w ∘ g) := rfl

lemma wordEvenSites_comp_eq {p : ℕ} {C : Type*} (g : SymmetricGroup p)
    (w z : Fin p → C ⊕ C) (h : wordEvenSites w = wordEvenSites z) :
    wordEvenSites (w ∘ g) = wordEvenSites (z ∘ g) := by
  ext i
  simp only [wordEvenSites_comp_mem, h]

lemma oddPositionSetEquiv_sign_congr {p : ℕ} (g : SymmetricGroup p)
    {S T R U : Finset (Fin p)} (hS : S = T) (hT : R = U)
    (h1 : ∀ i, i ∈ R ↔ g i ∈ S) (h2 : ∀ i, i ∈ U ↔ g i ∈ T) :
    complexEquivSign (oddPositionSetEquiv g S R h1) =
      complexEquivSign (oddPositionSetEquiv g T U h2) := by
  subst T
  subst U
  rfl

lemma wordPhase_eq_of_parity {p : ℕ} {C : Type*} (g : SymmetricGroup p)
    (w z : Fin p → C ⊕ C) (h : wordEvenSites w = wordEvenSites z) :
    wordPhase g w = wordPhase g z := by
  have hi := wordEvenSites_comp_eq g w z h
  exact oddPositionSetEquiv_sign_congr g h hi _ _

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PairCovariance
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) pairCovarianceWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) pairCovarianceSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma wordTypeProjection_perm_commute {p : ℕ} (μ : Partition p) {C : Type*} [Fintype C]
    (g : SymmetricGroup p) :
    wordTypeProjection μ C * wordRepresentation p C g =
      wordRepresentation p C g * wordTypeProjection μ C := by
  apply submodule_projection_commute
  · exact fun x hx => (isotypicSubrepresentation (spechtRepresentation μ)
      (wordRepresentation p C)).apply_mem_toSubmodule g hx
  · rw [unitary_representation_adjoint _ (fun g x => wordRepresentation_norm g x)]
    exact fun x hx => (isotypicSubrepresentation (spechtRepresentation μ)
      (wordRepresentation p C)).apply_mem_toSubmodule g⁻¹ hx

lemma wordRepresentation_single {p : ℕ} {C : Type*} [Fintype C]
    (g : SymmetricGroup p) (w : Fin p → C) :
    wordRepresentation p C g (EuclideanSpace.single w 1) =
      EuclideanSpace.single (w ∘ (g⁻¹ : SymmetricGroup p)) 1 := by
  ext z
  simp only [wordRepresentation_apply, PiLp.single_apply]
  have he : z ∘ g = w ↔ z = w ∘ (g⁻¹ : SymmetricGroup p) := by
    constructor
    · intro h; funext i; simpa using congrFun h (g⁻¹ i)
    · rintro rfl; ext i; simp
  simp only [he]

lemma pairWordEmbedding_single {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) (w : Fin u → C) (z : Fin v → C) :
    pairWordEmbedding e (EuclideanSpace.single w 1 ⊗ₜ[ℂ] EuclideanSpace.single z 1) =
      EuclideanSpace.single (pairColorWord e (w,z)) 1 := by
  change euclideanEmbedding (pairColorEmbedding e)
    (euclideanTensorEquiv (EuclideanSpace.single w 1 ⊗ₜ[ℂ] EuclideanSpace.single z 1)) = _
  have he := euclideanTensorEquiv_single (I := Fin u → C) (J := Fin v → C) w z
  rw [he]
  convert euclideanEmbedding_single (pairColorEmbedding e) (w,z) using 1
  · congr 1
    ext j
    simp only [PiLp.single_apply]
    split_ifs <;> rfl
  · ext j
    simp only [PiLp.single_apply]
    rfl

lemma pairWordEmbedding_reindex {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) (g : SymmetricGroup p) :
    wordRepresentation p (C ⊕ C) g ∘ₗ (pairWordEmbedding (C := C) e).toLinearMap =
      (pairWordEmbedding (C := C) (e.trans g)).toLinearMap := by
  apply ((EuclideanSpace.basisFun (Fin u → C) ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin v → C) ℂ)).toBasis.ext
  rintro ⟨w,z⟩
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply,
    EuclideanSpace.basisFun_apply, LinearMap.comp_apply]
  change wordRepresentation p (C ⊕ C) g
    (pairWordEmbedding e (EuclideanSpace.single w 1 ⊗ₜ[ℂ] EuclideanSpace.single z 1)) =
    pairWordEmbedding (e.trans g) (EuclideanSpace.single w 1 ⊗ₜ[ℂ] EuclideanSpace.single z 1)
  rw [pairWordEmbedding_single, wordRepresentation_single, pairWordEmbedding_single]
  rfl

lemma pairWordEmbedding_internal {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) (a : SymmetricGroup u) (b : SymmetricGroup v) :
    (pairWordEmbedding (C := C) ((a.sumCongr b).trans e)).toLinearMap =
      (pairWordEmbedding (C := C) e).toLinearMap ∘ₗ
        TensorProduct.map (wordRepresentation u C a) (wordRepresentation v C b) := by
  apply ((EuclideanSpace.basisFun (Fin u → C) ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin v → C) ℂ)).toBasis.ext
  rintro ⟨w,z⟩
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply,
    EuclideanSpace.basisFun_apply, LinearMap.comp_apply]
  change pairWordEmbedding ((a.sumCongr b).trans e)
    (EuclideanSpace.single w 1 ⊗ₜ[ℂ] EuclideanSpace.single z 1) =
    pairWordEmbedding e (TensorProduct.map (wordRepresentation u C a) (wordRepresentation v C b)
      (EuclideanSpace.single w 1 ⊗ₜ[ℂ] EuclideanSpace.single z 1))
  rw [TensorProduct.map_tmul, wordRepresentation_single, wordRepresentation_single,
    pairWordEmbedding_single, pairWordEmbedding_single]
  congr 1
  funext i
  cases hi : e.symm i <;> simp [pairColorWord, hi]

lemma allocation_factorEquiv {u v p : ℕ} (h : u+v=p) (S : EvenAllocation u p)
    (f : (Fin u ⊕ Fin v) ≃ Fin p) (hf : ∀ i, f (Sum.inl i) ∈ S.1) :
    ∃ a : SymmetricGroup u, ∃ b : SymmetricGroup v,
      f = (a.sumCongr b).trans (allocationEquiv h S) := by
  let t : Equiv.Perm (Fin u ⊕ Fin v) := f.trans (allocationEquiv h S).symm
  have ht : Set.MapsTo t (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨i,rfl⟩
    cases he : t (Sum.inl i) with
    | inl k => exact ⟨k,rfl⟩
    | inr j =>
      have hj : f (Sum.inl i) = allocationEquiv h S (Sum.inr j) := by
        have hx := congrArg (allocationEquiv h S) he
        simpa [t] using hx
      exact False.elim (allocationEquiv_right_not_mem h S j (hj ▸ hf i))
  obtain ⟨⟨a,b⟩, hab⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl ht
  refine ⟨a,b,?_⟩
  apply Equiv.ext
  intro i
  have hi := congrArg (fun k : Equiv.Perm (Fin u ⊕ Fin v) => allocationEquiv h S (k i)) hab
  simpa [t] using hi.symm

lemma hilbertBlock_precomp {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (j k : E →ₗᵢ[ℂ] F) (U P : E →ₗ[ℂ] E)
    (hk : k.toLinearMap = j.toLinearMap ∘ₗ U) (hUU : U * U.adjoint = 1)
    (hUP : U * P = P * U) : hilbertBlock k P = hilbertBlock j P := by
  change k.toLinearMap ∘ₗ P ∘ₗ k.toLinearMap.adjoint = j.toLinearMap ∘ₗ P ∘ₗ j.toLinearMap.adjoint
  rw [hk, LinearMap.adjoint_comp]
  have he : U ∘ₗ P ∘ₗ U.adjoint = P := by
    change U * P * U.adjoint = P
    rw [hUP, mul_assoc, hUU, mul_one]
  calc
    _ = j.toLinearMap ∘ₗ (U ∘ₗ P ∘ₗ U.adjoint) ∘ₗ j.toLinearMap.adjoint := by
      simp only [LinearMap.comp_assoc]
    _ = _ := by rw [he]

lemma pairTypeBlock_allocation {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) (S : EvenAllocation u p)
    (f : (Fin u ⊕ Fin v) ≃ Fin p) (hf : ∀ i, f (Sum.inl i) ∈ S.1) :
    hilbertBlock (pairWordEmbedding (C := C) f)
        (TensorProduct.map (wordTypeProjection α C) (wordTypeProjection β C)) =
      hilbertBlock (pairWordEmbedding (C := C) (allocationEquiv h S))
        (TensorProduct.map (wordTypeProjection α C) (wordTypeProjection β C)) := by
  obtain ⟨a,b,rfl⟩ := allocation_factorEquiv h S f hf
  apply hilbertBlock_precomp _ _
    (TensorProduct.map (wordRepresentation u C a) (wordRepresentation v C b)) _
    (pairWordEmbedding_internal _ a b)
  · have ha : (wordRepresentation u C a).adjoint = wordRepresentation u C a⁻¹ :=
      unitary_representation_adjoint _ (fun g x => wordRepresentation_norm g x) a
    have hb : (wordRepresentation v C b).adjoint = wordRepresentation v C b⁻¹ :=
      unitary_representation_adjoint _ (fun g x => wordRepresentation_norm g x) b
    rw [TensorProduct.adjoint_map, ha, hb, ← TensorProduct.map_mul,
      ← map_mul, ← map_mul, mul_inv_cancel, mul_inv_cancel, map_one, map_one,
      TensorProduct.map_one]

  · rw [← TensorProduct.map_mul, ← TensorProduct.map_mul,
      wordTypeProjection_perm_commute, wordTypeProjection_perm_commute]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PairCentral
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) pairCentralAllocationFunctionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) pairCentralAllocationSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

def allocationMap {u p : ℕ} (g : SymmetricGroup p) : EvenAllocation u p ≃ EvenAllocation u p where
  toFun S := ⟨S.1.map g.toEmbedding, by simpa using S.2⟩
  invFun S := ⟨S.1.map g.symm.toEmbedding, by simpa using S.2⟩
  left_inv S := by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Equiv.symm_apply_apply]
  right_inv S := by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]

lemma allocationMap_mem {u p : ℕ} (g : SymmetricGroup p) (S : EvenAllocation u p)
    {i : Fin p} (hi : i ∈ S.1) : g i ∈ (allocationMap g S).1 := by
  change g i ∈ S.1.map g.toEmbedding
  exact Finset.mem_map.mpr ⟨i,hi,rfl⟩

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) pairCentralHilbertFunctionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) pairCentralHilbertSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

lemma hilbertBlock_postcomp (j k : E →ₗᵢ[ℂ] F) (U : F →ₗ[ℂ] F) (P : E →ₗ[ℂ] E)
    (hk : k.toLinearMap = U ∘ₗ j.toLinearMap) :
    U * hilbertBlock j P * U.adjoint = hilbertBlock k P := by
  change U ∘ₗ (j.toLinearMap ∘ₗ P ∘ₗ j.toLinearMap.adjoint) ∘ₗ U.adjoint =
    k.toLinearMap ∘ₗ P ∘ₗ k.toLinearMap.adjoint
  rw [hk, LinearMap.adjoint_comp]
  simp only [LinearMap.comp_assoc]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) pairCentralProjectionFunctionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) pairCentralProjectionSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma pairTypeProjection_permute_conj {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) (g : SymmetricGroup p) :
    wordRepresentation p (C ⊕ C) g * pairTypeProjection h α β C *
        (wordRepresentation p (C ⊕ C) g).adjoint = pairTypeProjection h α β C := by
  let Q := TensorProduct.map (wordTypeProjection α C) (wordTypeProjection β C)
  unfold pairTypeProjection
  rw [Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ S : EvenAllocation u p,
        hilbertBlock (pairWordEmbedding (C := C) (allocationEquiv h (allocationMap g S))) Q := by
      apply Finset.sum_congr rfl
      intro S _
      rw [hilbertBlock_postcomp _ (pairWordEmbedding (C := C) ((allocationEquiv h S).trans g)) _ Q
        (pairWordEmbedding_reindex (allocationEquiv h S) g).symm]
      apply pairTypeBlock_allocation
      intro i
      exact allocationMap_mem g S (allocationEquiv_left_mem h S i)
    _ = _ := by
      simpa only [Q] using (allocationMap (u := u) g).sum_comp
        (fun S => hilbertBlock (pairWordEmbedding (C := C) (allocationEquiv h S)) Q)

theorem pairTypeProjection_perm_commute {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) (g : SymmetricGroup p) :
    pairTypeProjection h α β C * wordRepresentation p (C ⊕ C) g =
      wordRepresentation p (C ⊕ C) g * pairTypeProjection h α β C := by
  have hg := pairTypeProjection_permute_conj (C := C) h α β g
  have hU : (wordRepresentation p (C ⊕ C) g).adjoint * wordRepresentation p (C ⊕ C) g = 1 := by
    rw [unitary_representation_adjoint _ (fun g x => wordRepresentation_norm g x),
      ← map_mul, inv_mul_cancel, map_one]
  have hh := congrArg (fun T => T * wordRepresentation p (C ⊕ C) g) hg
  rw [mul_assoc, mul_assoc, hU, mul_one] at hh
  exact hh.symm

lemma pairWordEmbedding_off {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (S : EvenAllocation u p) (x : WordSpace u C ⊗[ℂ] WordSpace v C)
    (w : Fin p → C ⊕ C) (hw : wordEvenSites w ≠ S.1) :
    pairWordEmbedding (allocationEquiv h S) x w = 0 := by
  apply euclideanEmbeddingLinear_off
  exact fun he => hw ((pairColorEmbedding_range h S w).mp he)

lemma pairWordEmbedding_adjoint_off {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (S : EvenAllocation u p)
    (w : Fin p → C ⊕ C) (hw : wordEvenSites w ≠ S.1) :
    (pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap.adjoint
      (EuclideanSpace.single w 1) = 0 := by
  apply ext_inner_left ℂ
  intro x
  rw [LinearMap.adjoint_inner_right, inner_zero_right, EuclideanSpace.inner_single_right]
  change 1 * starRingEnd ℂ (pairWordEmbedding (allocationEquiv h S) x w) = 0
  rw [pairWordEmbedding_off h S x w hw, map_zero, mul_zero]

lemma pairTypeProjection_parity_off {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v)
    (w z : Fin p → C ⊕ C) (hwz : wordEvenSites w ≠ wordEvenSites z) :
    wordMatrixEquiv p (C ⊕ C) (pairTypeProjection h α β C) w z = 0 := by
  simp only [wordMatrixEquiv, LinearMap.toMatrixOrthonormal_apply_apply,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
  unfold pairTypeProjection
  simp only [LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro S _
  rw [hilbertBlock_apply]
  by_cases hw : wordEvenSites w = S.1
  · have hz : wordEvenSites z ≠ S.1 := fun hz => hwz (hw.trans hz.symm)
    rw [pairWordEmbedding_adjoint_off h S z hz, map_zero, map_zero]
    rfl
  · exact pairWordEmbedding_off h S _ w hw

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SignedPair
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) signedPairWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) signedPairSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

def wordPhaseDiagonal {p : ℕ} {C : Type*} [Fintype C] (g : SymmetricGroup p) :
    WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C) where
  toFun f := WithLp.toLp 2 (fun w => wordPhase g w * f w)
  map_add' f h := by ext w; exact mul_add _ _ _
  map_smul' c f := by ext w; exact mul_left_comm _ _ _

lemma signedWordRepresentation_eq {p : ℕ} {C : Type*} [Fintype C] (g : SymmetricGroup p) :
    signedWordRepresentation p C g = wordPhaseDiagonal g * wordRepresentation p (C ⊕ C) g := rfl

lemma wordPhaseDiagonal_matrix {p : ℕ} {C : Type*} [Fintype C] (g : SymmetricGroup p) :
    wordMatrixEquiv p (C ⊕ C) (wordPhaseDiagonal g) = Matrix.diagonal (wordPhase g) := by
  ext w z
  simp only [wordMatrixEquiv, LinearMap.toMatrixOrthonormal_apply_apply,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
  change wordPhase g w * (EuclideanSpace.single z (1 : ℂ)) w = _
  simp only [PiLp.single_apply, Matrix.diagonal_apply]
  split_ifs with hw
  · subst z; simp
  · simp

lemma pairTypeProjection_phase_commute {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) (g : SymmetricGroup p) :
    pairTypeProjection h α β C * wordPhaseDiagonal g =
      wordPhaseDiagonal g * pairTypeProjection h α β C := by
  apply (wordMatrixEquiv p (C ⊕ C)).injective
  change wordMatrixEquiv p (C ⊕ C) (_ * _) = wordMatrixEquiv p (C ⊕ C) (_ * _)
  rw [map_mul, map_mul, wordPhaseDiagonal_matrix]
  ext w z
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hp : wordEvenSites w = wordEvenSites z
  · rw [wordPhase_eq_of_parity g w z hp, mul_comm]
  · rw [pairTypeProjection_parity_off h α β w z hp, zero_mul, mul_zero]

theorem pairTypeProjection_signed_commute_oai {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) (g : SymmetricGroup p) :
    pairTypeProjection h α β C * signedWordRepresentation p C g =
      signedWordRepresentation p C g * pairTypeProjection h α β C := by
  rw [signedWordRepresentation_eq, ← mul_assoc,
    pairTypeProjection_phase_commute h α β g, mul_assoc,
    pairTypeProjection_perm_commute h α β g, ← mul_assoc]

end SignedSweeps
end

end OAI
end

theorem solution : type_of% @OAI.SignedSweeps.pairTypeProjection_signed_commute_oai := @OAI.SignedSweeps.pairTypeProjection_signed_commute_oai
