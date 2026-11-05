-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.exists_unital_completelyPositive_extension
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:44:28.754299+00:00
-- url     : https://prove2.me/submissions/d783ab0e-a281-4366-ae04-9af6ab8cc24d

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M]

def matrixScalarHom (k : ℕ) : M →⋆ₐ[ℂ] CStarMatrix (Fin k) (Fin k) M where
  toFun a := CStarMatrix.ofMatrix (Matrix.scalar (Fin k) a)
  map_zero' := (Matrix.scalar (Fin k)).map_zero
  map_one' := (Matrix.scalar (Fin k)).map_one
  map_add' a b := (Matrix.scalar (Fin k)).map_add a b
  map_mul' a b := (Matrix.scalar (Fin k)).map_mul a b
  commutes' _ := rfl
  map_star' a := by
    ext i j
    change (if i = j then star a else 0) = star (if j = i then a else 0)
    by_cases h : i = j
    · simp only [h, ite_true]
    · simp only [h, Ne.symm h, ite_false, star_zero]

@[simp] lemma matrixScalarHom_apply (k : ℕ) (a : M) (i j : Fin k) :
    matrixScalarHom k a i j = if i = j then a else 0 := rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace Generator

namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_weak_vector_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (v : ι → H) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C) :
    ∃ z : H, ‖z‖ ≤ C ∧ ∀ y : H,
      Tendsto (fun i => inner ℂ y (v i)) (ω : Filter ι) (𝓝 (inner ℂ y z)) := by
  let f : ι → WeakDual ℂ H := fun i =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H (v i))
  obtain ⟨d, hd, ht⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ H) C).ultrafilter_le_nhds
    (ω.map f) (by
      apply le_principal_iff.mpr
      change ∀ᶠ i in (ω : Filter ι), f i ∈ _
      exact Eventually.of_forall fun i => by
        simpa [f, Metric.mem_closedBall, dist_zero_right] using hv i)
  let z := (InnerProductSpace.toDual ℂ H).symm (WeakDual.toStrongDual d)
  refine ⟨z, ?_, ?_⟩
  · have hd' : ‖WeakDual.toStrongDual d‖ ≤ C := by
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hd
    simpa only [z, LinearIsometryEquiv.norm_map] using hd'
  · intro y
    have he : Tendsto (fun i => inner ℂ (v i) y) (ω : Filter ι)
        (𝓝 (inner ℂ z y)) := by
      have h := (WeakBilin.eval_continuous _ y).continuousAt.tendsto.comp ht
      change Tendsto (fun i => inner ℂ (v i) y) (ω : Filter ι) (𝓝 (d y)) at h
      rw [show inner ℂ z y = d y from InnerProductSpace.toDual_symm_apply]
      exact h
    have hs := he.star
    change Tendsto (fun i => (starRingEnd ℂ) (inner ℂ (v i) y)) (ω : Filter ι)
      (𝓝 ((starRingEnd ℂ) (inner ℂ z y))) at hs
    simpa only [inner_conj_symm] using hs

theorem exists_weak_operator_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (a : ι → H →L[ℂ] H) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    ∃ T : H →L[ℂ] H, ‖T‖ ≤ C ∧ ∀ x y : H,
      Tendsto (fun i => inner ℂ y (a i x)) (ω : Filter ι) (𝓝 (inner ℂ y (T x))) := by
  have h (x : H) := exists_weak_vector_ultralimit ω (fun i => a i x) (C * ‖x‖)
    (fun i => (a i).le_of_opNorm_le (ha i) x)
  choose v hv ht using h
  have hadd (x z : H) : v (x+z) = v x + v z := by
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (x+z) y)
    simpa only [map_add, inner_add_right] using (ht x y).add (ht z y)
  have hsmul (c : ℂ) (x : H) : v (c • x) = c • v x := by
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (c • x) y)
    simpa only [map_smul, inner_smul_right] using (ht x y).const_mul c
  let T : H →L[ℂ] H := LinearMap.mkContinuous
    { toFun := v, map_add' := hadd, map_smul' := hsmul } C hv
  exact ⟨T, T.opNorm_le_bound hC hv, ht⟩
end Tracial
end Generator
end
end OAI
end

section
namespace OAI

noncomputable section

universe u v w
namespace NaimarkZFC

section HNNWords

namespace HNNWord
variable {A B : Type*} [Mul B]

end HNNWord

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  (φ : A →⋆ₐ[ℂ] B) (v : Bool → B) (K : Bool → A → Prop)

variable (center r : Bool → A → A)
  (hc : ∀ i a, K i (center i a))
  (hr : ∀ i a, v i*φ a*v (!i) = v i*φ (center i a)*v (!i) + φ (r i a))
include hc hr

end HNNWords

section GNS

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def gnsVector (f : A →ₚ[ℂ] ℂ) : f.GNS := (f.toPreGNS 1 : f.GNS)

@[simp] theorem gns_apply_vector (f : A →ₚ[ℂ] ℂ) (a : A) :
    f.gnsStarAlgHom a (gnsVector f) = (f.toPreGNS a : f.GNS) := by
  simp [gnsVector]

@[simp] theorem gnsVector_coefficient (f : A →ₚ[ℂ] ℂ) (a : A) :
    ⟪gnsVector f, f.gnsStarAlgHom a (gnsVector f)⟫_ℂ = f a := by
  simp [gnsVector, Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]

@[simp] theorem gnsVector_norm_sq (f : A →ₚ[ℂ] ℂ) :
    ‖gnsVector f‖ ^ 2 = (f 1).re := by
  simp only [gnsVector, Completion.norm_coe,
    PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS,
    star_one, one_mul]
  exact Real.sq_sqrt (f.map_nonneg (show (0 : A) ≤ 1 from zero_le_one)).1
end GNS
end NaimarkZFC
end
end OAI
end

section
namespace OAI

noncomputable section

namespace NaimarkZFC

variable {A : Type*} [CStarAlgebra A] (e : A) (he : IsStarProjection e)

open scoped ComplexOrder InnerProductSpace
open UniformSpace
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def selfAdjointComplexify (g : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := (g (realPart a) : ℂ) + Complex.I * (g (imaginaryPart a) : ℂ)
  map_add' a b := by simp only [map_add, Complex.ofReal_add, mul_add]; ring
  map_smul' z a := by
    simp only [realPart_smul, imaginaryPart_smul, map_sub, map_add, map_smul,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul]
    apply Complex.ext <;> simp

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem selfAdjointComplexify_coe (g : selfAdjoint A →ₗ[ℝ] ℝ) (a : selfAdjoint A) :
    selfAdjointComplexify g (a : A) = (g a : ℂ) := by
  simp [selfAdjointComplexify]
end NaimarkZFC
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder ComplexStarModule

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def operatorSystemRealPart (S : Submodule ℂ A) : Submodule ℝ A :=
  S.restrictScalars ℝ ⊓ selfAdjoint.submodule ℝ A

def operatorSystemRealInclusion (S : Submodule ℂ A) :
    operatorSystemRealPart S →ₗ[ℝ] S where
  toFun x := ⟨x.val, x.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma positive_subspace_selfAdjoint_im (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (f : S →ₗ[ℂ] ℂ) (hf : ∀ a : S, 0 ≤ (a : A) → 0 ≤ f a)
    (a : S) (ha : IsSelfAdjoint (a : A)) : (f a).im = 0 := by
  let e : S := ⟨1, h1⟩
  have he : (f e).im = 0 := (hf e zero_le_one).2.symm
  have hb : 0 ≤ ‖a‖ • (1 : A) + (a : A) := by
    change 0 ≤ ‖(a : A)‖ • (1 : A) + (a : A)
    have h := ha.neg_algebraMap_norm_le_self
    simpa only [Algebra.algebraMap_eq_smul_one, neg_le_iff_add_nonneg, add_comm] using h
  have h := (hf ((‖a‖ : ℂ) • e + a) (by
    change 0 ≤ (‖a‖ : ℂ) • (1 : A) + (a : A)
    rw [Complex.coe_smul]
    exact hb)).2
  simpa only [map_add, map_smul, smul_eq_mul, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, he, mul_zero, zero_mul, zero_add,
    Complex.zero_im] using h.symm

lemma positive_subspace_real_bound (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (f : S →ₗ[ℂ] ℂ) (hf : ∀ a : S, 0 ≤ (a : A) → 0 ≤ f a)
    (a : S) (ha : IsSelfAdjoint (a : A)) :
    |(f a).re| ≤ (f ⟨1, h1⟩).re * ‖a‖ := by
  let e : S := ⟨1, h1⟩
  have hup : 0 ≤ ‖a‖ • (1 : A) - (a : A) := by
    apply sub_nonneg.mpr
    change (a : A) ≤ ‖(a : A)‖ • (1 : A)
    simpa only [Algebra.algebraMap_eq_smul_one] using ha.le_algebraMap_norm_self
  have hlo : 0 ≤ ‖a‖ • (1 : A) + (a : A) := by
    change 0 ≤ ‖(a : A)‖ • (1 : A) + (a : A)
    simpa only [Algebra.algebraMap_eq_smul_one, neg_le_iff_add_nonneg, add_comm]
      using ha.neg_algebraMap_norm_le_self
  have hp := (hf ((‖a‖ : ℂ) • e - a) (by
    change 0 ≤ (‖a‖ : ℂ) • (1 : A) - (a : A)
    rw [Complex.coe_smul]
    exact hup)).1
  have hm := (hf ((‖a‖ : ℂ) • e + a) (by
    change 0 ≤ (‖a‖ : ℂ) • (1 : A) + (a : A)
    rw [Complex.coe_smul]
    exact hlo)).1
  simp only [map_sub, map_add, map_smul, smul_eq_mul, Complex.sub_re, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.zero_re] at hp hm
  change 0 ≤ ‖a‖ * (f ⟨1, h1⟩).re - (f a).re at hp
  change 0 ≤ ‖a‖ * (f ⟨1, h1⟩).re + (f a).re at hm
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

def operatorSystemRealFunctional (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (f : S →ₗ[ℂ] ℂ) (hf : ∀ a : S, 0 ≤ (a : A) → 0 ≤ f a) :
    operatorSystemRealPart S →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    (Complex.reLm.comp ((f.restrictScalars ℝ).comp (operatorSystemRealInclusion S)))
    (f ⟨1, h1⟩).re (fun a =>
      positive_subspace_real_bound S h1 f hf (operatorSystemRealInclusion S a) a.property.2)

lemma selfAdjoint_nonneg_of_norm_le (g : selfAdjoint A →L[ℝ] ℝ) (c : ℝ)
    (hg : ‖g‖ ≤ c) (h1 : g 1 = c) (a : selfAdjoint A) (ha : 0 ≤ (a : A)) :
    0 ≤ g a := by
  have hau : (a : A) ≤ ‖a‖ • (1 : A) := by
    change (a : A) ≤ ‖(a : A)‖ • (1 : A)
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (CStarAlgebra.norm_le_iff_le_algebraMap (a : A) (norm_nonneg _) ha).mp le_rfl
  have hpos : 0 ≤ ‖a‖ • (1 : A) - (a : A) := sub_nonneg.mpr hau
  have hn : ‖‖a‖ • (1 : selfAdjoint A) - a‖ ≤ ‖a‖ := by
    change ‖‖a‖ • (1 : A) - (a : A)‖ ≤ ‖a‖
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (norm_nonneg _) hpos).mpr
    simpa only [Algebra.algebraMap_eq_smul_one] using sub_le_self (‖a‖ • (1 : A)) ha
  have hc : ‖g (‖a‖ • (1 : selfAdjoint A) - a)‖ ≤ c * ‖a‖ :=
    (g.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hg (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hn ((norm_nonneg g).trans hg)))
  rw [map_sub, map_smul, h1, smul_eq_mul, Real.norm_eq_abs] at hc
  have h := (le_abs_self _).trans hc
  nlinarith
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder ComplexStarModule

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_positive_operatorSystem_extension
    (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (hstar : ∀ a ∈ S, star a ∈ S) (f : S →ₗ[ℂ] ℂ)
    (hf : ∀ a : S, 0 ≤ (a : A) → 0 ≤ f a) :
    ∃ F : A →ₚ[ℂ] ℂ, ∀ a : S, F (a : A) = f a := by
  let c := (f ⟨1, h1⟩).re
  have hc : 0 ≤ c := (hf ⟨1, h1⟩ zero_le_one).1
  let g := operatorSystemRealFunctional S h1 f hf
  have hg : ‖g‖ ≤ c := by
    apply g.opNorm_le_bound hc
    intro a
    exact positive_subspace_real_bound S h1 f hf (operatorSystemRealInclusion S a)
      a.property.2
  obtain ⟨G₀, hG₀, hnG₀⟩ := exists_extension_norm_eq (operatorSystemRealPart S) g
  let sa : selfAdjoint A →L[ℝ] A :=
    ((selfAdjoint.submodule ℝ A).subtype).mkContinuous 1 (fun a => by simp)
  let G := G₀.comp sa
  have hGn : ‖G‖ ≤ c := by
    apply G.opNorm_le_bound hc
    intro a
    exact (G₀.le_opNorm (sa a)).trans
      (mul_le_mul_of_nonneg_right (hnG₀.trans_le hg) (norm_nonneg a))
  have hG1 : G 1 = c := by
    exact hG₀ ⟨1, h1, IsSelfAdjoint.one A⟩
  let F : A →ₚ[ℂ] ℂ :=
    PositiveLinearMap.mk₀ (NaimarkZFC.selfAdjointComplexify G.toLinearMap) (fun a ha => by
      let x : selfAdjoint A := ⟨a, ha.isSelfAdjoint⟩
      change 0 ≤ NaimarkZFC.selfAdjointComplexify G.toLinearMap (x : A)
      rw [NaimarkZFC.selfAdjointComplexify_coe]
      exact ⟨selfAdjoint_nonneg_of_norm_le G c hGn hG1 x ha, by simp⟩)
  have hsa (a : S) (ha : IsSelfAdjoint (a : A)) : F (a : A) = f a := by
    let b : operatorSystemRealPart S := ⟨a, a.property, ha⟩
    let x : selfAdjoint A := ⟨a, ha⟩
    change NaimarkZFC.selfAdjointComplexify G.toLinearMap (x : A) = f a
    rw [NaimarkZFC.selfAdjointComplexify_coe]
    change (G₀ b : ℂ) = f a
    rw [hG₀ b]
    change ((f a).re : ℂ) = f a
    apply Complex.ext
    · simp
    · simpa using (positive_subspace_selfAdjoint_im S h1 f hf a ha).symm
  refine ⟨F, fun a => ?_⟩
  have hr : (realPart (a : A) : A) ∈ S := by
    rw [realPart_apply_coe, ← Complex.coe_smul]
    exact S.smul_mem _ (S.add_mem a.property (hstar a a.property))
  have hi : (imaginaryPart (a : A) : A) ∈ S := by
    rw [imaginaryPart_apply_coe, ← Complex.coe_smul]
    exact S.smul_mem _ (S.smul_mem _ (S.sub_mem a.property (hstar a a.property)))
  let ar : S := ⟨realPart (a : A), hr⟩
  let ai : S := ⟨imaginaryPart (a : A), hi⟩
  have ha : a = ar + Complex.I • ai := by
    apply Subtype.ext
    exact (realPart_add_I_smul_imaginaryPart (a : A)).symm
  rw [ha]
  change F ((ar : A) + Complex.I • (ai : A)) = f (ar + Complex.I • ai)
  simp only [map_add, map_smul]
  rw [hsa ar (realPart (a : A)).property, hsa ai (imaginaryPart (a : A)).property]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace

namespace WeakPureInfiniteness

section MatrixOperators

variable {n H : Type*} [Fintype n]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def matrixOperator (M : CStarMatrix n n (H →L[ℂ] H)) :
    (PiLp 2 (fun _ : n => H)) →L[ℂ] (PiLp 2 (fun _ : n => H)) :=
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => H)
  e.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun i => ∑ j, (M i j).comp (ContinuousLinearMap.proj j)).comp
      e.toContinuousLinearMap)

omit [CompleteSpace H] in
@[simp]

lemma matrixOperator_apply (M : CStarMatrix n n (H →L[ℂ] H))
    (x : PiLp 2 (fun _ : n => H)) (i : n) :
    matrixOperator M x i = ∑ j, M i j (x j) := by
  simp [matrixOperator]

omit [CompleteSpace H] in
lemma matrixOperator_add (M N : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (M + N) = matrixOperator M + matrixOperator N := by
  ext x i
  simp [Finset.sum_add_distrib]

omit [CompleteSpace H] in
lemma matrixOperator_smul (c : ℂ) (M : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (c • M) = c • matrixOperator M := by
  ext x i
  simp [Finset.smul_sum]

omit [CompleteSpace H] in
lemma matrixOperator_zero : matrixOperator (0 : CStarMatrix n n (H →L[ℂ] H)) = 0 := by
  ext x i
  simp

omit [CompleteSpace H] in
lemma matrixOperator_mul (M N : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (M * N) = matrixOperator M * matrixOperator N := by
  ext x i
  simp only [matrixOperator_apply, CStarMatrix.mul_apply, sum_apply,
    mul_apply_eq_comp, map_sum]
  exact Finset.sum_comm

lemma matrixOperator_star (M : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (star M) = star (matrixOperator M) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [PiLp.inner_apply, matrixOperator_apply, sum_inner, inner_sum,
    CStarMatrix.star_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]
  exact Finset.sum_comm

noncomputable def matrixOperatorHom : CStarMatrix n n (H →L[ℂ] H) →⋆ₙₐ[ℂ]
    ((PiLp 2 (fun _ : n => H)) →L[ℂ] (PiLp 2 (fun _ : n => H))) where
  toFun := matrixOperator
  map_zero' := matrixOperator_zero
  map_add' := matrixOperator_add
  map_smul' := matrixOperator_smul
  map_mul' := matrixOperator_mul
  map_star' := matrixOperator_star

omit [CompleteSpace H] in
lemma matrixOperator_single [DecidableEq n] (M : CStarMatrix n n (H →L[ℂ] H)) (i j : n) (x : H) :
    matrixOperator M (PiLp.single 2 j x) i = M i j x := by
  simp [PiLp.single_apply, apply_ite]

omit [CompleteSpace H] in
lemma matrixOperator_injective : Function.Injective (matrixOperator (n := n) (H := H)) := by
  classical
  intro M N h
  ext i j x
  have he := congrArg (fun T => T (PiLp.single 2 j x) i) h
  simpa only [matrixOperator_single] using he
end MatrixOperators
end WeakPureInfiniteness
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype I]

def algebraGram (a : I → M) : CStarMatrix I I M := fun i j => star (a i) * a j

lemma algebraGram_nonneg (a : I → M) : 0 ≤ algebraGram a := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h =>
    have hz : algebraGram a = 0 := by ext i; exact isEmptyElim i
    rw [hz]
  | inr h =>
    let i₀ : I := Classical.choice h
    let R : CStarMatrix I I M := fun i j => if i = i₀ then a j else 0
    have heq : star R * R = algebraGram a := by
      ext i j
      change (∑ k, star (if k = i₀ then a i else 0) *
        (if k = i₀ then a j else 0)) = star (a i) * a j
      simp
    rw [← heq]
    exact star_mul_self_nonneg R

lemma weighted_algebraGram_nonneg (a : I → M) (q : M) (hq : 0 ≤ q) :
    0 ≤ CStarMatrix.ofMatrix (fun i j => star (a i) * q * a j) := by
  have hs : star (CFC.sqrt q) * CFC.sqrt q = q := by
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg q)).star_eq]
    exact CFC.sqrt_mul_sqrt_self q hq
  have heq : algebraGram (fun i => CFC.sqrt q * a i) =
      CStarMatrix.ofMatrix (fun i j => star (a i) * q * a j) := by
    ext i j
    change star (CFC.sqrt q * a i) * (CFC.sqrt q * a j) = _
    rw [star_mul]
    calc
      _ = star (a i) * (star (CFC.sqrt q) * CFC.sqrt q) * a j := by
        simp only [mul_assoc]
      _ = _ := by rw [hs]; rfl
  rw [← heq]
  exact algebraGram_nonneg (fun i : I => CFC.sqrt q * a i)

lemma algebraGram_left_le (a : I → M) (b : M) :
    algebraGram (fun i => b * a i) ≤ ‖b‖ ^ 2 • algebraGram a := by
  have hb : star b * b ≤ ‖b‖ ^ 2 • (1 : M) := by
    simpa only [star_one, one_mul, mul_one, CStarRing.norm_star_mul_self, pow_two]
      using CStarAlgebra.star_left_conjugate_le_norm_smul (a := (1 : M)) (b := star b * b)
  have hq := weighted_algebraGram_nonneg a (‖b‖ ^ 2 • (1 : M) - star b * b)
    (sub_nonneg.mpr hb)
  have heq : CStarMatrix.ofMatrix (fun i j => star (a i) * (‖b‖ ^ 2 • (1 : M) - star b * b) * a j) = ‖b‖ ^ 2 • algebraGram a - algebraGram (fun i => b * a i) := by
    ext i j
    change star (a i) * (‖b‖ ^ 2 • (1 : M) - star b * b) * a j =
      ‖b‖ ^ 2 • (star (a i) * a j) - star (b * a i) * (b * a j)
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, star_mul, mul_assoc]
  rw [heq] at hq
  exact sub_nonneg.mp hq

lemma operatorMatrix_quadratic_nonneg
    (A : CStarMatrix I I (H →L[ℂ] H)) (hA : 0 ≤ A) (ξ : I → H) :
    0 ≤ ∑ i, ∑ j, inner ℂ (ξ i) (A i j (ξ j)) := by
  have h := map_nonneg (WeakPureInfiniteness.matrixOperatorHom (n := I) (H := H)) hA
  have hi := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp h).inner_nonneg_right
    (WithLp.toLp 2 ξ)
  change 0 ≤ inner ℂ (WithLp.toLp 2 ξ)
    (WeakPureInfiniteness.matrixOperator A (WithLp.toLp 2 ξ)) at hi
  simpa only [PiLp.inner_apply, WeakPureInfiniteness.matrixOperator_apply,
    PiLp.toLp_apply, inner_sum] using hi

lemma completelyPositive_kernel_nonneg
    (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : I → M) (ξ : I → H) :
    0 ≤ ∑ i, ∑ j, inner ℂ (ξ i) (φ (star (a i) * a j) (ξ j)) := by
  exact operatorMatrix_quadratic_nonneg _
    (φ.map_cstarMatrix_nonneg (algebraGram a) (algebraGram_nonneg a)) ξ
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {I : Type*}

def kernelForm (K : Matrix I I ℂ) (x y : I →₀ ℂ) : ℂ :=
  x.sum fun i a => y.sum fun j b => star a * K i j * b

lemma kernelForm_conj_symm (K : Matrix I I ℂ) (hK : K.IsHermitian) (x y : I →₀ ℂ) :
    star (kernelForm K y x) = kernelForm K x y := by
  classical
  simp only [kernelForm, Finsupp.sum, star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hK.apply i j]
  ring

lemma kernelForm_add_left (K : Matrix I I ℂ) (x y z : I →₀ ℂ) :
    kernelForm K (x + y) z = kernelForm K x z + kernelForm K y z := by
  classical
  unfold kernelForm
  apply Finsupp.sum_add_index'
  · intro i
    simp
  · intro i a b
    simp only [star_add, add_mul, Finsupp.sum, Finset.sum_add_distrib]

lemma kernelForm_smul_left (K : Matrix I I ℂ) (x y : I →₀ ℂ) (r : ℂ) :
    kernelForm K (r • x) y = star r * kernelForm K x y := by
  classical
  unfold kernelForm
  rw [Finsupp.sum_smul_index (by intro i; simp)]
  simp only [star_mul, mul_assoc, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma kernelForm_nonneg (K : Matrix I I ℂ) (hK : K.PosSemidef) (x : I →₀ ℂ) :
    0 ≤ kernelForm K x x := hK.2 x

def PositiveKernelPreSpace (K : Matrix I I ℂ) (_hK : K.PosSemidef) : Type _ := I →₀ ℂ

instance kernelPreAddCommGroup (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    AddCommGroup (PositiveKernelPreSpace K hK) := inferInstanceAs (AddCommGroup (I →₀ ℂ))

instance kernelPreModule (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    Module ℂ (PositiveKernelPreSpace K hK) := inferInstanceAs (Module ℂ (I →₀ ℂ))

abbrev positiveKernelCore (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    PreInnerProductSpace.Core ℂ (PositiveKernelPreSpace K hK) where
  inner := kernelForm K
  conj_inner_symm x y := kernelForm_conj_symm K hK.1 x y
  re_inner_nonneg x := (kernelForm_nonneg K hK x).1
  add_left := kernelForm_add_left K
  smul_left := kernelForm_smul_left K

instance kernelPreSeminormedAddCommGroup (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    SeminormedAddCommGroup (PositiveKernelPreSpace K hK) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := positiveKernelCore K hK)

instance kernelPreInnerProductSpace (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    InnerProductSpace ℂ (PositiveKernelPreSpace K hK) :=
  InnerProductSpace.ofCore (positiveKernelCore K hK)

abbrev PositiveKernelHilbert (K : Matrix I I ℂ) (hK : K.PosSemidef) :=
  UniformSpace.Completion (PositiveKernelPreSpace K hK)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma completelyPositive_star (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : M) :
    φ (star a) = star (φ a) := by
  obtain ⟨x, hx, _, rfl⟩ := CStarAlgebra.exists_sum_four_nonneg a
  have hxstar (i : Fin 4) : star (x i) = x i := (IsSelfAdjoint.of_nonneg (hx i)).star_eq
  have hystar (i : Fin 4) : star (φ (x i)) = φ (x i) :=
    (IsSelfAdjoint.of_nonneg (map_nonneg φ (hx i))).star_eq
  simp only [star_sum, star_smul, map_sum, map_smul, hxstar, hystar]

def stinespringKernel (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    Matrix (M × H) (M × H) ℂ :=
  fun p q => inner ℂ p.2 (φ (star p.1 * q.1) q.2)

lemma stinespringKernel_hermitian (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    (stinespringKernel φ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  change star (inner ℂ q.2 (φ (star q.1 * p.1) p.2)) =
    inner ℂ p.2 (φ (star p.1 * q.1) q.2)
  rw [← starRingEnd_apply, inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right]
  rw [← ContinuousLinearMap.star_eq_adjoint, ← completelyPositive_star]
  simp only [star_mul, star_star]

lemma kernelForm_coefficients {J : Type*}
    (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : J → M) (ξ : J → H) (x : J →₀ ℂ) :
    kernelForm (fun i j => inner ℂ (ξ i) (φ (star (a i) * a j) (ξ j))) x x =
      ∑ i : x.support, ∑ j : x.support,
        inner ℂ (x i • ξ i) (φ (star (a i) * a j) (x j • ξ j)) := by
  classical
  unfold kernelForm
  rw [Finsupp.sum, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finsupp.sum, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [inner_smul_left, map_smul, inner_smul_right, starRingEnd_apply]
  ring

theorem stinespringKernel_positive (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    (stinespringKernel φ).PosSemidef := by
  classical
  refine ⟨stinespringKernel_hermitian φ, ?_⟩
  intro x
  change 0 ≤ kernelForm (fun p q : M × H =>
    inner ℂ p.2 (φ (star p.1 * q.1) q.2)) x x
  rw [kernelForm_coefficients]
  exact completelyPositive_kernel_nonneg φ
    (fun i : x.support => i.val.1) (fun i : x.support => x i • i.val.2)

abbrev StinespringSpace (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :=
  PositiveKernelHilbert (stinespringKernel φ) (stinespringKernel_positive φ)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype I]

def operatorMatrixVectorFunctional (ξ : I → H) :
    CStarMatrix I I (H →L[ℂ] H) →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun A := ∑ i, ∑ j, inner ℂ (ξ i) (A i j (ξ j))
      map_add' A B := by
        simp only [CStarMatrix.add_apply, add_apply,
          inner_add_right, Finset.sum_add_distrib]
      map_smul' z A := by
        simp only [CStarMatrix.smul_apply, smul_apply,
          inner_smul_right, smul_eq_mul, Finset.mul_sum, RingHom.id_apply] }
    (fun A hA => operatorMatrix_quadratic_nonneg A hA ξ)

def cpMatrixVectorFunctional (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : I → H) :
    CStarMatrix I I M →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    ((operatorMatrixVectorFunctional ξ).toLinearMap.comp (CStarMatrix.mapₗ φ.toLinearMap))
    (fun A hA => operatorMatrix_quadratic_nonneg _ (φ.map_cstarMatrix_nonneg A hA) ξ)

lemma completelyPositive_kernel_left_bound
    (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : I → M) (ξ : I → H) (b : M) :
    (∑ i, ∑ j, inner ℂ (ξ i) (φ (star (b * a i) * (b * a j)) (ξ j))).re ≤
      ‖b‖ ^ 2 * (∑ i, ∑ j, inner ℂ (ξ i) (φ (star (a i) * a j) (ξ j))).re := by
  have h := (cpMatrixVectorFunctional φ ξ).monotone (algebraGram_left_le a b)
  change cpMatrixVectorFunctional φ ξ (algebraGram (fun i => b * a i)) ≤
    cpMatrixVectorFunctional φ ξ (‖b‖ ^ 2 • algebraGram a) at h
  rw [PositiveLinearMap.map_smul_of_tower] at h
  have hr := h.1
  rw [← Complex.coe_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hr
  exact hr
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
lemma operatorSystemMatrices_one (S : Submodule ℂ A) (h1 : (1 : A) ∈ S) (n : ℕ) :
    (1 : CStarMatrix (Fin n) (Fin n) A) ∈ operatorSystemMatrices S n := by
  intro i j
  change (if i = j then (1 : A) else 0) ∈ S
  split_ifs
  · exact h1
  · exact S.zero_mem

omit [PartialOrder A] [StarOrderedRing A] in
lemma operatorSystemMatrices_star (S : Submodule ℂ A)
    (hs : ∀ a ∈ S, star a ∈ S) (n : ℕ)
    (X : CStarMatrix (Fin n) (Fin n) A) (hX : X ∈ operatorSystemMatrices S n) :
    star X ∈ operatorSystemMatrices S n := fun i j => hs _ (hX j i)

def operatorSystemMatrixFunctional (S : Submodule ℂ A) (φ : S →ₗ[ℂ] (H →L[ℂ] H))
    {n : ℕ} (ξ : Fin n → H) : operatorSystemMatrices S n →ₗ[ℂ] ℂ :=
  (operatorMatrixVectorFunctional ξ).toLinearMap.comp (operatorSystemAmplification S φ n)

lemma operatorSystemMatrixFunctional_nonneg
    (S : Submodule ℂ A) (φ : S →ₗ[ℂ] (H →L[ℂ] H)) {n : ℕ} (ξ : Fin n → H)
    (hφ : ∀ X : operatorSystemMatrices S n,
      0 ≤ (X : CStarMatrix (Fin n) (Fin n) A) →
        0 ≤ operatorSystemAmplification S φ n X)
    (X : operatorSystemMatrices S n) (hX : 0 ≤ (X : CStarMatrix (Fin n) (Fin n) A)) :
    0 ≤ operatorSystemMatrixFunctional S φ ξ X :=
  (operatorMatrixVectorFunctional ξ).map_nonneg (hφ X hX)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H K I : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [Fintype I]

lemma operatorMatrix_nonneg_of_quadratic
    (B : CStarMatrix I I (H →L[ℂ] H))
    (hB : ∀ ξ : I → H, 0 ≤ ∑ i, ∑ j, inner ℂ (ξ i) (B i j (ξ j))) : 0 ≤ B := by
  let ρ := WeakPureInfiniteness.matrixOperatorHom (n := I) (H := H)
  apply (Compat.map_le_map_iff ρ
    WeakPureInfiniteness.matrixOperator_injective).mp
  rw [map_zero, ContinuousLinearMap.nonneg_iff_isPositive,
    ContinuousLinearMap.isPositive_iff_complex]
  intro ξ
  have hp : 0 ≤ inner ℂ ξ (ρ B ξ) := by
    change 0 ≤ inner ℂ ξ (WeakPureInfiniteness.matrixOperator B ξ)
    simpa only [WeakPureInfiniteness.matrixOperator_apply, PiLp.inner_apply, inner_sum]
      using hB ξ
  have hq : 0 ≤ inner ℂ (ρ B ξ) ξ := by
    rw [← inner_conj_symm (𝕜 := ℂ) (ρ B ξ) ξ]
    exact star_nonneg_iff.mpr hp
  exact ⟨Complex.ext (by simp) hq.2, hq.1⟩

def compressCompletelyPositive (φ : CompletelyPositiveMap A (K →L[ℂ] K))
    (V : H →L[ℂ] K) : CompletelyPositiveMap A (H →L[ℂ] H) where
  toFun a := V.adjoint.comp ((φ a).comp V)
  map_add' a b := by ext ξ; simp
  map_smul' z a := by ext ξ; simp
  map_cstarMatrix_nonneg' n B hB := by
    apply operatorMatrix_nonneg_of_quadratic
    intro ξ
    change 0 ≤ ∑ i, ∑ j, inner ℂ (ξ i) (V.adjoint (φ (B i j) (V (ξ j))))
    simp only [ContinuousLinearMap.adjoint_inner_right]
    exact operatorMatrix_quadratic_nonneg (B.map φ) (φ.map_cstarMatrix_nonneg B hB)
      (fun i => V (ξ i))

@[simp] lemma compressCompletelyPositive_apply
    (φ : CompletelyPositiveMap A (K →L[ℂ] K)) (V : H →L[ℂ] K) (a : A) :
    compressCompletelyPositive φ V a = V.adjoint.comp ((φ a).comp V) := rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def singleCStarMatrix {n : ℕ} (i j : Fin n) (a : A) : CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrix (Matrix.single i j a)

omit [PartialOrder A] [StarOrderedRing A] in
lemma singleCStarMatrix_star {n : ℕ} (i j : Fin n) (a : A) :
    star (singleCStarMatrix i j a) = singleCStarMatrix j i (star a) :=
  congrArg CStarMatrix.ofMatrix (Matrix.conjTranspose_single i j a)

omit [PartialOrder A] [StarOrderedRing A] in
lemma singleCStarMatrix_diagonal {n : ℕ} (i₀ i j : Fin n) (a : A) :
    star (singleCStarMatrix i₀ i (1 : A)) *
      (matrixScalarHom n a * singleCStarMatrix i₀ j 1) = singleCStarMatrix i j a := by
  rw [singleCStarMatrix_star, star_one, ← mul_assoc]
  change CStarMatrix.ofMatrix
    (Matrix.single i i₀ 1 * Matrix.scalar (Fin n) a * Matrix.single i₀ j 1) = _
  rw [Matrix.single_mul_mul_single]
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, one_mul, mul_one]
  rfl

def matrixFunctionalVector {n : ℕ} (F : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ)
    (i₀ i : Fin n) : F.GNS :=
  F.gnsStarAlgHom (singleCStarMatrix i₀ i 1) (NaimarkZFC.gnsVector F)

def matrixFunctionalEmbedding {n : ℕ} (F : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ)
    (i₀ : Fin n) : EuclideanSpace ℂ (Fin n) →L[ℂ] F.GNS :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ => ∑ i, ξ i • matrixFunctionalVector F i₀ i
      map_add' := fun ξ η => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun z ξ => by simp [Finset.smul_sum, mul_smul] }

@[simp] lemma matrixFunctionalEmbedding_single {n : ℕ}
    (F : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ) (i₀ i : Fin n) :
    matrixFunctionalEmbedding F i₀ (EuclideanSpace.single i 1) =
      matrixFunctionalVector F i₀ i := by
  change (∑ j, (EuclideanSpace.single i (1 : ℂ)) j • matrixFunctionalVector F i₀ j) = _
  simp [PiLp.single_apply]

def matrixFunctionalCP {n : ℕ} (F : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ)
    (i₀ : Fin n) : CompletelyPositiveMap A
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  compressCompletelyPositive
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
      (F.gnsStarAlgHom.comp (matrixScalarHom n))) (matrixFunctionalEmbedding F i₀)

lemma matrixFunctionalCP_coefficient {n : ℕ}
    (F : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ) (i₀ i j : Fin n) (a : A) :
    inner ℂ (EuclideanSpace.single i 1)
      (matrixFunctionalCP F i₀ a (EuclideanSpace.single j 1)) =
        F (singleCStarMatrix i j a) := by
  change inner ℂ (EuclideanSpace.single i 1)
    ((matrixFunctionalEmbedding F i₀).adjoint
      (F.gnsStarAlgHom (matrixScalarHom n a)
        (matrixFunctionalEmbedding F i₀ (EuclideanSpace.single j 1)))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, matrixFunctionalEmbedding_single,
    matrixFunctionalEmbedding_single]
  unfold matrixFunctionalVector
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    ← map_star]
  change inner ℂ (NaimarkZFC.gnsVector F)
    ((F.gnsStarAlgHom (star (singleCStarMatrix i₀ i 1)) *
      (F.gnsStarAlgHom (matrixScalarHom n a) *
        F.gnsStarAlgHom (singleCStarMatrix i₀ j 1))) (NaimarkZFC.gnsVector F)) = _
  rw [← map_mul, ← map_mul, NaimarkZFC.gnsVector_coefficient,
    singleCStarMatrix_diagonal]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def operatorSystemSingle (S : Submodule ℂ A) {n : ℕ} (i j : Fin n) (a : S) :
    operatorSystemMatrices S n :=
  ⟨singleCStarMatrix i j (a : A), fun p q => by
    change (if i = p ∧ j = q then (a : A) else 0) ∈ S
    split_ifs
    · exact a.property
    · exact S.zero_mem⟩

omit [PartialOrder A] [StarOrderedRing A] in
lemma operatorSystemSingle_amplification (S : Submodule ℂ A) {n : ℕ}
    (φ : S →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
    (i j : Fin n) (a : S) :
    operatorSystemAmplification S φ n (operatorSystemSingle S i j a) =
      singleCStarMatrix i j (φ a) := by
  apply CStarMatrix.ext
  intro p q
  by_cases h : i = p ∧ j = q
  · rcases h with ⟨rfl, rfl⟩
    have he : (⟨(operatorSystemSingle S i j a).val i j,
        (operatorSystemSingle S i j a).property i j⟩ : S) = a :=
      Subtype.ext (Matrix.single_apply_same i j (a : A))
    exact (congrArg φ he).trans (Matrix.single_apply_same i j (φ a)).symm
  · have hz : (operatorSystemSingle S i j a).val p q = 0 := by
      exact ite_eq_right (fun h' => (h h').elim)
    have he : (⟨(operatorSystemSingle S i j a).val p q,
        (operatorSystemSingle S i j a).property p q⟩ : S) = 0 := Subtype.ext hz
    exact (congrArg φ he).trans ((map_zero φ).trans
      (show singleCStarMatrix i j (φ a) p q = 0 from
        ite_eq_right (fun h' => (h h').elim)).symm)

omit [PartialOrder A] [StarOrderedRing A] in
lemma operatorSystemMatrixFunctional_single (S : Submodule ℂ A) {n : ℕ}
    (φ : S →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
    (i j : Fin n) (a : S) :
    operatorSystemMatrixFunctional S φ (fun k => EuclideanSpace.single k 1)
      (operatorSystemSingle S i j a) =
        inner ℂ (EuclideanSpace.single i 1) (φ a (EuclideanSpace.single j 1)) := by
  change operatorMatrixVectorFunctional (fun k => EuclideanSpace.single k 1)
    (operatorSystemAmplification S φ n (operatorSystemSingle S i j a)) = _
  rw [operatorSystemSingle_amplification]
  change (∑ p, ∑ q, inner ℂ (EuclideanSpace.single p 1)
    ((if i = p ∧ j = q then φ a else 0) (EuclideanSpace.single q 1))) = _
  have he (p q : Fin n) : inner ℂ (EuclideanSpace.single p 1)
      ((if i = p ∧ j = q then φ a else 0) (EuclideanSpace.single q 1)) =
      if p = i ∧ q = j then
        inner ℂ (EuclideanSpace.single i 1) (φ a (EuclideanSpace.single j 1)) else 0 := by
    by_cases hp : p = i <;> by_cases hq : q = j
    · subst p; subst q; simp
    · simp [hp, hq, Ne.symm hq]
    · simp [hp, Ne.symm hp]
    · simp [hp, Ne.symm hp]
  simp_rw [he]
  simp [ite_and]

lemma euclideanOperator_ext {n : ℕ}
    (T U : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (h : ∀ i j, inner ℂ (EuclideanSpace.single i 1) (T (EuclideanSpace.single j 1)) =
      inner ℂ (EuclideanSpace.single i 1) (U (EuclideanSpace.single j 1))) : T = U := by
  have he (j : Fin n) : T (EuclideanSpace.single j 1) = U (EuclideanSpace.single j 1) := by
    apply PiLp.ext
    intro i
    have hh := h i j
    simp only [EuclideanSpace.inner_single_left, map_one, one_mul] at hh
    exact hh
  apply ContinuousLinearMap.coe_injective
  apply (PiLp.basisFun 2 ℂ (Fin n)).ext
  intro j
  rw [PiLp.basisFun_apply]
  exact he j

theorem exists_finite_completelyPositive_extension (S : Submodule ℂ A)
    (h1 : (1 : A) ∈ S) (hstar : ∀ a ∈ S, star a ∈ S) {n : ℕ} (i₀ : Fin n)
    (φ : S →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
    (hφ : ∀ X : operatorSystemMatrices S n,
      0 ≤ (X : CStarMatrix (Fin n) (Fin n) A) →
        0 ≤ operatorSystemAmplification S φ n X) :
    ∃ Φ : CompletelyPositiveMap A
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
        ∀ a : S, Φ (a : A) = φ a := by
  let ξ : Fin n → EuclideanSpace ℂ (Fin n) := fun i => EuclideanSpace.single i 1
  obtain ⟨F, hF⟩ := exists_positive_operatorSystem_extension
    (operatorSystemMatrices S n) (operatorSystemMatrices_one S h1 n)
    (operatorSystemMatrices_star S hstar n) (operatorSystemMatrixFunctional S φ ξ)
    (operatorSystemMatrixFunctional_nonneg S φ ξ hφ)
  refine ⟨matrixFunctionalCP F i₀, fun a => euclideanOperator_ext _ _ (fun i j => ?_)⟩
  rw [matrixFunctionalCP_coefficient]
  exact (hF (operatorSystemSingle S i j a)).trans
    (operatorSystemMatrixFunctional_single S φ i j a)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def compressOperatorSystem (S : Submodule ℂ A) (φ : S →ₗ[ℂ] (H →L[ℂ] H))
    (V : K →L[ℂ] H) : S →ₗ[ℂ] (K →L[ℂ] K) where
  toFun a := V.adjoint.comp ((φ a).comp V)
  map_add' a b := by ext ξ; simp
  map_smul' z a := by ext ξ; simp

omit [PartialOrder A] [StarOrderedRing A] in
lemma compressOperatorSystem_positive (S : Submodule ℂ A)
    (φ : S →ₗ[ℂ] (H →L[ℂ] H)) (V : K →L[ℂ] H) {n : ℕ}
    (X : operatorSystemMatrices S n) (hX : 0 ≤ operatorSystemAmplification S φ n X) :
    0 ≤ operatorSystemAmplification S (compressOperatorSystem S φ V) n X := by
  apply operatorMatrix_nonneg_of_quadratic
  intro ξ
  change 0 ≤ ∑ i, ∑ j, inner ℂ (ξ i)
    (V.adjoint (φ ⟨X.val i j, X.property i j⟩ (V (ξ j))))
  simp only [ContinuousLinearMap.adjoint_inner_right]
  exact operatorMatrix_quadratic_nonneg (operatorSystemAmplification S φ n X) hX
    (fun i => V (ξ i))

omit [PartialOrder A] [StarOrderedRing A] in
lemma compressOperatorSystem_one (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (φ : S →ₗ[ℂ] (H →L[ℂ] H)) (hφ : φ ⟨1, h1⟩ = 1) (V : K →ₗᵢ[ℂ] H) :
    compressOperatorSystem S φ V.toContinuousLinearMap ⟨1, h1⟩ = 1 := by
  change V.toContinuousLinearMap.adjoint.comp ((φ ⟨1, h1⟩).comp V.toContinuousLinearMap) = 1
  rw [hφ]
  change V.toContinuousLinearMap.adjoint.comp V.toContinuousLinearMap = 1
  exact V.adjoint_comp_self
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {I : Type*}

lemma kernelForm_mapDomain_left (K : Matrix I I ℂ) (f : I → I) (x y : I →₀ ℂ) :
    kernelForm K (Finsupp.mapDomain f x) y = kernelForm (fun i j => K (f i) j) x y := by
  classical
  unfold kernelForm
  rw [Finsupp.sum_mapDomain_index]
  · intro i
    simp
  · intro i a b
    simp only [star_add, add_mul, Finsupp.sum, Finset.sum_add_distrib]

lemma kernelForm_mapDomain_right (K : Matrix I I ℂ) (f : I → I) (x y : I →₀ ℂ) :
    kernelForm K x (Finsupp.mapDomain f y) = kernelForm (fun i j => K i (f j)) x y := by
  classical
  unfold kernelForm
  apply Finsupp.sum_congr
  intro i hi
  rw [Finsupp.sum_mapDomain_index]
  · intro j
    simp
  · intro j a b
    exact mul_add _ _ _

lemma kernelForm_mapDomain (K : Matrix I I ℂ) (f : I → I) (x y : I →₀ ℂ) :
    kernelForm K (Finsupp.mapDomain f x) (Finsupp.mapDomain f y) =
      kernelForm (fun i j => K (f i) (f j)) x y := by
  rw [kernelForm_mapDomain_left]
  exact kernelForm_mapDomain_right (K := (fun i j => K (f i) j)) f x y

lemma kernelPre_norm_sq (K : Matrix I I ℂ) (hK : K.PosSemidef)
    (x : PositiveKernelPreSpace K hK) : ‖x‖ ^ 2 = (kernelForm K x x).re :=
  norm_sq_eq_re_inner (𝕜 := ℂ) x

def kernelPreMap (K : Matrix I I ℂ) (hK : K.PosSemidef) (f : I → I)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x : I →₀ ℂ, (kernelForm (fun i j => K (f i) (f j)) x x).re ≤
      C ^ 2 * (kernelForm K x x).re) :
    PositiveKernelPreSpace K hK →L[ℂ] PositiveKernelPreSpace K hK :=
  let L : PositiveKernelPreSpace K hK →ₗ[ℂ] PositiveKernelPreSpace K hK :=
    { toFun := Finsupp.mapDomain f
      map_add' _ _ := Finsupp.mapDomain_add
      map_smul' r x := Finsupp.mapDomain_smul r x }
  L.mkContinuous C (fun x => by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
    rw [mul_pow, kernelPre_norm_sq K hK, kernelPre_norm_sq K hK]
    change (kernelForm K (Finsupp.mapDomain f x) (Finsupp.mapDomain f x)).re ≤
      C ^ 2 * (kernelForm K x x).re
    exact (congrArg Complex.re (kernelForm_mapDomain K f
      (show I →₀ ℂ from x) (show I →₀ ℂ from x))).trans_le (hf x))

@[simp] lemma kernelPreMap_apply (K : Matrix I I ℂ) (hK : K.PosSemidef) (f : I → I)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x : I →₀ ℂ, (kernelForm (fun i j => K (f i) (f j)) x x).re ≤
      C ^ 2 * (kernelForm K x x).re) (x : PositiveKernelPreSpace K hK) :
    kernelPreMap K hK f C hC hf x = Finsupp.mapDomain f x := rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev StinespringPreSpace (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :=
  PositiveKernelPreSpace (stinespringKernel φ) (stinespringKernel_positive φ)

def stinespringLeftLabel (b : M) (p : M × H) : M × H := (b * p.1, p.2)

def stinespringShift (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M)
    (x : StinespringPreSpace φ) : StinespringPreSpace φ :=
  Finsupp.mapDomain (stinespringLeftLabel b) x

lemma stinespringShift_one (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (x : StinespringPreSpace φ) : stinespringShift φ 1 x = x := by
  have he : stinespringLeftLabel (H := H) (1 : M) = id := by
    funext p
    simp only [stinespringLeftLabel, one_mul, id_eq]
  unfold stinespringShift
  dsimp only [StinespringPreSpace, PositiveKernelPreSpace] at x ⊢
  rw [he, Finsupp.mapDomain_id]

lemma stinespringShift_mul (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (a b : M) (x : StinespringPreSpace φ) :
    stinespringShift φ a (stinespringShift φ b x) = stinespringShift φ (a * b) x := by
  have he : stinespringLeftLabel (H := H) a ∘ stinespringLeftLabel b =
      stinespringLeftLabel (a * b) := by
    funext p
    simp only [Function.comp_apply, stinespringLeftLabel, mul_assoc]
  unfold stinespringShift
  dsimp only [StinespringPreSpace, PositiveKernelPreSpace] at x ⊢
  rw [← Finsupp.mapDomain_comp, he]

lemma stinespringLeft_bound (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M)
    (x : (M × H) →₀ ℂ) :
    (kernelForm (fun p q => stinespringKernel φ (stinespringLeftLabel b p)
      (stinespringLeftLabel b q)) x x).re ≤ ‖b‖ ^ 2 * (kernelForm (stinespringKernel φ) x x).re := by
  classical
  change (kernelForm (fun p q : M × H => inner ℂ p.2
    (φ (star (b * p.1) * (b * q.1)) q.2)) x x).re ≤
      ‖b‖ ^ 2 * (kernelForm (fun p q : M × H => inner ℂ p.2
        (φ (star p.1 * q.1) q.2)) x x).re
  rw [kernelForm_coefficients, kernelForm_coefficients]
  exact completelyPositive_kernel_left_bound φ (fun p : x.support => p.val.1)
    (fun p : x.support => x p • p.val.2) b

def stinespringPreOperator (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M) :
    StinespringPreSpace φ →L[ℂ] StinespringPreSpace φ :=
  kernelPreMap (stinespringKernel φ) (stinespringKernel_positive φ)
    (stinespringLeftLabel b) ‖b‖ (norm_nonneg _) (stinespringLeft_bound φ b)

def stinespringOperator (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M) :
    StinespringSpace φ →L[ℂ] StinespringSpace φ :=
  (stinespringPreOperator φ b).completion

@[simp] lemma stinespringOperator_coe (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (b : M) (x : StinespringPreSpace φ) :
    stinespringOperator φ b x =
      (UniformSpace.Completion.coe' (stinespringShift φ b x)) := by
  exact ContinuousLinearMap.completion_apply_coe (stinespringPreOperator φ b) x
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace
open UniformSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma stinespringOperator_ext (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (A B : StinespringSpace φ →L[ℂ] StinespringSpace φ)
    (h : ∀ x y : StinespringPreSpace φ,
      inner ℂ (x : StinespringSpace φ) (A y) = inner ℂ (x : StinespringSpace φ) (B y)) :
    A = B := by
  apply ContinuousLinearMap.ext
  intro η
  apply ext_inner_left ℂ
  intro ξ
  induction ξ, η using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y => exact h x y

lemma stinespringOperator_inner_coe (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (b : M) (x y : StinespringPreSpace φ) :
    inner ℂ (x : StinespringSpace φ) (stinespringOperator φ b y) =
      kernelForm (fun p q : M × H => inner ℂ p.2 (φ (star p.1 * b * q.1) q.2)) x y := by
  rw [stinespringOperator_coe, Completion.inner_coe]
  change kernelForm (stinespringKernel φ) x (Finsupp.mapDomain (stinespringLeftLabel b) y) = _
  have he := kernelForm_mapDomain_right (stinespringKernel φ) (stinespringLeftLabel b)
    (show (M × H) →₀ ℂ from x) (show (M × H) →₀ ℂ from y)
  refine he.trans ?_
  congr 1
  funext p q
  simp only [stinespringKernel, stinespringLeftLabel, mul_assoc]

lemma stinespringOperator_zero (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    stinespringOperator φ 0 = 0 := by
  apply stinespringOperator_ext φ
  intro x y
  rw [stinespringOperator_inner_coe]
  simp [kernelForm, Finsupp.sum]

lemma stinespringOperator_add (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a b : M) :
    stinespringOperator φ (a + b) = stinespringOperator φ a + stinespringOperator φ b := by
  apply stinespringOperator_ext φ
  intro x y
  simp only [add_apply, inner_add_right, stinespringOperator_inner_coe, kernelForm,
    mul_add, add_mul, map_add, Finsupp.sum, Finset.sum_add_distrib]

lemma stinespringOperator_one (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    stinespringOperator φ 1 = 1 := by
  apply stinespringOperator_ext φ
  intro x y
  rw [stinespringOperator_coe]
  rw [stinespringShift_one]
  rfl

lemma stinespringOperator_mul (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a b : M) :
    stinespringOperator φ (a * b) = stinespringOperator φ a * stinespringOperator φ b := by
  apply stinespringOperator_ext φ
  intro x y
  rw [mul_apply_eq_comp, stinespringOperator_coe, stinespringOperator_coe,
    stinespringOperator_coe, stinespringShift_mul]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace
open UniformSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma stinespringOperator_star (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M) :
    stinespringOperator φ (star b) = star (stinespringOperator φ b) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro ξ η
  induction ξ, η using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    rw [stinespringOperator_coe, stinespringOperator_coe, Completion.inner_coe, Completion.inner_coe]
    change kernelForm (stinespringKernel φ) (Finsupp.mapDomain (stinespringLeftLabel (star b)) x) y =
      kernelForm (stinespringKernel φ) x (Finsupp.mapDomain (stinespringLeftLabel b) y)
    have hl := kernelForm_mapDomain_left (stinespringKernel φ) (stinespringLeftLabel (star b))
      (show (M × H) →₀ ℂ from x) (show (M × H) →₀ ℂ from y)
    have hr := kernelForm_mapDomain_right (stinespringKernel φ) (stinespringLeftLabel b)
      (show (M × H) →₀ ℂ from x) (show (M × H) →₀ ℂ from y)
    refine hl.trans ((congrArg (fun K : Matrix (M × H) (M × H) ℂ => kernelForm K x y) ?_).trans hr.symm)
    funext p q
    simp only [stinespringKernel, stinespringLeftLabel, star_mul, star_star, mul_assoc]

lemma stinespringOperator_smul (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (z : ℂ) (b : M) :
    stinespringOperator φ (z • b) = z • stinespringOperator φ b := by
  apply stinespringOperator_ext φ
  intro x y
  rw [smul_apply, inner_smul_right, stinespringOperator_inner_coe, stinespringOperator_inner_coe]
  simp only [kernelForm, mul_smul_comm, smul_mul_assoc, map_smul,
    smul_apply, inner_smul_right, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

def stinespringRepresentation (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    M →⋆ₐ[ℂ] (StinespringSpace φ →L[ℂ] StinespringSpace φ) where
  toFun := stinespringOperator φ
  map_zero' := stinespringOperator_zero φ
  map_one' := stinespringOperator_one φ
  map_add' := stinespringOperator_add φ
  map_mul' := stinespringOperator_mul φ
  map_star' := stinespringOperator_star φ
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one, stinespringOperator_smul, stinespringOperator_one]
    rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace
open UniformSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def stinespringPreVector (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    StinespringPreSpace φ := Finsupp.single (1, ξ) 1

def stinespringVector (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    StinespringSpace φ := Completion.coe' (stinespringPreVector φ ξ)

lemma stinespringVector_pairing (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (x : StinespringPreSpace φ) (ξ : H) :
    inner ℂ (x : StinespringSpace φ) (stinespringVector φ ξ) =
      x.sum (fun p z => star z * inner ℂ p.2 (φ (star p.1) ξ)) := by
  classical
  rw [stinespringVector, Completion.inner_coe]
  change kernelForm (stinespringKernel φ) x (stinespringPreVector φ ξ) = _
  simp [kernelForm, stinespringKernel, stinespringPreVector]

lemma stinespringVector_add (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ η : H) :
    stinespringVector φ (ξ + η) = stinespringVector φ ξ + stinespringVector φ η := by
  apply ext_inner_left ℂ
  intro ω
  induction ω using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    simp only [inner_add_right, stinespringVector_pairing, map_add, mul_add,
      Finsupp.sum, Finset.sum_add_distrib]

lemma stinespringVector_smul (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (z : ℂ) (ξ : H) :
    stinespringVector φ (z • ξ) = z • stinespringVector φ ξ := by
  apply ext_inner_left ℂ
  intro ω
  induction ω using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    simp only [inner_smul_right, stinespringVector_pairing, map_smul,
      Finsupp.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring

lemma stinespringVector_norm_sq (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    ‖stinespringVector φ ξ‖ ^ 2 = (inner ℂ ξ (φ 1 ξ)).re := by
  classical
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (inner ℂ ((stinespringPreVector φ ξ) : StinespringSpace φ) (stinespringVector φ ξ)).re = _
  rw [stinespringVector_pairing]
  simp [stinespringPreVector]

lemma stinespringVector_bound (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    ‖stinespringVector φ ξ‖ ≤ Real.sqrt ‖φ 1‖ * ‖ξ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (norm_nonneg _), stinespringVector_norm_sq]
  calc
    _ ≤ ‖inner ℂ ξ (φ 1 ξ)‖ := Complex.re_le_norm _
    _ ≤ ‖ξ‖ * ‖φ 1 ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖ * (‖φ 1‖ * ‖ξ‖) :=
      mul_le_mul_of_nonneg_left ((φ 1).le_opNorm ξ) (norm_nonneg _)
    _ = _ := by ring

def stinespringEmbedding (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    H →L[ℂ] StinespringSpace φ :=
  LinearMap.mkContinuous
    { toFun := stinespringVector φ
      map_add' := stinespringVector_add φ
      map_smul' := stinespringVector_smul φ }
    (Real.sqrt ‖φ 1‖) (stinespringVector_bound φ)

@[simp] lemma stinespringEmbedding_apply (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    stinespringEmbedding φ ξ = stinespringVector φ ξ := rfl

lemma stinespringVector_coefficient (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (a : M) (ξ η : H) :
    inner ℂ (stinespringVector φ ξ) (stinespringRepresentation φ a (stinespringVector φ η)) =
      inner ℂ ξ (φ a η) := by
  classical
  change inner ℂ ((stinespringPreVector φ ξ) : StinespringSpace φ)
    (stinespringOperator φ a (stinespringPreVector φ η)) = _
  rw [stinespringOperator_inner_coe]
  simp [kernelForm, stinespringPreVector]

theorem stinespring_factorization (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : M) :
    φ a = (stinespringEmbedding φ).adjoint.comp
      ((stinespringRepresentation φ a).comp (stinespringEmbedding φ)) := by
  apply ContinuousLinearMap.ext
  intro η
  apply ext_inner_left ℂ
  intro ξ
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  exact (stinespringVector_coefficient φ a ξ η).symm
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma stinespringEmbedding_norm_le (φ : CompletelyPositiveMap A (H →L[ℂ] H)) :
    ‖stinespringEmbedding φ‖ ≤ Real.sqrt ‖φ 1‖ :=
  (stinespringEmbedding φ).opNorm_le_bound (Real.sqrt_nonneg _)
    (stinespringVector_bound φ)

theorem completelyPositive_norm_apply_le (φ : CompletelyPositiveMap A (H →L[ℂ] H))
    (a : A) : ‖φ a‖ ≤ ‖φ 1‖ * ‖a‖ := by
  have hV := stinespringEmbedding_norm_le φ
  calc
    ‖φ a‖ = ‖(stinespringEmbedding φ).adjoint.comp
        ((stinespringRepresentation φ a).comp (stinespringEmbedding φ))‖ :=
      congrArg norm (stinespring_factorization φ a)
    _ ≤ ‖(stinespringEmbedding φ).adjoint‖ *
        (‖stinespringRepresentation φ a‖ * ‖stinespringEmbedding φ‖) := by
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ Real.sqrt ‖φ 1‖ * (‖a‖ * Real.sqrt ‖φ 1‖) := by
      rw [LinearIsometryEquiv.norm_map]
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le (stinespringRepresentation φ) a
    _ = ‖φ 1‖ * ‖a‖ := by
      calc
        _ = (Real.sqrt ‖φ 1‖) ^ 2 * ‖a‖ := by ring
        _ = _ := by rw [Real.sq_sqrt (norm_nonneg (φ 1))]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_finite_compression_extension (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (hstar : ∀ a ∈ S, star a ∈ S) (φ : S →ₗ[ℂ] (H →L[ℂ] H))
    (hφ1 : φ ⟨1, h1⟩ = 1) {n : ℕ} (i₀ : Fin n)
    (V : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] H)
    (hφ : ∀ X : operatorSystemMatrices S n,
      0 ≤ (X : CStarMatrix (Fin n) (Fin n) A) →
        0 ≤ operatorSystemAmplification S φ n X) :
    ∃ Ψ : CompletelyPositiveMap A (H →L[ℂ] H),
      (∀ a, ‖Ψ a‖ ≤ ‖a‖) ∧ ∀ (a : S) ξ η,
        inner ℂ (V η) (Ψ (a : A) (V ξ)) = inner ℂ (V η) (φ a (V ξ)) := by
  let ψ := compressOperatorSystem S φ V.toContinuousLinearMap
  obtain ⟨Φ, hΦ⟩ := exists_finite_completelyPositive_extension S h1 hstar i₀ ψ
    (fun X hX => compressOperatorSystem_positive S φ _ X (hφ X hX))
  have hΦ1 : Φ 1 = 1 := (hΦ ⟨1, h1⟩).trans (compressOperatorSystem_one S h1 φ hφ1 V)
  let Ψ := compressCompletelyPositive Φ V.toContinuousLinearMap.adjoint
  have hV : ‖V.toContinuousLinearMap‖ ≤ 1 := by
    apply V.toContinuousLinearMap.opNorm_le_bound zero_le_one
    intro ξ
    simp only [LinearIsometry.coe_toContinuousLinearMap, V.norm_map, one_mul]
    exact le_rfl
  have hΨ1 : Ψ 1 = V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint := by
    change V.toContinuousLinearMap.adjoint.adjoint.comp
      ((Φ 1).comp V.toContinuousLinearMap.adjoint) = _
    rw [ContinuousLinearMap.adjoint_adjoint, hΦ1]
    rfl
  have hn : ‖Ψ 1‖ ≤ 1 := by
    rw [hΨ1]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map]
    nlinarith [norm_nonneg V.toContinuousLinearMap]
  have hVV (ξ : EuclideanSpace ℂ (Fin n)) : V.toContinuousLinearMap.adjoint (V ξ) = ξ := by
    exact congrArg (fun T => T ξ) V.adjoint_comp_self
  refine ⟨Ψ, fun a => (completelyPositive_norm_apply_le Ψ a).trans ?_, ?_⟩
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (norm_nonneg a)
  · intro a ξ η
    change inner ℂ (V η) (V.toContinuousLinearMap.adjoint.adjoint
      (Φ (a : A) (V.toContinuousLinearMap.adjoint (V ξ)))) = _
    rw [ContinuousLinearMap.adjoint_inner_right, hVV, hVV, hΦ a]
    change inner ℂ η (V.toContinuousLinearMap.adjoint (φ a (V ξ))) = _
    exact ContinuousLinearMap.adjoint_inner_right _ _ _
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]

theorem exists_finite_coefficient_extension (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (hstar : ∀ a ∈ S, star a ∈ S) (φ : S →ₗ[ℂ] (H →L[ℂ] H))
    (hφ1 : φ ⟨1, h1⟩ = 1)
    (hφ : ∀ n (X : operatorSystemMatrices S n),
      0 ≤ (X : CStarMatrix (Fin n) (Fin n) A) →
        0 ≤ operatorSystemAmplification S φ n X) (s : Finset H) :
    ∃ Ψ : CompletelyPositiveMap A (H →L[ℂ] H),
      (∀ a, ‖Ψ a‖ ≤ ‖a‖) ∧ ∀ (a : S) (ξ : H), ξ ∈ s → ∀ η ∈ s,
        inner ℂ η (Ψ (a : A) ξ) = inner ℂ η (φ a ξ) := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_ne (0 : H)
  let t := insert ζ s
  let E := Submodule.span ℂ (t : Set H)
  let : FiniteDimensional ℂ E := FiniteDimensional.span_finset ℂ t
  let ζE : E := ⟨ζ, Submodule.subset_span (Finset.mem_insert_self ζ s)⟩
  let : Nontrivial E := ⟨⟨ζE, 0, fun h => hζ (congrArg Subtype.val h)⟩⟩
  let b := stdOrthonormalBasis ℂ E
  let V : EuclideanSpace ℂ (Fin (Module.finrank ℂ E)) →ₗᵢ[ℂ] H :=
    E.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  let i₀ : Fin (Module.finrank ℂ E) := ⟨0, Module.finrank_pos⟩
  obtain ⟨Ψ, hΨ, hcoeff⟩ := exists_finite_compression_extension S h1 hstar φ hφ1 i₀ V
    (hφ (Module.finrank ℂ E))
  refine ⟨Ψ, hΨ, fun a ξ hξ η hη => ?_⟩
  let ξE : E := ⟨ξ, Submodule.subset_span (Finset.mem_insert_of_mem hξ)⟩
  let ηE : E := ⟨η, Submodule.subset_span (Finset.mem_insert_of_mem hη)⟩
  have hξE : V (b.repr ξE) = ξ := by
    change ((b.repr.symm (b.repr ξE) : E) : H) = ξ
    rw [b.repr.symm_apply_apply]
  have hηE : V (b.repr ηE) = η := by
    change ((b.repr.symm (b.repr ηE) : E) : H) = η
    rw [b.repr.symm_apply_apply]
  simpa only [hξE, hηE] using hcoeff a (b.repr ξE) (b.repr ηE)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_completelyPositive_ultralimit (ω : Ultrafilter ι)
    (φ : ι → CompletelyPositiveMap A (H →L[ℂ] H)) {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ i a, ‖φ i a‖ ≤ C * ‖a‖) :
    ∃ Φ : CompletelyPositiveMap A (H →L[ℂ] H),
      (∀ a, ‖Φ a‖ ≤ C * ‖a‖) ∧ ∀ a ξ η,
        Tendsto (fun i => inner ℂ η (φ i a ξ)) (ω : Filter ι)
          (𝓝 (inner ℂ η (Φ a ξ))) := by
  have hex (a : A) := Generator.Tracial.exists_weak_operator_ultralimit ω
    (fun i => φ i a) (C * ‖a‖) (mul_nonneg hC (norm_nonneg a)) (fun i => hφ i a)
  choose T hT ht using hex
  have hadd (a b : A) : T (a + b) = T a + T b := by
    apply ContinuousLinearMap.ext
    intro ξ
    apply ext_inner_left ℂ
    intro η
    apply tendsto_nhds_unique (ht (a + b) ξ η)
    simpa only [map_add, add_apply, inner_add_right] using (ht a ξ η).add (ht b ξ η)
  have hsmul (z : ℂ) (a : A) : T (z • a) = z • T a := by
    apply ContinuousLinearMap.ext
    intro ξ
    apply ext_inner_left ℂ
    intro η
    apply tendsto_nhds_unique (ht (z • a) ξ η)
    simpa only [map_smul, smul_apply, inner_smul_right, smul_eq_mul] using
      (ht a ξ η).const_mul z
  let L : A →ₗ[ℂ] (H →L[ℂ] H) :=
    { toFun := T, map_add' := hadd, map_smul' := hsmul }
  have hpos (n : ℕ) (B : CStarMatrix (Fin n) (Fin n) A) (hB : 0 ≤ B) :
      0 ≤ B.map L := by
    apply operatorMatrix_nonneg_of_quadratic
    intro ξ
    have hl : Tendsto (fun i => ∑ j, ∑ k, inner ℂ (ξ j) (φ i (B j k) (ξ k)))
        (ω : Filter ι) (𝓝 (∑ j, ∑ k, inner ℂ (ξ j) (T (B j k) (ξ k)))) := by
      apply tendsto_finsetSum
      intro j _
      apply tendsto_finsetSum
      intro k _
      exact ht (B j k) (ξ k) (ξ j)
    change 0 ≤ ∑ j, ∑ k, inner ℂ (ξ j) (T (B j k) (ξ k))
    exact ge_of_tendsto hl (Eventually.of_forall fun i =>
      operatorMatrix_quadratic_nonneg (B.map (φ i)) ((φ i).map_cstarMatrix_nonneg B hB) ξ)
  exact ⟨{ L with map_cstarMatrix_nonneg' := hpos }, hT, ht⟩
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]

theorem exists_unital_completelyPositive_extension
    (S : Submodule ℂ A) (h1 : (1 : A) ∈ S) (hstar : ∀ a ∈ S, star a ∈ S)
    (φ : S →ₗ[ℂ] (H →L[ℂ] H)) (hφ1 : φ ⟨1, h1⟩ = 1)
    (hφ : ∀ n (X : operatorSystemMatrices S n),
      0 ≤ (X : CStarMatrix (Fin n) (Fin n) A) →
        0 ≤ operatorSystemAmplification S φ n X) :
    ∃ Φ : CompletelyPositiveMap A (H →L[ℂ] H),
      Φ 1 = 1 ∧ (∀ a, ‖Φ a‖ ≤ ‖a‖) ∧ ∀ a : S, Φ (a : A) = φ a := by
  classical
  have hex := exists_finite_coefficient_extension S h1 hstar φ hφ1 hφ
  choose Ψ hΨ hcoeff using hex
  let ω : Ultrafilter (Finset H) := Ultrafilter.of atTop
  have hω : (ω : Filter (Finset H)) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨Φ, hΦ, ht⟩ := exists_completelyPositive_ultralimit ω Ψ zero_le_one
    (fun s a => by simpa only [one_mul] using hΨ s a)
  have hext (a : S) : Φ (a : A) = φ a := by
    apply ContinuousLinearMap.ext
    intro ξ
    apply ext_inner_left ℂ
    intro η
    have he : (fun s => inner ℂ η (Ψ s (a : A) ξ)) =ᶠ[ω]
        (fun _ => inner ℂ η (φ a ξ)) := by
      filter_upwards [(eventually_finset_mem_atTop ξ).filter_mono hω,
        (eventually_finset_mem_atTop η).filter_mono hω] with s hξ hη
      exact hcoeff s a ξ hξ η hη
    exact tendsto_nhds_unique (ht (a : A) ξ η) (tendsto_const_nhds.congr' he.symm)
  exact ⟨Φ, (hext ⟨1, h1⟩).trans hφ1,
    fun a => by simpa only [one_mul] using hΦ a, hext⟩
end BoundedHochschild.KadisonRingrose
end
end OAI
end

theorem solution.{u_1,u_2} : type_of% @OAI.BoundedHochschild.KadisonRingrose.exists_unital_completelyPositive_extension.{u_1,u_2} := @OAI.BoundedHochschild.KadisonRingrose.exists_unital_completelyPositive_extension.{u_1,u_2}
