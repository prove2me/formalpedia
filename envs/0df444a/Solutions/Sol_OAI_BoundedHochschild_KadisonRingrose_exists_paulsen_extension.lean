-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.exists_paulsen_extension
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:42:32.624855+00:00
-- url     : https://prove2.me/submissions/e9734078-e494-4739-a741-46ae2b4735c7

import Mathlib
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Order.Zorn
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff
import Definitions.Def_OAIQ075A006
import Definitions.Def_OAIQ075A013

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CompletelyPositiveLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded pointwise weak-operator ultralimits of completely positive maps. -/

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
-- module Solutions.OAIQ075_KS.BoundedHochschild_StinespringEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded vector map and factorization of a completely positive map. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace
open UniformSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma stinespringVector_coefficient (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (a : M) (ξ η : H) :
    inner ℂ (stinespringVector φ ξ) (stinespringRepresentation φ a (stinespringVector φ η)) =
      inner ℂ ξ (φ a η) := by
  classical
  change inner ℂ ((stinespringPreVector φ ξ) : StinespringSpace φ)
    (stinespringOperator φ a (stinespringPreVector φ η)) = _
  rw [stinespringOperator_inner_coe]
  simp [kernelForm, stinespringPreVector]

/-- Stinespring factorization on the constructed auxiliary Hilbert space. -/
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
-- module Solutions.OAIQ075_KS.BoundedHochschild_CompletelyPositiveNorm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm bound supplied by the constructed Stinespring factorization. -/

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
-- module Solutions.OAIQ075_KS.BoundedHochschild_MatrixFunctionalDilation
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive functional on a matrix algebra gives a completely positive
map into the corresponding finite-dimensional operator algebra. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

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
-- module Solutions.OAIQ075_KS.BoundedHochschild_OperatorSystemFunctionals
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive scalar functionals on unital self-adjoint linear subspaces.
The extension uses real Hahn–Banach on the self-adjoint part. -/

noncomputable section

open scoped ComplexOrder ComplexStarModule

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

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
-- module Solutions.OAIQ075_KS.BoundedHochschild_OperatorSystemExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive scalar extension from an operator system. No multiplicative
closure or closedness of the subspace is required. -/

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
-- module Solutions.OAIQ075_KS.BoundedHochschild_OperatorSystemMatrices
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar matrix functional used in finite-dimensional positive extension. -/

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
-- module Solutions.OAIQ075_KS.BoundedHochschild_FinitePositiveExtension
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional operator-valued positive extension theorem.
Only positivity at the target matrix size is needed. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

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
-- module Solutions.OAIQ075_KS.BoundedHochschild_OperatorSystemCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compression of positive matrix levels on a unital linear subspace. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

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
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteCompressionExtension
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend a finite compression and then regard it as a map on the original
Hilbert space. All coefficients on that finite subspace are retained. -/

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
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteCoefficientExtension
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite collections of Hilbert-space coefficients admit simultaneous
contractive completely positive extensions. -/

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
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveUnitBlocks
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.HochschildMatrixDilation.diag_pow _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary two-by-two positivity test for a contraction. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma positiveUnitBlock_nonneg (a : A) (ha : ‖a‖ ≤ 1) : 0 ≤ positiveUnitBlock a := by
  have hsq : star a * a ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg a)).mp
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg a]
  let d := CFC.sqrt (1 - star a * a)
  have hd : star d * d = 1 - star a * a := by
    rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hsq)
  let R : Mat A := CStarMatrix.ofMatrix !![1, a; 0, d]
  have hR : star R * R = positiveUnitBlock a := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [R, positiveUnitBlock, offdiag, CStarMatrix.mul_apply, CStarMatrix.star_apply,
        Fin.sum_univ_two]
    · simp [R, positiveUnitBlock, offdiag, CStarMatrix.mul_apply, CStarMatrix.star_apply,
        Fin.sum_univ_two]
    · simp [R, positiveUnitBlock, offdiag, CStarMatrix.mul_apply, CStarMatrix.star_apply,
        Fin.sum_univ_two]
    · simp [R, positiveUnitBlock, offdiag, CStarMatrix.mul_apply, CStarMatrix.star_apply,
        Fin.sum_univ_two, hd]
  rw [← hR]
  exact star_mul_self_nonneg R

lemma norm_le_one_of_positiveUnitBlock (a : A) (ha : 0 ≤ positiveUnitBlock a) : ‖a‖ ≤ 1 := by
  let V : Mat A := CStarMatrix.ofMatrix !![-a, 0; 1, 0]
  have hp := diagEntry_nonneg (star V * positiveUnitBlock a * V)
    (star_left_conjugate_nonneg ha V) 0
  have he : (star V * positiveUnitBlock a * V) 0 0 = 1 - star a * a := by
    simp [V, positiveUnitBlock, offdiag, CStarMatrix.mul_apply, CStarMatrix.star_apply,
      Fin.sum_univ_two]
    noncomm_ring
  rw [he] at hp
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg a)).mpr
    (sub_nonneg.mp hp)
  rw [CStarRing.norm_star_mul_self] at hn
  exact (sq_le_one_iff₀ (norm_nonneg a)).mp (by simpa only [pow_two] using hn)

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveBlocks
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.HochschildMatrixDilation.diag_pow _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the two diagonal entries of a positive two-by-two block. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma positiveBlock_one (x : A) : positiveBlock 1 1 x = positiveUnitBlock x := by
  rw [positiveBlock, diag_one_one]
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma positiveBlock_conjugate (p q x u v : A) :
    star (diag u v) * positiveBlock p q x * diag u v =
      positiveBlock (star u * p * u) (star v * q * v) (star u * x * v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [positiveBlock, diag, offdiag, CStarMatrix.mul_apply, CStarMatrix.star_apply,
      Fin.sum_univ_two, star_mul, mul_assoc]

omit [PartialOrder A] [StarOrderedRing A] in
lemma diag_isUnit {u v : A} (hu : IsUnit u) (hv : IsUnit v) : IsUnit (diag u v) := by
  obtain ⟨u, rfl⟩ := hu
  obtain ⟨v, rfl⟩ := hv
  refine ⟨⟨diag (u : A) (v : A), diag (↑u⁻¹) (↑v⁻¹), ?_, ?_⟩, rfl⟩
  · rw [diag_mul]
    simp
  · rw [diag_mul]
    simp

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveBlockTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A contraction respecting the scalar matrix actions preserves positive
two-by-two blocks with strictly positive scalar diagonal entries. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {D A B : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem positiveBlock_transfer_strict (ρ : D →⋆ₐ[ℂ] A) (σ : D →⋆ₐ[ℂ] B)
    (T : A →ₗ[ℂ] B) (hT : ∀ a, ‖T a‖ ≤ ‖a‖)
    (hmodule : ∀ d e a, T (ρ d * a * ρ e) = σ d * T a * σ e)
    (p q : D) (hp : IsStrictlyPositive p) (hq : IsStrictlyPositive q) (a : A)
    (ha : 0 ≤ positiveBlock (ρ p) (ρ q) a) :
    0 ≤ positiveBlock (σ p) (σ q) (T a) := by
  let u := p ^ (-(1 / 2) : ℝ)
  let v := q ^ (-(1 / 2) : ℝ)
  have hu := IsStrictlyPositive.rpow p (-(1 / 2) : ℝ) hp
  have hv := IsStrictlyPositive.rpow q (-(1 / 2) : ℝ) hq
  have hsu : star u = u := hu.nonneg.isSelfAdjoint.star_eq
  have hsv : star v = v := hv.nonneg.isSelfAdjoint.star_eq
  have hup : star u * p * u = 1 := by
    rw [hsu]
    exact CFC.conjugate_rpow_neg_one_half p hp
  have hvq : star v * q * v = 1 := by
    rw [hsv]
    exact CFC.conjugate_rpow_neg_one_half q hq
  have hρp : star (ρ u) * ρ p * ρ u = 1 := by
    simpa only [map_mul, map_star, map_one] using congrArg ρ hup
  have hρq : star (ρ v) * ρ q * ρ v = 1 := by
    simpa only [map_mul, map_star, map_one] using congrArg ρ hvq
  have hσp : star (σ u) * σ p * σ u = 1 := by
    simpa only [map_mul, map_star, map_one] using congrArg σ hup
  have hσq : star (σ v) * σ q * σ v = 1 := by
    simpa only [map_mul, map_star, map_one] using congrArg σ hvq
  have hρu : star (ρ u) = ρ u := by rw [← map_star, hsu]
  have hσu : star (σ u) = σ u := by rw [← map_star, hsu]
  have hnA : ‖ρ u * a * ρ v‖ ≤ 1 := by
    have h := star_left_conjugate_nonneg ha (diag (ρ u) (ρ v))
    rw [positiveBlock_conjugate, hρp, hρq, hρu, positiveBlock_one] at h
    exact norm_le_one_of_positiveUnitBlock _ h
  have hnB : ‖star (σ u) * T a * σ v‖ ≤ 1 := by
    rw [hσu, ← hmodule]
    exact (hT _).trans hnA
  have hpos := positiveUnitBlock_nonneg _ hnB
  have he := positiveBlock_conjugate (σ p) (σ q) (T a) (σ u) (σ v)
  rw [hσp, hσq, positiveBlock_one] at he
  rw [← he] at hpos
  exact (diag_isUnit (hu.isUnit.map σ.toMonoidHom) (hv.isUnit.map σ.toMonoidHom)).star_left_conjugate_nonneg_iff.mp hpos

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveBlockRegularization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.HochschildMatrixDilation.diag_pow _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove strict positivity of the scalar block entries by norm limits. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {D A B : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma starAlgHom_real_one (ρ : D →⋆ₐ[ℂ] A) (r : ℝ) :
    ρ (r • (1 : D)) = r • (1 : A) := by
  rw [← Complex.coe_smul, map_smul, map_one, Complex.coe_smul]

lemma positive_real_one (r : ℝ) (hr : 0 < r) : IsStrictlyPositive (r • (1 : D)) := by
  refine ⟨smul_nonneg hr.le zero_le_one, ?_⟩
  rw [← Algebra.algebraMap_eq_smul_one]
  exact (isUnit_iff_ne_zero.mpr hr.ne').map (algebraMap ℝ D)

omit [PartialOrder A] [StarOrderedRing A] in
lemma positiveBlock_add_real_one (p q x : A) (r : ℝ) :
    positiveBlock (p + r • 1) (q + r • 1) x = positiveBlock p q x + r • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [positiveBlock, diag, offdiag, add_comm]

theorem positiveBlock_transfer (ρ : D →⋆ₐ[ℂ] A) (σ : D →⋆ₐ[ℂ] B)
    (T : A →ₗ[ℂ] B) (hT : ∀ a, ‖T a‖ ≤ ‖a‖)
    (hmodule : ∀ d e a, T (ρ d * a * ρ e) = σ d * T a * σ e)
    (p q : D) (hp : 0 ≤ p) (hq : 0 ≤ q) (a : A)
    (ha : 0 ≤ positiveBlock (ρ p) (ρ q) a) :
    0 ≤ positiveBlock (σ p) (σ q) (T a) := by
  have heps (r : ℝ) (hr : 0 < r) :
      0 ≤ positiveBlock (σ p) (σ q) (T a) + r • 1 := by
    have h := positiveBlock_transfer_strict ρ σ T hT hmodule
      (p + r • 1) (q + r • 1)
      (IsStrictlyPositive.nonneg_add hp (positive_real_one r hr))
      (IsStrictlyPositive.nonneg_add hq (positive_real_one r hr)) a
    simp only [map_add, starAlgHom_real_one, positiveBlock_add_real_one] at h
    exact h (add_nonneg ha (smul_nonneg hr.le zero_le_one))
  have ht : Tendsto (fun n : ℕ => positiveBlock (σ p) (σ q) (T a) +
      (1 / ((n : ℝ) + 1)) • 1) atTop (𝓝 (positiveBlock (σ p) (σ q) (T a))) := by
    simpa only [zero_smul, add_zero] using
      (tendsto_const_nhds.add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul
        (tendsto_const_nhds (x := (1 : Mat B)))))
  exact ge_of_tendsto' ht (fun n => heps _ (by positivity))

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_ScalarMatrixActions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entrywise scalar matrices and their action on matrix amplifications. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma scalarMatrixHom_injective [Nontrivial A] (n : ℕ) :
    Function.Injective (scalarMatrixHom A n) :=
  CStarMatrix.map_injective (algebraMap ℂ A).injective

lemma linearMap_scalar_multiply (T : A →ₗ[ℂ] B) (z w : ℂ) (a : A) :
    T (algebraMap ℂ A z * a * algebraMap ℂ A w) =
      algebraMap ℂ B z * T a * algebraMap ℂ B w := by
  simp [Algebra.algebraMap_eq_smul_one]

lemma entrywiseMatrixLinear_scalar_actions (T : A →ₗ[ℂ] B) (n : ℕ)
    (Q R : CStarMatrix (Fin n) (Fin n) ℂ) (X : CStarMatrix (Fin n) (Fin n) A) :
    entrywiseMatrixLinear T n (scalarMatrixHom A n Q * X * scalarMatrixHom A n R) =
      scalarMatrixHom B n Q * entrywiseMatrixLinear T n X * scalarMatrixHom B n R := by
  apply CStarMatrix.ext
  intro i j
  change T (∑ k, (∑ l, algebraMap ℂ A (Q i l) * X l k) * algebraMap ℂ A (R k j)) =
    ∑ k, (∑ l, algebraMap ℂ B (Q i l) * T (X l k)) * algebraMap ℂ B (R k j)
  simp only [Finset.sum_mul, map_sum, linearMap_scalar_multiply]

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_ScalarPositiveBlocks
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.HochschildMatrixDilation.diag_pow _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete contractions preserve the positive scalar-diagonal blocks
appearing in the two-by-two operator system. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Nontrivial A]

lemma scalarBlock_diagonals_nonneg (n : ℕ)
    (p q : CStarMatrix (Fin n) (Fin n) ℂ) (X : CStarMatrix (Fin n) (Fin n) A)
    (hX : 0 ≤ positiveBlock (scalarMatrixHom A n p) (scalarMatrixHom A n q) X) :
    0 ≤ p ∧ 0 ≤ q := by
  have hp := diagEntry_nonneg _ hX 0
  have hq := diagEntry_nonneg _ hX 1
  have hρ := scalarMatrixHom_injective (A := A) n
  constructor
  · apply (NonUnitalStarAlgHom.map_le_map_iff (scalarMatrixHom A n) hρ).mp
    simpa [positiveBlock, diag, offdiag] using hp
  · apply (NonUnitalStarAlgHom.map_le_map_iff (scalarMatrixHom A n) hρ).mp
    simpa [positiveBlock, diag, offdiag] using hq

theorem scalarPositiveBlock_transfer (T : A →ₗ[ℂ] B) (n : ℕ)
    (hT : ∀ X : CStarMatrix (Fin n) (Fin n) A, ‖X.map T‖ ≤ ‖X‖)
    (p q : CStarMatrix (Fin n) (Fin n) ℂ) (X : CStarMatrix (Fin n) (Fin n) A)
    (hX : 0 ≤ positiveBlock (scalarMatrixHom A n p) (scalarMatrixHom A n q) X) :
    0 ≤ positiveBlock (scalarMatrixHom B n p) (scalarMatrixHom B n q) (X.map T) := by
  obtain ⟨hp, hq⟩ := scalarBlock_diagonals_nonneg n p q X hX
  exact positiveBlock_transfer (scalarMatrixHom A n) (scalarMatrixHom B n)
    (entrywiseMatrixLinear T n) hT (entrywiseMatrixLinear_scalar_actions T n)
    p q hp hq X hX

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PaulsenSystem
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.HochschildMatrixDilation.diag_pow _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unital two-by-two operator system associated to a linear map. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma paulsenSystem_star (X : Mat A) (hX : X ∈ paulsenSystem A) :
    star X ∈ paulsenSystem A := by
  obtain ⟨z, w, hz, hw⟩ := hX
  refine ⟨star z, star w, ?_, ?_⟩
  · change star (X 0 0) = _
    rw [hz]
    exact (map_star (StarAlgHom.ofId ℂ A) z).symm
  · change star (X 1 1) = _
    rw [hw]
    exact (map_star (StarAlgHom.ofId ℂ A) w).symm

lemma paulsenSystemMap_one (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1) (T : A →ₗ[ℂ] B) :
    paulsenSystemMap f T ⟨1, paulsenSystem_one⟩ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [paulsenSystemMap, paulsenLinear, starConjugateLinear, hf]

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PaulsenMatrixBlocks
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.HochschildMatrixDilation.diag_pow _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify amplified two-by-two operator systems with scalar-diagonal blocks. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma positiveBlock_zero_zero (p q x : A) : positiveBlock p q x 0 0 = p := by
  simp [positiveBlock, diag, offdiag]
lemma positiveBlock_zero_one (p q x : A) : positiveBlock p q x 0 1 = x := by
  simp [positiveBlock, diag, offdiag]
lemma positiveBlock_one_zero (p q x : A) : positiveBlock p q x 1 0 = star x := by
  simp [positiveBlock, diag, offdiag]
lemma positiveBlock_one_one (p q x : A) : positiveBlock p q x 1 1 = q := by
  simp [positiveBlock, diag, offdiag]

lemma paulsen_scalar_coefficient (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1) (z : ℂ) :
    f (algebraMap ℂ A z) = z := by
  simp [Algebra.algebraMap_eq_smul_one, hf]

lemma paulsen_diagonal_coefficient (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1)
    (X : paulsenSystem A) (i : Fin 2) :
    algebraMap ℂ A (f (X.val i i)) = X.val i i := by
  obtain ⟨z, w, hz, hw⟩ := X.property
  fin_cases i
  · exact (congrArg (fun a => algebraMap ℂ A (f a)) hz).trans
      ((congrArg (algebraMap ℂ A) (paulsen_scalar_coefficient f hf z)).trans hz.symm)
  · exact (congrArg (fun a => algebraMap ℂ A (f a)) hw).trans
      ((congrArg (algebraMap ℂ A) (paulsen_scalar_coefficient f hf w)).trans hw.symm)

variable [PartialOrder A] [StarOrderedRing A]

lemma paulsenMatrix_lower {n : ℕ} (X : operatorSystemMatrices (paulsenSystem A) n)
    (hX : 0 ≤ X.val) (i j : Fin n) : X.val i j 1 0 = star (X.val j i 0 1) := by
  exact (congrArg (fun Y : CStarMatrix (Fin n) (Fin n) (Mat A) => Y i j 1 0)
    hX.isSelfAdjoint.star_eq).symm

lemma paulsenMatrix_source_block (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1) {n : ℕ}
    (X : operatorSystemMatrices (paulsenSystem A) n) (hX : 0 ≤ X.val) :
    flipMatrixNesting n 2 X.val = positiveBlock
      (scalarMatrixHom A n (paulsenMatrixDiagonal f 0 X))
      (scalarMatrixHom A n (paulsenMatrixDiagonal f 1 X)) (paulsenMatrixUpper X) := by
  let p := scalarMatrixHom A n (paulsenMatrixDiagonal f 0 X)
  let q := scalarMatrixHom A n (paulsenMatrixDiagonal f 1 X)
  let x := paulsenMatrixUpper X
  apply CStarMatrix.ext
  intro d e
  apply CStarMatrix.ext
  intro i j
  fin_cases d <;> fin_cases e
  · exact (paulsen_diagonal_coefficient f hf ⟨X.val i j, X.property i j⟩ 0).symm.trans
      (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) A => Z i j)
        (positiveBlock_zero_zero p q x)).symm
  · exact (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) A => Z i j)
      (positiveBlock_zero_one p q x)).symm
  · exact (paulsenMatrix_lower X hX i j).trans
      (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) A => Z i j)
        (positiveBlock_one_zero p q x)).symm
  · exact (paulsen_diagonal_coefficient f hf ⟨X.val i j, X.property i j⟩ 1).symm.trans
      (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) A => Z i j)
        (positiveBlock_one_one p q x)).symm

variable [PartialOrder B] [StarOrderedRing B]

lemma paulsenMatrix_target_block (f : A →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] B) {n : ℕ}
    (X : operatorSystemMatrices (paulsenSystem A) n) (hX : 0 ≤ X.val) :
    flipMatrixNesting n 2 (operatorSystemAmplification (paulsenSystem A)
      (paulsenSystemMap f T) n X) = positiveBlock
      (scalarMatrixHom B n (paulsenMatrixDiagonal f 0 X))
      (scalarMatrixHom B n (paulsenMatrixDiagonal f 1 X)) ((paulsenMatrixUpper X).map T) := by
  let p := scalarMatrixHom B n (paulsenMatrixDiagonal f 0 X)
  let q := scalarMatrixHom B n (paulsenMatrixDiagonal f 1 X)
  let x := (paulsenMatrixUpper X).map T
  apply CStarMatrix.ext
  intro d e
  apply CStarMatrix.ext
  intro i j
  fin_cases d <;> fin_cases e
  · exact (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) B => Z i j)
      (positiveBlock_zero_zero p q x)).symm
  · exact (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) B => Z i j)
      (positiveBlock_zero_one p q x)).symm
  · have hh : star (T (star (X.val i j 1 0))) = star (T (X.val j i 0 1)) := by
      have h := congrArg (fun a => star (T (star a))) (paulsenMatrix_lower X hX i j)
      simpa only [star_star] using h
    exact hh.trans (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) B => Z i j)
      (positiveBlock_one_zero p q x)).symm
  · exact (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) B => Z i j)
      (positiveBlock_one_one p q x)).symm

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PaulsenPositivity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete contractivity implies complete positivity of the associated
unital two-by-two operator-system map. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Nontrivial A]

theorem paulsenSystemMap_positive (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1) (T : A →ₗ[ℂ] B)
    (hT : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X.map T‖ ≤ ‖X‖)
    (n : ℕ) (X : operatorSystemMatrices (paulsenSystem A) n) (hX : 0 ≤ X.val) :
    0 ≤ operatorSystemAmplification (paulsenSystem A) (paulsenSystemMap f T) n X := by
  have hs := map_nonneg (flipMatrixNesting (A := A) n 2) hX
  rw [paulsenMatrix_source_block f hf X hX] at hs
  have ht := scalarPositiveBlock_transfer T n (hT n)
    (paulsenMatrixDiagonal f 0 X) (paulsenMatrixDiagonal f 1 X) (paulsenMatrixUpper X) hs
  rw [← paulsenMatrix_target_block f T X hX] at ht
  have h := map_nonneg (flipMatrixNesting (A := B) n 2).symm ht
  simpa only [StarAlgEquiv.symm_apply_apply] using h

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_UnitalPositiveExtension
attribute [-instance] _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unital completely positive extension, without a separability hypothesis.
Finite coefficient extensions are joined by a weak-operator ultralimit. -/

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

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PaulsenExtension
attribute [-instance] _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend the two-by-two operator-system map into operators on the doubled
Hilbert space, using the proved positive extension theorem. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma matrixDouble_one :
    doubleMatrixHom (H := H) (1 : Mat (H →L[ℂ] H)) = 1 := by
  ext ξ i
  change (∑ j : Fin 2, (1 : Mat (H →L[ℂ] H)) i j (ξ j)) = ξ i
  fin_cases i <;> simp [CStarMatrix.one_apply, apply_ite]

omit [PartialOrder A] [StarOrderedRing A] in
lemma paulsenOperatorMap_one (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1)
    (T : A →ₗ[ℂ] (H →L[ℂ] H)) :
    paulsenOperatorMap f T ⟨1, paulsenSystem_one⟩ = 1 := by
  change doubleMatrixHom (H := H)
    (paulsenSystemMap f T ⟨1, paulsenSystem_one⟩) = 1
  rw [paulsenSystemMap_one f hf, matrixDouble_one]

variable [Nontrivial A]

lemma paulsenOperatorMap_positive (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1)
    (T : A →ₗ[ℂ] (H →L[ℂ] H))
    (hT : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X.map T‖ ≤ ‖X‖)
    (n : ℕ) (X : operatorSystemMatrices (paulsenSystem A) n) (hX : 0 ≤ X.val) :
    0 ≤ operatorSystemAmplification (paulsenSystem A) (paulsenOperatorMap f T) n X := by
  have h := paulsenSystemMap_positive f hf T hT n X hX
  exact map_nonneg (CStarMatrix.mapₙₐ (doubleMatrixHom (H := H))) h

theorem exists_paulsen_extension_oai [Nontrivial H] (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1)
    (T : A →ₗ[ℂ] (H →L[ℂ] H))
    (hT : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X.map T‖ ≤ ‖X‖) :
    ∃ Φ : CompletelyPositiveMap (Mat A) (HilbertDouble H →L[ℂ] HilbertDouble H),
      Φ 1 = 1 ∧ ∀ X : paulsenSystem A, Φ (X : Mat A) = paulsenOperatorMap f T X := by
  obtain ⟨Φ, hΦ, _, hrest⟩ := exists_unital_completelyPositive_extension (paulsenSystem A)
    paulsenSystem_one paulsenSystem_star (paulsenOperatorMap f T)
    (paulsenOperatorMap_one f hf T) (paulsenOperatorMap_positive f hf T hT)
  exact ⟨Φ, hΦ, hrest⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.BoundedHochschild.KadisonRingrose.exists_paulsen_extension_oai.{u_1, u_2} := @OAI.BoundedHochschild.KadisonRingrose.exists_paulsen_extension_oai.{u_1, u_2}
