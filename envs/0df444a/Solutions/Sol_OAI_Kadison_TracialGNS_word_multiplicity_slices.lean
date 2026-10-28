-- Prove2me | solution 1 for OAI.Kadison.TracialGNS.word_multiplicity_slices
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:51:21.027987+00:00
-- url     : https://prove2.me/submissions/26c005c8-9f5b-43b7-9b30-58eb44374b0c

import Mathlib
import Definitions.Def_OAIQ039C058
import Theorems.Thm_OAI_Kadison_PreHilbert_operator_ext_dense_stages
import Theorems.Thm_OAI_Kadison_TracialGNS_stageWord_inner_classification

section
-- module Solutions.OAIQ039_CM.Commutator_CenteredSpace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace

namespace Kadison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma center_vacuum (Ω : E) : center Ω Ω = 0 := by
  apply Subtype.ext
  change (ℂ ∙ Ω)ᗮ.starProjection Ω = (0 : E)
  exact Submodule.starProjection_orthogonalComplement_singleton_eq_zero Ω

lemma center_centered (Ω : E) (x : centeredSpace Ω) : center Ω (x : E) = x :=
  (centeredSpace Ω).orthogonalProjectionOnto_mem_subspace_eq_self x

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace

namespace Kadison.TracialGNS

open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

omit [Nonempty I] in
lemma stage_vacuum : stageVector τ φ 1 = vacuum τ := by
  change algebraVector τ (φ 1) = vacuum τ
  rw [map_one]
  rfl

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TensorDevelopment
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter

namespace Kadison

namespace HilbertTensor

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

variable {G H : Type*}
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

lemma completion_ext {f g : Completion (E ⊗[𝕜] G) →L[𝕜] H}
    (h : ∀ (x : E) (y : G), f ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] G) : Completion _) =
      g ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] G) : Completion _)) : f = g := by
  ext z
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih z =>
    induction z using OAI.tensorInductionOn with
    | tmul x y => exact h x y
    | add x y hx hy => simp only [Completion.coe_add, map_add, hx, hy]

@[simp] lemma map_one_one : map (1 : E →L[𝕜] E) (1 : F →L[𝕜] F) = 1 := by
  apply completion_ext
  intro x y
  simp

end HilbertTensor

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StageDensity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.TracialGNS

open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b) = τ (b*a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

omit [Nonempty I] in
lemma centeredStageVector_sub_trace (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)
    (a : Matrix I I ℂ) :
    centeredStageVector τ φ (a - ((Fintype.card I : ℂ)⁻¹ * a.trace) • 1) =
      centeredStageVector τ φ a := by
  rw [map_sub, map_smul]
  have hz : centeredStageVector τ φ 1 = 0 := by
    change center (vacuum τ) (stageVector τ φ 1) = 0
    rw [stage_vacuum, center_vacuum]
  rw [hz, smul_zero, sub_zero]

lemma trace_sub_normalized_trace (a : Matrix I I ℂ) :
    (a - ((Fintype.card I : ℂ)⁻¹ * a.trace) • 1).trace = 0 := by
  have hn : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  field_simp
  simp

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
  [∀ n, Nonempty (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)

lemma centeredStageSet_eq (n : ℕ) :
    centeredStageSet τ I φ n = (center (vacuum τ)) '' stageSet τ I φ n := by
  ext x
  constructor
  · rintro ⟨a, _, rfl⟩
    exact ⟨stageVector τ (φ n) a, ⟨a, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a - ((Fintype.card (I n) : ℂ)⁻¹ * a.trace) • 1,
      trace_sub_normalized_trace a, centeredStageVector_sub_trace τ (φ n) a⟩

lemma dense_centeredStageSet (hd : Dense (⋃ n, stageSet τ I φ n)) :
    Dense (⋃ n, centeredStageSet τ I φ n) := by
  have hs : Function.Surjective (center (vacuum τ)) :=
    fun x => ⟨x, center_centered (vacuum τ) x⟩
  have hi : (⋃ n, centeredStageSet τ I φ n) =
      (center (vacuum τ)) '' (⋃ n, stageSet τ I φ n) := by
    simp only [centeredStageSet_eq, Set.image_iUnion]
  rw [hi]
  exact hs.denseRange.dense_image (center (vacuum τ)).continuous hd

variable (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)

variable (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)

omit [∀ n, Nonempty (I n)] in
include e he in
lemma stageSet_mono : Monotone (stageSet τ I φ) := by
  intro n m hnm x hx
  obtain ⟨a, rfl⟩ := hx
  refine ⟨e hnm a, ?_⟩
  change algebraVector τ (φ m (e hnm a)) = algebraVector τ (φ n a)
  rw [he]

include e he in
lemma centeredStageSet_mono : Monotone (centeredStageSet τ I φ) := by
  intro n m hnm
  rw [centeredStageSet_eq, centeredStageSet_eq]
  exact Set.image_mono (stageSet_mono τ I φ e he hnm)

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WordPermutations
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.PreHilbert

open UniformSpace

open scoped TensorProduct

lemma wordReindex_inner (E F : PreHilbert) {k l : ℕ} (b : Fin k ≃ Fin l)
    (d c : E) (x : Fin k → F) (y : Fin l → F) :
    inner ℂ (word E F l c y) (wordReindex E F b (word E F k d x)) =
      inner ℂ c d * ∏ i, inner ℂ (y (b i)) (x i) := by
  rw [wordReindex_word, inner_word]
  congr 1
  simpa using (Equiv.prod_comp b (fun j => inner ℂ (y j) (x (b.symm j)))).symm

end Kadison.PreHilbert
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry7
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.TracialGNS

open PreHilbert

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b) = τ (b*a)) (h1 : τ 1 = 1)

variable {k l : ℕ}

include h1 in
theorem word_intertwiner (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
    wordSpace (fullSpace τ) (zeroSpace τ) l)
    (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
    (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
    (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (hd : Dense (⋃ n, stageSet τ I φ n))
    (hY : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
      Y.comp (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap =
        (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap.comp Y)
    (hleft : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y) :
    ∃ c₀ : (Fin k ≃ Fin l) → ℂ,
      Y = ∑ b : Fin k ≃ Fin l, c₀ b •
        (wordReindex (fullSpace τ) (zeroSpace τ) b).toContinuousLinearMap := by
  classical
  obtain ⟨c₀, hc₀⟩ := stageWord_inner_classification τ hτ h1 Y I φ e he hsize hY hleft
  refine ⟨c₀, ?_⟩
  apply operator_ext_dense_stages (fullSpace τ) (zeroSpace τ) k l
    (stageSet τ I φ) (centeredStageSet τ I φ)
    (stageSet_mono τ I φ e he) (centeredStageSet_mono τ I φ e he)
    hd (dense_centeredStageSet τ I φ hd)
  intro n d hd x hx c hc y hy
  obtain ⟨d, rfl⟩ := hd
  obtain ⟨c, rfl⟩ := hc
  choose a ha hax using hx
  choose b hb hby using hy
  have hxa : x = fun i => centeredStageVector τ (φ n) (a i) := funext (fun i => (hax i).symm)
  have hyb : y = fun i => centeredStageVector τ (φ n) (b i) := funext (fun i => (hby i).symm)
  rw [hxa, hyb, hc₀ n d c a b ha hb]
  simp only [sum_apply, smul_apply,
    inner_sum, inner_smul_right, LinearIsometry.coe_toContinuousLinearMap, wordReindex_inner]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TensorMultiplicity2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.HilbertTensor

variable {E F J K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

lemma insertRight_adjoint_map [CompleteSpace E] [CompleteSpace F]
    (b : J) (f : E →L[ℂ] F) :
    (insertRight b).adjoint.comp (map f (1 : J →L[ℂ] J)) =
      f.comp (insertRight b).adjoint := by
  apply completion_ext
  intro x a
  change (insertRight b).adjoint (map f (1 : J →L[ℂ] J) (pair x a)) =
    f ((insertRight b).adjoint (pair x a))
  simp only [map_pair, one_apply_eq_self, insertRight_adjoint_pair, map_smul]

lemma scalarSlice_covariant [CompleteSpace E] [CompleteSpace F]
    (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (F ⊗[ℂ] K))
    (f : E →L[ℂ] E) (g : F →L[ℂ] F)
    (h : T.comp (map f (1 : J →L[ℂ] J)) = (map g (1 : K →L[ℂ] K)).comp T)
    (a : J) (b : K) : (scalarSlice T a b).comp f = g.comp (scalarSlice T a b) := by
  ext x
  have ht := congrArg (fun R : Completion (E ⊗[ℂ] J) →L[ℂ]
    Completion (F ⊗[ℂ] K) => R (pair x a)) h
  have ho := congrArg (fun R : Completion (F ⊗[ℂ] K) →L[ℂ] F =>
    R (T (pair x a))) (insertRight_adjoint_map b g)
  simp only [ContinuousLinearMap.comp_apply, map_pair, one_apply_eq_self] at ht
  change (insertRight b).adjoint (T (pair (f x) a)) =
    g ((insertRight b).adjoint (T (pair x a)))
  rw [ht]
  exact ho

end Kadison.HilbertTensor
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry8
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.TracialGNS

open PreHilbert HilbertTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b) = τ (b*a)) (h1 : τ 1 = 1)

variable {k l : ℕ} {J K : Type*}
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

include h1 in
theorem word_multiplicity_slices_oai
    (T : Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J) →L[ℂ]
      Completion (wordSpace (fullSpace τ) (zeroSpace τ) l ⊗[ℂ] K))
    (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
    (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
    (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (hd : Dense (⋃ n, stageSet τ I φ n))
    (hT : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
      T.comp (HilbertTensor.map (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap 1) =
        (HilbertTensor.map (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap 1).comp T)
    (hleft : ∀ a : A, T.comp (HilbertTensor.map (wordLeft τ a k) 1) =
      (HilbertTensor.map (wordLeft τ a l) 1).comp T) :
    ∀ a : J, ∀ b : K, ∃ c : (Fin k ≃ Fin l) → ℂ,
      scalarSlice T a b = ∑ σ, c σ •
        (wordReindex (fullSpace τ) (zeroSpace τ) σ).toContinuousLinearMap := by
  intro a b
  apply word_intertwiner τ hτ h1 (scalarSlice T a b) I φ e he hsize hd
  · intro n u
    exact scalarSlice_covariant T _ _ (hT n u) a b
  · intro x
    exact scalarSlice_covariant T _ _ (hleft x) a b

end Kadison.TracialGNS
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.TracialGNS.word_multiplicity_slices_oai.{u_1, u_2, u_3} := @OAI.Kadison.TracialGNS.word_multiplicity_slices_oai.{u_1, u_2, u_3}
