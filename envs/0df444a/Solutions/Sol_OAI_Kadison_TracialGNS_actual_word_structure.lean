-- Prove2me | solution 1 for OAI.Kadison.TracialGNS.actual_word_structure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:10:49.478298+00:00
-- url     : https://prove2.me/submissions/b5816390-213c-4b1a-971f-cd202cc8a379

import Mathlib
import Definitions.Def_OAIQ039C063
import Definitions.Def_OAIQ039C066
import Definitions.Def_OAIQ039C067
import Theorems.Thm_OAI_Kadison_TracialGNS_normalizedLetter_orthonormal
import Theorems.Thm_OAI_Kadison_TracialGNS_word_multiplicity_both
import Theorems.Thm_OAI_Kadison_TracialGNS_word_multiplicity_slices

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry15
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
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap

namespace Kadison.ActualHilbertSum

variable {ι H : Type*} (E : ι → Type*)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)]

variable (U : ∀ i, E i →ₗᵢ[ℂ] H)

lemma norm_project_le (i : ι) : ‖project E U i‖ ≤ 1 := by
  rw [project, adjoint.norm_map]
  exact (U i).norm_toContinuousLinearMap_le

lemma norm_block_le (T : H →L[ℂ] H) (i j : ι) : ‖block E U T i j‖ ≤ ‖T‖ := by
  calc
    ‖block E U T i j‖ ≤ (‖project E U i‖ * ‖T‖) * ‖insert E U j‖ :=
      (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right
        (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖T‖) * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right (norm_project_le E U i) (norm_nonneg T))
      (U j).norm_toContinuousLinearMap_le (norm_nonneg _)
      (by simp)
    _ = ‖T‖ := by ring

variable (hU : IsHilbertSum ℂ E U)

lemma project_coordinates (i : ι) (x : H) :
    project E U i x = hU.linearIsometryEquiv x i := by
  classical
  apply ext_inner_left ℂ
  intro y
  rw [project, adjoint_inner_right]
  change inner ℂ (U i y) x = _
  rw [← hU.linearIsometryEquiv_symm_apply_single y]
  have := hU.linearIsometryEquiv.symm.inner_map_map
    (lp.single 2 i y) (hU.linearIsometryEquiv x)
  simpa only [LinearIsometryEquiv.symm_apply_apply, lp.inner_single_left] using this

include hU in
lemma ext_vectors {x y : H} (h : ∀ i, project E U i x=project E U i y) : x=y := by
  apply hU.linearIsometryEquiv.injective
  ext i
  simpa only [project_coordinates E U hU] using h i

include hU in
lemma project_insert_ne {i j : ι} (hij : i≠j) :
    (project E U i).comp (insert E U j) = 0 := by
  ext x
  apply ext_inner_left ℂ
  intro y
  simp only [comp_apply, project, adjoint_inner_right, insert,
    LinearIsometry.coe_toContinuousLinearMap, zero_apply, inner_zero_right]
  exact hU.OrthogonalFamily hij y x

include hU in
lemma reduces_of_offdiagonal (T : H →L[ℂ] H)
    (h : ∀ i j, i≠j → block E U T i j=0) (j : ι) :
    T.comp (insert E U j)=(insert E U j).comp (block E U T j j) := by
  ext x
  apply ext_vectors E U hU
  intro i
  by_cases hij : i=j
  · subst i
    change block E U T j j x = ((project E U j).comp (insert E U j)) _
    rw [project_insert,one_apply_eq_self]
    rfl
  · change block E U T i j x = ((project E U i).comp (insert E U j)) _
    rw [h i j hij,project_insert_ne E U hU hij]
    rfl

include hU in
lemma adjoint_reduces_of_offdiagonal (T : H →L[ℂ] H)
    (h : ∀ i j, i≠j → block E U T i j=0) (j : ι) :
    T.adjoint.comp (insert E U j)=(insert E U j).comp (block E U T j j).adjoint := by
  rw [←block_adjoint]
  apply reduces_of_offdiagonal E U hU
  intro i k hik
  rw [block_adjoint,h k i hik.symm,map_zero]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

include hU in
lemma project_covariant (L : H →L[ℂ] H) (l : ∀ i, E i →L[ℂ] E i)
    (h : ∀ i, L.comp (insert E U i)=(insert E U i).comp (l i)) (i : ι) :
    (project E U i).comp L=(l i).comp (project E U i) := by
  apply map_ext E U hU
  intro j
  rw [comp_assoc, h j, ←comp_assoc, comp_assoc (l i)]
  by_cases hij : i=j
  · subst i
    rw [project_insert]
    ext x
    rfl
  · rw [project_insert_ne E U hU hij]
    simp

omit hU in
lemma block_covariant (T L R : H →L[ℂ] H) (l r : ∀ i, E i →L[ℂ] E i)
    (h : T.comp L=R.comp T)
    (hL : ∀ j, L.comp (insert E U j)=(insert E U j).comp (l j))
    (hR : ∀ i, (project E U i).comp R=(r i).comp (project E U i))
    (i j : ι) : (block E U T i j).comp (l j)=(r i).comp (block E U T i j) := by
  simp only [block,comp_assoc]
  rw [←hL,←comp_assoc T,h,comp_assoc R,←comp_assoc (project E U i),hR,comp_assoc]

include hU in
lemma block_covariant_of_insert (T L : H →L[ℂ] H) (l : ∀ i, E i →L[ℂ] E i)
    (h : T.comp L=L.comp T)
    (hL : ∀ j, L.comp (insert E U j)=(insert E U j).comp (l j)) (i j : ι) :
    (block E U T i j).comp (l j)=(l i).comp (block E U T i j) :=
  block_covariant E U T L L l l h hL (project_covariant E U hU L l hL) i j

end Kadison.ActualHilbertSum
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
-- module Solutions.OAIQ039_CM.Commutator_TensorMultiplicity
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

lemma scalarSlice_inner [CompleteSpace F] (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (F ⊗[ℂ] K))
    (a : J) (b : K) (x : E) (y : F) :
    inner ℂ y (scalarSlice T a b x) = inner ℂ (pair y b) (T (pair x a)) := by
  simp only [scalarSlice, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, insertRight_apply]

lemma eq_zero_of_pair_inner (z : Completion (E ⊗[ℂ] J))
    (h : ∀ x a, inner ℂ (pair x a) z = 0) : z = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have hz (y : Completion (E ⊗[ℂ] J)) : inner ℂ y z = 0 := by
    induction y using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) continuous_const
    | ih y =>
      induction y using OAI.tensorInductionOn with
      | tmul x a => exact h x a
      | add x y hx hy => simp only [Completion.coe_add, inner_add_left, hx, hy, add_zero]
  exact hz z

lemma eq_zero_of_scalarSlice [CompleteSpace F]
    (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (F ⊗[ℂ] K))
    (h : ∀ a b, scalarSlice T a b = 0) : T = 0 := by
  apply completion_ext
  intro x a
  change T (pair x a) = 0
  apply eq_zero_of_pair_inner
  intro y b
  rw [← scalarSlice_inner, h, zero_apply, inner_zero_right]

end Kadison.HilbertTensor
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry8
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.TracialGNS.sumLevelComplete _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

theorem word_multiplicity_offlevel
    (T : Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J) →L[ℂ]
      Completion (wordSpace (fullSpace τ) (zeroSpace τ) l ⊗[ℂ] K))
    (hkl : k ≠ l)
    (hclass : ∀ a : J, ∀ b : K, ∃ c : (Fin k ≃ Fin l) → ℂ,
      scalarSlice T a b = ∑ σ, c σ •
        (wordReindex (fullSpace τ) (zeroSpace τ) σ).toContinuousLinearMap) : T = 0 := by
  classical
  let : IsEmpty (Fin k ≃ Fin l) := ⟨fun b => hkl (by simpa using Fintype.card_congr b)⟩
  apply eq_zero_of_scalarSlice
  intro a b
  obtain ⟨c, hc⟩ := hclass a b
  simpa only [Finset.univ_eq_empty, Finset.sum_empty] using hc

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StageGeneration
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

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)

variable (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)

variable (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)

include e he in
lemma operatorStage_mono : Monotone (operatorStage τ I φ) := by
  intro n m hnm x hx
  obtain ⟨a, rfl⟩ := hx
  refine ⟨e hnm a, ?_⟩
  change τ.gnsStarAlgHom (φ m (e hnm a)) = τ.gnsStarAlgHom (φ n a)
  rw [he]

include e he in
lemma orbit_stageAlgebra :
    (orbitSubmodule (stageAlgebra τ I φ) (vacuum τ) : Set τ.GNS) =
      ⋃ n, stageSet τ I φ n := by
  have hS : (stageAlgebra τ I φ : Set (τ.GNS →L[ℂ] τ.GNS)) =
      ⋃ n, (operatorStage τ I φ n : Set (τ.GNS →L[ℂ] τ.GNS)) :=
    StarSubalgebra.coe_iSup_of_directed (operatorStage_mono τ I φ e he).directed_le
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    change a ∈ (stageAlgebra τ I φ : Set (τ.GNS →L[ℂ] τ.GNS)) at ha
    rw [hS] at ha
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
    obtain ⟨b, rfl⟩ := hn
    refine Set.mem_iUnion.mpr ⟨n, b, ?_⟩
    exact (left_vacuum τ (φ n b)).symm
  · intro hx
    obtain ⟨n, b, rfl⟩ := Set.mem_iUnion.mp hx
    refine ⟨τ.gnsStarAlgHom (φ n b), ?_, left_vacuum τ (φ n b)⟩
    change τ.gnsStarAlgHom (φ n b) ∈ (stageAlgebra τ I φ : Set (τ.GNS →L[ℂ] τ.GNS))
    rw [hS]
    exact Set.mem_iUnion.mpr ⟨n, b, rfl⟩

include e he in
theorem dense_stages_of_bicommutant_generation
    (hgen : ∀ a : A, τ.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer
        (stageAlgebra τ I φ : Set (τ.GNS →L[ℂ] τ.GNS)))) :
    Dense (⋃ n, stageSet τ I φ n) := by
  have hbase (a : A) : algebraVector τ a ∈ closure (⋃ n, stageSet τ I φ n) := by
    have h := bicommutant_mem_cyclicSubspace (stageAlgebra τ I φ) (hgen a) (vacuum τ)
    rw [left_vacuum] at h
    change algebraVector τ a ∈ closure (orbitSubmodule (stageAlgebra τ I φ) (vacuum τ) : Set τ.GNS) at h
    rwa [orbit_stageAlgebra τ I φ e he] at h
  intro x
  exact (algebraVector_dense τ).induction (fun _ ⟨a, ha⟩ => ha ▸ hbase a) isClosed_closure x

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry9
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.TracialGNS.sumLevelComplete _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)

include hτ h1 φ in
lemma exists_unit_centered_letter (hsize : ∃ n, 2 ≤ Fintype.card (I n)) :
    ∃ z : zeroSpace τ, ‖z‖ = 1 := by
  classical
  obtain ⟨n, hn⟩ := hsize
  have hc : Fintype.card (Fin 2) ≤ Fintype.card (I n) := by simpa using hn
  obtain ⟨b⟩ := (Function.Embedding.nonempty_of_card_le hc)
  let a : Unit ↪ I n := ⟨fun _ => b 1, fun _ _ _ => Subsingleton.elim _ _⟩
  have ha : ∀ j, a j ≠ b 0 := fun _ => b.injective.ne (by decide : (1 : Fin 2) ≠ 0)
  exact ⟨centeredStageVector τ (φ n) (MatrixAlphabet.normalizedLetter (b 0) (b 1)),
    (normalizedLetter_orthonormal τ hτ h1 (φ n) (b 0) a ha).norm_eq_one ()⟩

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_InvariantSum
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
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
open scoped InnerProductSpace ENNReal
open scoped ComplexOrder InnerProductSpace TensorProduct
open UniformSpace ContinuousLinearMap

namespace Kadison.TracialGNS

open PreHilbert HilbertTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a)) (h1 : τ 1=1)

variable (J : ℕ → Type*) [∀ k, NormedAddCommGroup (J k)]
  [∀ k, InnerProductSpace ℂ (J k)] [∀ k, CompleteSpace (J k)]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : ∀ k, sumLevel τ J k →ₗᵢ[ℂ] H) (hU : IsHilbertSum ℂ (sumLevel τ J) U)

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)

variable (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)

variable (he : ∀ n m (h : n ≤ m) a, φ m (e h a)=φ n a)

variable (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))

variable (hgen : ∀ a : A, τ.gnsStarAlgHom a ∈ Set.centralizer (Set.centralizer
  (stageAlgebra τ I φ : Set (τ.GNS →L[ℂ] τ.GNS))))

variable (L : A → H →L[ℂ] H)

variable (W : ∀ n, unitary (Matrix (I n) (I n) ℂ) → H →L[ℂ] H)

variable (hL : ∀ a k, (L a).comp (U k).toContinuousLinearMap =
  (U k).toContinuousLinearMap.comp (sumLeft τ J a k))

variable (hW : ∀ n u k, (W n u).comp (U k).toContinuousLinearMap =
  (U k).toContinuousLinearMap.comp
    (sumConjugation τ hτ J (stageUnitary (φ n) u) k))

variable (G : H →L[ℂ] H)

variable (hGL : ∀ a, G.comp (L a)=(L a).comp G)

variable (hGW : ∀ n u, G.comp (W n u)=(W n u).comp G)

omit [∀ k, CompleteSpace (J k)] [∀ n, Nonempty (I n)] in
include hU hW hGW in
lemma actual_block_conjugation (k l n : ℕ) (u : unitary (Matrix (I n) (I n) ℂ)) :
    (ActualHilbertSum.block (sumLevel τ J) U G l k).comp
      (sumConjugation τ hτ J (stageUnitary (φ n) u) k) =
    (sumConjugation τ hτ J (stageUnitary (φ n) u) l).comp
      (ActualHilbertSum.block (sumLevel τ J) U G l k) := by
  exact ActualHilbertSum.block_covariant_of_insert (sumLevel τ J) U hU G (W n u)
    (fun k => sumConjugation τ hτ J (stageUnitary (φ n) u) k)
    (hGW n u) (hW n u) l k

omit [∀ k, CompleteSpace (J k)] in
include hU hL hGL in
lemma actual_block_left (k l : ℕ) (a : A) :
    (ActualHilbertSum.block (sumLevel τ J) U G l k).comp (sumLeft τ J a k) =
    (sumLeft τ J a l).comp (ActualHilbertSum.block (sumLevel τ J) U G l k) := by
  exact ActualHilbertSum.block_covariant_of_insert (sumLevel τ J) U hU G (L a)
    (fun k => sumLeft τ J a k) (hGL a) (hL a) l k

omit [∀ k, CompleteSpace (J k)] in
include h1 hU he hsize hgen hL hW hGL hGW in
lemma actual_block_classification (k l : ℕ) :
    ∀ a : J k, ∀ b : J l, ∃ c : (Fin k ≃ Fin l) → ℂ,
      scalarSlice (ActualHilbertSum.block (sumLevel τ J) U G l k) a b =
        ∑ σ, c σ • (wordReindex (fullSpace τ) (zeroSpace τ) σ).toContinuousLinearMap := by
  exact word_multiplicity_slices τ hτ h1 _ I φ e he hsize
    (dense_stages_of_bicommutant_generation τ I φ e he hgen)
    (actual_block_conjugation τ hτ J U hU I φ W hW G hGW k l)
    (actual_block_left τ J U hU L hL G hGL k l)

include h1 hU he hsize hgen hL hW hGL hGW in
theorem actual_word_structure_oai : ∃ B : ∀ k, J k →L[ℂ] J k,
    (∀ k, ‖B k‖ ≤ ‖G‖) ∧
    (∀ k (d : fullSpace τ) (x : zeroSpace τ) (a : J k),
      G (U k (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a)) =
        U k (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) (B k a))) ∧
    (∀ k (d : fullSpace τ) (x : zeroSpace τ) (a : J k),
      G.adjoint (U k (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a)) =
        U k (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) ((B k).adjoint a))) := by
  classical
  have hclass := actual_block_classification τ hτ h1 J U hU I φ e he hsize hgen L W hL hW G hGL hGW
  have hoff : ∀ i j, i≠j → ActualHilbertSum.block (sumLevel τ J) U G i j=0 := by
    intro i j hij
    exact word_multiplicity_offlevel τ _ hij.symm (hclass j i)
  obtain ⟨z,hz⟩ := exists_unit_centered_letter τ hτ h1 I φ (by
    obtain ⟨n,_,hn⟩ := hsize 0 2
    exact ⟨n,hn⟩)
  have hex (k : ℕ) := word_multiplicity_both τ h1
    (ActualHilbertSum.block (sumLevel τ J) U G k k) (hclass k k) z hz
  choose B hB hG hGa using hex
  refine ⟨B,fun k => (hB k).trans (ActualHilbertSum.norm_block_le (sumLevel τ J) U G k k),?_,?_⟩
  · intro k d x a
    have hr := congrArg (fun T : sumLevel τ J k →L[ℂ] H =>
      T (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a))
      (ActualHilbertSum.reduces_of_offdiagonal (sumLevel τ J) U hU G hoff k)
    exact hr.trans (congrArg (U k) (hG k d x a))
  · intro k d x a
    have hr := congrArg (fun T : sumLevel τ J k →L[ℂ] H =>
      T (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a))
      (ActualHilbertSum.adjoint_reduces_of_offdiagonal (sumLevel τ J) U hU G hoff k)
    exact hr.trans (congrArg (U k) (hGa k d x a))

end Kadison.TracialGNS
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.TracialGNS.actual_word_structure_oai.{u_1, u_2, u_3} := @OAI.Kadison.TracialGNS.actual_word_structure_oai.{u_1, u_2, u_3}
