-- Prove2me | solution 1 for OAI.Kadison.TracialGNS.word_multiplicity_both
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:29:08.444684+00:00
-- url     : https://prove2.me/submissions/6bdd00ef-e375-4291-aa08-14b70542e9fe

import Mathlib
import Definitions.Def_OAIQ039C040
import Definitions.Def_OAIQ039C047
import Definitions.Def_OAIQ039C048

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

lemma norm_insertLeft_le (x : E) : ‖insertLeft (J := J) x‖ ≤ ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  simp only [insertLeft_apply, norm_pair, le_refl]

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

lemma pair_inner_ext (z w : Completion (E ⊗[ℂ] J))
    (h : ∀ x a, inner ℂ (pair x a) z = inner ℂ (pair x a) w) : z = w := by
  apply sub_eq_zero.mp
  apply eq_zero_of_pair_inner
  intro x a
  rw [inner_sub_right, h, sub_self]

end Kadison.HilbertTensor
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

lemma multiplicityCompression_inner [CompleteSpace E] [CompleteSpace J]
    (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (E ⊗[ℂ] J)) (v : E) (a b : J) :
    inner ℂ b (multiplicityCompression T v a) = inner ℂ v (scalarSlice T a b v) := by
  simp only [multiplicityCompression, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, insertLeft_apply, scalarSlice_inner]

lemma norm_multiplicityCompression_le [CompleteSpace J]
    (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (E ⊗[ℂ] J)) (v : E) (hv : ‖v‖ = 1) :
    ‖multiplicityCompression T v‖ ≤ ‖T‖ := by
  have hi : ‖insertLeft (J := J) v‖ ≤ 1 := by simpa only [hv] using norm_insertLeft_le (J := J) v
  have hia : ‖(insertLeft (J := J) v).adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hi
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)).trans
      (calc
        ‖(insertLeft (J := J) v).adjoint‖ * ‖T‖ * ‖insertLeft (J := J) v‖
            ≤ (1 * ‖T‖) * ‖insertLeft (J := J) v‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hia (norm_nonneg T))
            (norm_nonneg (insertLeft (J := J) v))
        _ ≤ ‖T‖ := by
          simpa only [one_mul, mul_one] using mul_le_mul_of_nonneg_left hi (norm_nonneg T)))

theorem repeated_pair [CompleteSpace E] [CompleteSpace J]
    {ι : Type*} [Fintype ι]
    (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (E ⊗[ℂ] J))
    (U : ι → E →L[ℂ] E)
    (hclass : ∀ a b : J, ∃ c : ι → ℂ, scalarSlice T a b = ∑ i, c i • U i)
    (v w : E) (hv : ‖v‖ = 1) (hUv : ∀ i, U i v = v) (hUw : ∀ i, U i w = w)
    (a : J) : T (pair w a) = pair w (multiplicityCompression T v a) := by
  classical
  apply pair_inner_ext
  intro x b
  obtain ⟨c, hc⟩ := hclass a b
  have hc_v : scalarSlice T a b v = (∑ i, c i) • v := by
    simp only [hc, sum_apply, smul_apply, hUv, Finset.sum_smul]
  have hc_w : scalarSlice T a b w = (∑ i, c i) • w := by
    simp only [hc, sum_apply, smul_apply, hUw, Finset.sum_smul]
  have hsum : inner ℂ b (multiplicityCompression T v a) = ∑ i, c i := by
    rw [multiplicityCompression_inner, hc_v, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hv]
    simp
  rw [← scalarSlice_inner, hc_w, inner_smul_right, inner_pair, hsum]
  exact mul_comm _ _

end Kadison.HilbertTensor
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TensorAdjoints
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

open ContinuousLinearMap

variable {E F J K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

lemma scalarSlice_adjoint
    (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (F ⊗[ℂ] K))
    (a : K) (b : J) : scalarSlice T.adjoint a b = (scalarSlice T b a).adjoint := by
  simp only [scalarSlice, adjoint_comp, adjoint_adjoint, ContinuousLinearMap.comp_assoc]

omit [CompleteSpace E] in
lemma multiplicityCompression_adjoint [CompleteSpace J]
    (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (E ⊗[ℂ] J)) (v : E) :
    multiplicityCompression T.adjoint v = (multiplicityCompression T v).adjoint := by
  simp only [multiplicityCompression, adjoint_comp, adjoint_adjoint, ContinuousLinearMap.comp_assoc]

lemma isometry_adjoint_fix (U : E →ₗᵢ[ℂ] E) (v : E) (h : U v = v) :
    U.toContinuousLinearMap.adjoint v = v := by
  conv_lhs => rw [← h]
  exact congrArg (fun T : E →L[ℂ] E => T v) U.adjoint_comp_self

lemma repeated_pair_adjoint [CompleteSpace J] {ι : Type*} [Fintype ι]
    (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (E ⊗[ℂ] J))
    (U : ι → E →ₗᵢ[ℂ] E)
    (hclass : ∀ a b : J, ∃ c : ι → ℂ,
      scalarSlice T a b = ∑ i, c i • (U i).toContinuousLinearMap)
    (v w : E) (hv : ‖v‖ = 1) (hUv : ∀ i, U i v = v) (hUw : ∀ i, U i w = w)
    (a : J) : T.adjoint (pair w a) = pair w ((multiplicityCompression T v).adjoint a) := by
  rw [← multiplicityCompression_adjoint]
  have hclassAdj : ∀ b c : J, ∃ d : ι → ℂ,
      scalarSlice T.adjoint b c = ∑ i, d i • (U i).toContinuousLinearMap.adjoint := by
    intro b c
    obtain ⟨d, hd⟩ := hclass c b
    refine ⟨fun i => star (d i), ?_⟩
    rw [scalarSlice_adjoint, hd]
    simp only [map_sum, map_smulₛₗ, starRingEnd_apply]
  exact repeated_pair T.adjoint (fun i => (U i).toContinuousLinearMap.adjoint) hclassAdj v w hv
    (fun i => isometry_adjoint_fix (U i) v (hUv i))
    (fun i => isometry_adjoint_fix (U i) w (hUw i)) a

end Kadison.HilbertTensor
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry9
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

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)

include h1 in
theorem word_multiplicity_both_oai {k : ℕ} {J : Type*}
    [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (T : Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J) →L[ℂ]
      Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J))
    (hclass : ∀ a b : J, ∃ c : Equiv.Perm (Fin k) → ℂ,
      scalarSlice T a b = ∑ σ, c σ •
        (wordReindex (fullSpace τ) (zeroSpace τ) σ).toContinuousLinearMap)
    (z : zeroSpace τ) (hz : ‖z‖ = 1) :
    ∃ B : J →L[ℂ] J, ‖B‖ ≤ ‖T‖ ∧
      (∀ (d : fullSpace τ) (x : zeroSpace τ) (a : J),
        T (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a) =
          pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) (B a)) ∧
      (∀ (d : fullSpace τ) (x : zeroSpace τ) (a : J),
        T.adjoint (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a) =
          pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) (B.adjoint a)) := by
  let v := word (fullSpace τ) (zeroSpace τ) k (vacuum τ) (fun _ => z)
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_word, vacuum_norm τ h1, hz, Finset.prod_const_one, mul_one]
  refine ⟨multiplicityCompression T v, norm_multiplicityCompression_le T v hv, ?_, ?_⟩
  · intro d x a
    apply repeated_pair T (fun σ : Equiv.Perm (Fin k) =>
      (wordReindex (fullSpace τ) (zeroSpace τ) σ).toContinuousLinearMap) hclass v _ hv
    · intro σ
      simp only [v, LinearIsometry.coe_toContinuousLinearMap, wordReindex_word, Function.comp_def]
    · intro σ
      simp only [LinearIsometry.coe_toContinuousLinearMap, wordReindex_word, Function.comp_def]
  · intro d x a
    apply repeated_pair_adjoint T (wordReindex (fullSpace τ) (zeroSpace τ)) hclass v _ hv
    · intro σ
      simp only [v, wordReindex_word, Function.comp_def]
    · intro σ
      simp only [wordReindex_word, Function.comp_def]

end Kadison.TracialGNS
end

end OAI
end

theorem solution.{u_2} : type_of% @OAI.Kadison.TracialGNS.word_multiplicity_both_oai.{u_2} := @OAI.Kadison.TracialGNS.word_multiplicity_both_oai.{u_2}
