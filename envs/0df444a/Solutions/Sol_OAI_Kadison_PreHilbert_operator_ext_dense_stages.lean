-- Prove2me | solution 1 for OAI.Kadison.PreHilbert.operator_ext_dense_stages
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:12:30.986989+00:00
-- url     : https://prove2.me/submissions/d60c5dd9-69f4-4c6e-ba19-9965a3b4ff97

import Mathlib
import Definitions.Def_OAIQ039C040

section
-- module Solutions.OAIQ039_CM.Commutator_WordTopology
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

open UniformSpace TensorProduct

lemma eq_zero_of_word_inner (E F : PreHilbert) (n : ℕ) (z : wordSpace E F n)
    (hz : ∀ d x, inner ℂ (word E F n d x) z = 0) : z = 0 := by
  apply Completion.denseRange_coe.eq_zero_of_inner_right ℂ
  intro a
  induction a using OAI.tensorInductionOn with
  | add a b ha hb => simp [Completion.coe_add, inner_add_left, ha, hb]
  | tmul d x =>
    have hx : x ∈ Submodule.span ℂ (Set.range (pure F n)) := by
      rw [span_pure]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      exact hz d v
    | zero => simp only [TensorProduct.tmul_zero, Completion.coe_zero, inner_zero_left]
    | add x y _ _ hx hy => simp [TensorProduct.tmul_add, Completion.coe_add, inner_add_left, hx, hy]
    | smul c x _ hx => simp only [TensorProduct.tmul_smul, Completion.coe_smul, inner_smul_left, hx, mul_zero]

lemma continuousLinearMap_ext_word (E F : PreHilbert) (n : ℕ) {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (T U : wordSpace E F n →L[ℂ] G)
    (h : ∀ d x, T (word E F n d x) = U (word E F n d x)) : T = U := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih a =>
    induction a using OAI.tensorInductionOn with
    | add a b ha hb => simp only [Completion.coe_add, map_add, ha, hb]
    | tmul d x =>
      have hx : x ∈ Submodule.span ℂ (Set.range (pure F n)) := by
        rw [span_pure]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, rfl⟩ := hx
        exact h d v
      | zero => simp only [TensorProduct.tmul_zero, Completion.coe_zero, map_zero]
      | add x y _ _ hx hy => simp only [TensorProduct.tmul_add, Completion.coe_add, map_add, hx, hy]
      | smul c x _ hx => simp only [TensorProduct.tmul_smul, Completion.coe_smul, map_smul, hx]

lemma continuousLinearMap_ext_word_inner (E F : PreHilbert) (k l : ℕ)
    (T U : wordSpace E F k →L[ℂ] wordSpace E F l)
    (h : ∀ d x c y, inner ℂ (word E F l c y) (T (word E F k d x)) =
      inner ℂ (word E F l c y) (U (word E F k d x))) : T = U := by
  apply continuousLinearMap_ext_word E F k T U
  intro d x
  apply sub_eq_zero.mp
  apply eq_zero_of_word_inner E F l
  intro c y
  rw [inner_sub_right, h, sub_self]

end Kadison.PreHilbert
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WordTopology2
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

namespace Kadison.Topology

open Set

lemma exists_stage_pi {ι : Type*} [Fintype ι] {E : ι → Type*}
    (S : ℕ → (i : ι) → Set (E i)) (hmono : ∀ i, Monotone (fun n => S n i))
    (v : ∀ i, E i) (hv : ∀ i, v i ∈ ⋃ n, S n i) :
    ∃ n, ∀ i, v i ∈ S n i := by
  classical
  have hv' (i) : ∃ n, v i ∈ S n i := Set.mem_iUnion.mp (hv i)
  choose a ha using hv'
  refine ⟨Finset.univ.sup a, fun i => ?_⟩
  exact hmono i (Finset.le_sup (Finset.mem_univ i)) (ha i)

lemma dense_iUnion_pi {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, TopologicalSpace (E i)]
    (S : ℕ → (i : ι) → Set (E i)) (hmono : ∀ i, Monotone (fun n => S n i))
    (hd : ∀ i, Dense (⋃ n, S n i)) : Dense (⋃ n, Set.pi Set.univ (S n)) := by
  apply (dense_pi Set.univ (fun i _ => hd i)).mono
  intro v hv
  obtain ⟨n, hn⟩ := exists_stage_pi S hmono v (fun i => hv i (Set.mem_univ i))
  exact Set.mem_iUnion.mpr ⟨n, fun i _ => hn i⟩

lemma dense_iUnion_prod {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (S : ℕ → Set E) (T : ℕ → Set F) (hS : Monotone S) (hT : Monotone T)
    (hSd : Dense (⋃ n, S n)) (hTd : Dense (⋃ n, T n)) :
    Dense (⋃ n, S n ×ˢ T n) := by
  apply (hSd.prod hTd).mono
  intro x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx.1
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx.2
  exact Set.mem_iUnion.mpr ⟨max n m, hS (le_max_left n m) hn, hT (le_max_right n m) hm⟩

end Kadison.Topology
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WordTopology3
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

lemma stageWordArgs_mono (E F : PreHilbert) (S : ℕ → Set E) (R : ℕ → Set F)
    (hS : Monotone S) (hR : Monotone R) (j : ℕ) :
    Monotone (stageWordArgs E F S R j) := by
  intro n m hnm x hx
  exact ⟨hS hnm hx.1, fun i hi => hR hnm (hx.2 i hi)⟩

lemma dense_stageWordArgs (E F : PreHilbert) (S : ℕ → Set E) (R : ℕ → Set F)
    (hS : Monotone S) (hR : Monotone R) (hSd : Dense (⋃ n, S n))
    (hRd : Dense (⋃ n, R n)) (j : ℕ) : Dense (⋃ n, stageWordArgs E F S R j n) := by
  exact Topology.dense_iUnion_prod S (fun n => Set.pi Set.univ (fun _ : Fin j => R n)) hS
    (fun n m hnm x hx i hi => hR hnm (hx i hi)) hSd
    (Topology.dense_iUnion_pi (fun n (_ : Fin j) => R n) (fun _ => hR) (fun _ => hRd))

lemma continuous_wordCoefficient (E F : PreHilbert) (k l : ℕ)
    (T : wordSpace E F k →L[ℂ] wordSpace E F l) :
    Continuous (fun z : (E × (Fin k → F)) × (E × (Fin l → F)) =>
      inner ℂ (word E F l z.2.1 z.2.2) (T (word E F k z.1.1 z.1.2))) := by
  exact (((continuous_word E F l).comp continuous_snd).inner
    (T.continuous.comp ((continuous_word E F k).comp continuous_fst)))

theorem operator_ext_dense_stages_oai (E F : PreHilbert) (k l : ℕ)
    (S : ℕ → Set E) (R : ℕ → Set F) (hS : Monotone S) (hR : Monotone R)
    (hSd : Dense (⋃ n, S n)) (hRd : Dense (⋃ n, R n))
    (T U : wordSpace E F k →L[ℂ] wordSpace E F l)
    (h : ∀ n d, d ∈ S n → ∀ x, (∀ i, x i ∈ R n) → ∀ c, c ∈ S n →
      ∀ y, (∀ j, y j ∈ R n) →
      inner ℂ (word E F l c y) (T (word E F k d x)) =
        inner ℂ (word E F l c y) (U (word E F k d x))) : T = U := by
  let W := stageWordArgs E F S R
  have hd : Dense (⋃ n, W k n ×ˢ W l n) :=
    Topology.dense_iUnion_prod (W k) (W l)
      (stageWordArgs_mono E F S R hS hR k) (stageWordArgs_mono E F S R hS hR l)
      (dense_stageWordArgs E F S R hS hR hSd hRd k)
      (dense_stageWordArgs E F S R hS hR hSd hRd l)
  apply continuousLinearMap_ext_word_inner E F k l T U
  intro d x c y
  refine hd.induction (P := fun z =>
    inner ℂ (word E F l z.2.1 z.2.2) (T (word E F k z.1.1 z.1.2)) =
      inner ℂ (word E F l z.2.1 z.2.2) (U (word E F k z.1.1 z.1.2))) ?_ ?_ ((d, x), (c, y))
  · intro z hz
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
    exact h n z.1.1 hn.1.1 z.1.2 (fun i => hn.1.2 i (Set.mem_univ i))
      z.2.1 hn.2.1 z.2.2 (fun j => hn.2.2 j (Set.mem_univ j))
  · exact isClosed_eq (continuous_wordCoefficient E F k l T)
      (continuous_wordCoefficient E F k l U)

end Kadison.PreHilbert
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.PreHilbert.operator_ext_dense_stages_oai := @OAI.Kadison.PreHilbert.operator_ext_dense_stages_oai
