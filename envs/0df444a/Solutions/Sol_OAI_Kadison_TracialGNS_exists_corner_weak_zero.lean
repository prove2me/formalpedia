-- Prove2me | solution 1 for OAI.Kadison.TracialGNS.exists_corner_weak_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:14:01.143986+00:00
-- url     : https://prove2.me/submissions/6c898819-eac8-4d50-9251-178d62b8d77e

import Mathlib
import Definitions.Def_OAIQ039C032
import Definitions.Def_OAIQ039C040
import Theorems.Thm_OAI_Kadison_TracialGNS_corner_arbitrarily_large_alphabet

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
-- module Solutions.OAIQ039_CM.Commutator_WeakZeroSelection
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open Filter Topology

namespace Kadison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma exists_orthonormal_small {I : Type*} [Fintype I] (v : I → E)
    (hv : Orthonormal ℂ v) (b : ℕ → E) (n : ℕ) (ε : ℝ) (hε : 0<ε)
    (hlarge : (∑ j ∈ Finset.range n, ‖b j‖^2)<Fintype.card I*ε^2) :
    ∃ i, ∀ j < n, ‖inner ℂ (v i) (b j)‖<ε := by
  classical
  by_contra! h
  have hlow (i : I) : ε^2≤∑ j ∈ Finset.range n, ‖inner ℂ (v i) (b j)‖^2 := by
    obtain ⟨j,hj,hij⟩ := h i
    calc
      ε^2 ≤ ‖inner ℂ (v i) (b j)‖^2 := by nlinarith [norm_nonneg (inner ℂ (v i) (b j))]
      _ ≤ _ := Finset.single_le_sum (fun k _ => sq_nonneg ‖inner ℂ (v i) (b k)‖)
        (Finset.mem_range.mpr hj)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlow i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  have hupp : (∑ i, ∑ j ∈ Finset.range n, ‖inner ℂ (v i) (b j)‖^2)≤
      ∑ j ∈ Finset.range n, ‖b j‖^2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun j _ => hv.sum_inner_products_le (b j)
  linarith

theorem exists_weak_zero_sequence (P : Set E) (b : ℕ → E) (hb : DenseRange b)
    (hlarge : ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ ∃ v : Fin m → E,
      Orthonormal ℂ v ∧ ∀ i, v i∈P) :
    ∃ v : ℕ → E, (∀ n, v n∈P) ∧ (∀ n, ‖v n‖=1) ∧
      ∀ y : E, Tendsto (fun n => inner ℂ (v n) y) atTop (𝓝 0) := by
  classical
  have hchoose (n : ℕ) : ∃ x : E, x∈P ∧ ‖x‖=1 ∧
      ∀ j < n, ‖inner ℂ x (b j)‖<(1:ℝ)/(n+1) := by
    have hε : 0<(1:ℝ)/(n+1) := by positivity
    obtain ⟨N,hN⟩ := exists_nat_gt ((∑ j ∈ Finset.range n, ‖b j‖^2)/((1:ℝ)/(n+1))^2)
    obtain ⟨m,hm,v,hv,hP⟩ := hlarge N
    have hbound : (∑ j ∈ Finset.range n, ‖b j‖^2)<Fintype.card (Fin m)*((1:ℝ)/(n+1))^2 := by
      rw [Fintype.card_fin]
      apply (div_lt_iff₀ (sq_pos_of_pos hε)).mp
      exact hN.trans_le (by exact_mod_cast hm)
    obtain ⟨i,hi⟩ := exists_orthonormal_small v hv b n _ hε hbound
    exact ⟨v i,hP i,hv.norm_eq_one i,hi⟩
  choose v hvP hvnorm hvsmall using hchoose
  have htest (j : ℕ) : Tendsto (fun n => inner ℂ (v n) (b j)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _))
      (eventually_atTop.mpr ⟨j+1,fun n hn => (hvsmall n j (by omega)).le⟩)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hclosed : IsClosed {y : E | Tendsto (fun n => inner ℂ (v n) y) atTop (𝓝 0)} := by
    have hF : Equicontinuous (fun n y => inner ℂ (v n) y) :=
      (LipschitzWith.uniformEquicontinuous (fun n y => inner ℂ (v n) y) 1
        (fun n => (innerSL ℂ (v n)).lipschitz.weaken (by
          exact_mod_cast (show ‖innerSL ℂ (v n)‖ ≤ (1:ℝ) by rw [innerSL_apply_norm,hvnorm])))).equicontinuous
    exact hF.isClosed_setOfPred_tendsto continuous_const
  refine ⟨v,hvP,hvnorm,fun y => ?_⟩
  have hsub : Set.range b ⊆ {y : E | Tendsto (fun n => inner ℂ (v n) y) atTop (𝓝 0)} := by
    rintro _ ⟨j,rfl⟩
    exact htest j
  exact closure_minimal hsub hclosed (hb y)

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerWeakZero
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

open Filter Topology

open scoped Matrix.Norms.L2Operator

namespace Kadison.TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b, τ (a*b)=τ (b*a)) (h1 : τ 1=1)
  (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
  (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
  (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (he : ∀ n m (h : n ≤ m) a, φ m (e h a)=φ n a)
  (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
  (hgen : ∀ a : A, τ.gnsStarAlgHom a ∈ Set.centralizer (Set.centralizer
    (stageAlgebra τ I φ : Set (τ.GNS →L[ℂ] τ.GNS))))

include e he hgen in
omit [∀ n, Nonempty (I n)] in
lemma separableGNS_of_stages : TopologicalSpace.SeparableSpace τ.GNS := by
  apply (dense_stages_of_bicommutant_generation τ I φ e he hgen).isSeparable_iff.mp
  apply TopologicalSpace.IsSeparable.iUnion
  intro n
  let : ProperSpace (Matrix (I n) (I n) ℂ) := FiniteDimensional.proper ℂ _
  exact TopologicalSpace.isSeparable_range (stageVector τ (φ n)).continuous_of_finiteDimensional

include hτ h1 e he hsize hgen in
theorem exists_corner_weak_zero_oai (n : ℕ) (p : Matrix (I n) (I n) ℂ)
    (hp : IsStarProjection p) (α : ℝ) (hα : 0<α) (hατ : τ (φ n p)=(α:ℂ)) :
    ∃ x : ℕ → A, (∀ k, τ (x k)=0 ∧ x k*φ n p=x k ∧
      star (x k)*x k=((α:ℂ)⁻¹) • φ n p ∧ ‖x k‖≤(Real.sqrt α)⁻¹ ∧
      ‖τ.toPreGNS (x k)‖=1 ∧ ‖τ.toPreGNS (star (x k))‖=1) ∧
      ∀ a : A, Tendsto (fun k => τ (x k*a)) atTop (𝓝 0) := by
  classical
  let P : Set τ.GNS := {v | ∃ x : A, algebraVector τ x=v ∧ τ x=0 ∧
    x*φ n p=x ∧ star x*x=((α:ℂ)⁻¹) • φ n p ∧ ‖x‖≤(Real.sqrt α)⁻¹}
  have hlarge : ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ ∃ v : Fin m → τ.GNS,
      Orthonormal ℂ v ∧ ∀ i, v i∈P := by
    intro N
    obtain ⟨m,hm,x,hx,hprop⟩ := corner_arbitrarily_large_alphabet τ hτ h1 I φ e he hsize n p hp α hα hατ N
    exact ⟨m,hm,fun i => algebraVector τ (x i),hx,fun i => ⟨x i,rfl,hprop i⟩⟩
  let : TopologicalSpace.SeparableSpace τ.GNS := separableGNS_of_stages τ I φ e he hgen
  obtain ⟨v,hv,hvn,hvweak⟩ := Kadison.exists_weak_zero_sequence P (TopologicalSpace.denseSeq τ.GNS)
    (TopologicalSpace.denseRange_denseSeq _) hlarge
  choose x hx hprop using hv
  refine ⟨x,?_,?_⟩
  · intro k
    have hn : ‖τ.toPreGNS (x k)‖=1 := by
      have h := hvn k
      rw [←hx k,algebraVector_apply,UniformSpace.Completion.norm_coe] at h
      exact h
    exact ⟨(hprop k).1,(hprop k).2.1,(hprop k).2.2.1,(hprop k).2.2.2,hn,
      (norm_star_preGNS τ hτ (x k)).trans hn⟩
  · intro a
    have ht := (hvweak (algebraVector τ (star a))).star
    convert ht using 1
    · funext k
      rw [←hx k,←inner_conj_symm,inner_algebraVector,star_star,hτ]
      simp
    · simp

end Kadison.TracialGNS

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.TracialGNS.exists_corner_weak_zero_oai.{u_1, u_2} := @OAI.Kadison.TracialGNS.exists_corner_weak_zero_oai.{u_1, u_2}
