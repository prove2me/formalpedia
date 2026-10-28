-- Prove2me | solution 1 for OAI.KirchbergRordam.PrimeTensorSections.irreducible_fiber_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T17:12:54.821+00:00
-- url     : https://prove2.me/submissions/1cb94598-1228-442b-9e9c-fe9d3a2b52a9

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr010
import Definitions.Def_OAIB3Kr012
import Theorems.Thm_OAI_KirchbergRordam_MatrixTensor_representation_bound

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimeSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace

namespace KirchbergRordam
namespace MaxTensor


open scoped CStarAlgebra


universe u


attribute [instance] CStarPack.inst

end MaxTensor
end KirchbergRordam
namespace KirchbergRordam.ScalarCenter
variable {E B : Type*} [CStarAlgebra E] [CStarAlgebra B] [Nontrivial B]

theorem exists_character (φ : E →⋆ₐ[ℂ] B)
    (hφ : ∀ x, ∃ z : ℂ, φ x = algebraMap ℂ B z) :
    ∃ χ : E →ₐ[ℂ] ℂ, ∀ x, φ x = algebraMap ℂ B (χ x) := by
  classical
  choose χ hχ using hφ
  have inj := FaithfulSMul.algebraMap_injective ℂ B
  let f : E →ₐ[ℂ] ℂ := {
    toFun := χ
    map_zero' := inj (by rw [← hχ,map_zero,map_zero])
    map_one' := inj (by rw [← hχ,map_one,map_one])
    map_add' := fun x y => inj (by rw [← hχ,map_add,map_add,← hχ,← hχ])
    map_mul' := fun x y => inj (by rw [← hχ,map_mul,map_mul,← hχ,← hχ])
    commutes' := fun z => inj (by rw [← hχ]; exact φ.commutes z) }
  exact ⟨f,hχ⟩

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
theorem exists_evaluation (φ : C(X,ℂ) →⋆ₐ[ℂ] B)
    (hφ : ∀ f, ∃ z : ℂ, φ f = algebraMap ℂ B z) :
    ∃ t : X, ∀ f, φ f = algebraMap ℂ B (f t) := by
  obtain ⟨χ,hχ⟩ := exists_character φ hφ
  obtain ⟨t,ht⟩ := (WeakDual.CharacterSpace.continuousMapEval_bijective X ℂ).surjective
    (WeakDual.CharacterSpace.equivAlgHom.symm χ)
  refine ⟨t, fun f => ?_⟩
  have hf : f t = χ f := congrArg (fun g : WeakDual.characterSpace ℂ C(X,ℂ) => g f) ht
  rw [hχ,hf]
end KirchbergRordam.ScalarCenter
namespace KirchbergRordam.PrimeDimensionDrop
open scoped CStarAlgebra ComplexOrder
variable {p q : ℕ}
lemma scalar_commute (f : C(unitInterval,ℂ)) (a : Algebra p q) :
    Commute (scalar p q f) a := by
  change scalar p q f*a=a*scalar p q f
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change ((f t) • (1 : Fiber p q)) * a.val t = a.val t * ((f t) • (1 : Fiber p q))
  simpa only [_root_.Algebra.algebraMap_eq_smul_one] using _root_.Algebra.commutes (f t) ((a : C(unitInterval,Fiber p q)) t)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

omit [Nontrivial H] in


theorem kills_evaluation_kernel (π : Algebra p q →⋆ₐ[ℂ] (H →L[ℂ] H))
    (t : unitInterval) (hπ : ∀ f, π (scalar p q f)=algebraMap ℂ (H →L[ℂ] H) (f t))
    (a : Algebra p q) (ha : (a : C(unitInterval,Fiber p q)) t=0) : π a=0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let f : C(unitInterval,ℂ) := ⟨fun s => (↑(ε/(ε+‖(a : C(unitInterval,Fiber p q)) s‖)) : ℂ),
    Complex.continuous_ofReal.comp (continuous_const.div
      (continuous_const.add (map_continuous (a : C(unitInterval,Fiber p q))).norm)
      (fun s => ne_of_gt (add_pos_of_pos_of_nonneg hε (norm_nonneg _))))⟩
  have hft : f t=1 := by simp [f,ha,ne_of_gt hε]
  have hfix : π (scalar p q f*a)=π a := by
    rw [map_mul,hπ,hft,map_one,one_mul]
  have hn : ‖scalar p q f*a‖≤ε := by
    change ‖((scalar p q f*a : Algebra p q) : C(unitInterval,Fiber p q))‖≤ε
    apply (ContinuousMap.norm_le _ hε.le).mpr
    intro s
    change ‖((f s) • (1 : Fiber p q))*(a : C(unitInterval,Fiber p q)) s‖≤ε
    rw [smul_mul_assoc,one_mul,norm_smul]
    change ‖((ε/(ε+‖(a : C(unitInterval,Fiber p q)) s‖) : ℝ) : ℂ)‖*‖(a : C(unitInterval,Fiber p q)) s‖≤ε
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (div_pos hε
      (add_pos_of_pos_of_nonneg hε (norm_nonneg _)))]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (add_pos_of_pos_of_nonneg hε (norm_nonneg _))).mpr
    nlinarith [sq_nonneg ε]
  have := (NonUnitalStarAlgHom.norm_apply_le π (scalar p q f*a)).trans hn
  simpa only [zero_add,hfix] using this
end KirchbergRordam.PrimeDimensionDrop

namespace KirchbergRordam
open scoped CStarAlgebra
lemma irreducible_central_evaluation {A : Type*} [CStarAlgebra A]
    (π : IrreducibleRepresentation A) (φ : C(unitInterval,ℂ) →⋆ₐ[ℂ] A)
    (hc : ∀ f a, Commute (φ f) a) :
    ∃ t, ∀ f, π.representation (φ f)=algebraMap ℂ _ (f t) := by
  apply ScalarCenter.exists_evaluation (π.representation.comp φ)
  intro f
  obtain ⟨z,hz⟩ := π.scalar_commutant (π.representation (φ f))
    (fun a => (hc f a).map π.representation)
  exact ⟨z,hz.trans (_root_.Algebra.algebraMap_eq_smul_one z).symm⟩
end KirchbergRordam
namespace KirchbergRordam.MaxTensor
open scoped CStarAlgebra
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

lemma commute_of_legs (π : Algebra A B →⋆ₐ[ℂ] C) (T : C)
    (hL : ∀ a, Commute T (π (includeLeft a)))
    (hR : ∀ b, Commute T (π (includeRight b))) :
    ∀ x, Commute T (π x) := by
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    change IsClosed {x | T * π x = π x * T}
    exact isClosed_eq (continuous_const.mul (map_continuous π))
      ((map_continuous π).mul continuous_const)
  | ih x =>
    suffices ∀ tensor : A ⊗[ℂ] B,
        Commute T (π (of (rawEquiv tensor))) from this x
    intro tensor
    induction tensor using OAI.tensorInductionOn with
    | add x y hx hy => simpa only [map_add] using hx.add_right hy
    | tmul a b =>
      change Commute T (π (of (a ⊗ₜ[ℂ] b)))
      rw [of_tmul, map_mul]
      exact (hL a).mul_right (hR b)
end KirchbergRordam.MaxTensor

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_TensorSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace

namespace KirchbergRordam.PrimeTensorSections
open scoped CStarAlgebra ComplexOrder TensorProduct
open PrimeDimensionDrop MatrixTensor
variable {p q r k : ℕ}

lemma scalarLeft_commute (f : C(unitInterval,ℂ)) :
    ∀ x : MaxTensor.Algebra (Algebra p q) (Algebra r k),
      Commute (MaxTensor.includeLeft (scalar p q f)) x := by
  apply MaxTensor.commute_of_legs (StarAlgHom.id ℂ _) _
  · intro a
    exact (scalar_commute f a).map MaxTensor.includeLeft
  · intro b
    exact MaxTensor.legs_commute (scalar p q f) b
lemma scalarRight_commute (f : C(unitInterval,ℂ)) :
    ∀ x : MaxTensor.Algebra (Algebra p q) (Algebra r k),
      Commute (MaxTensor.includeRight (scalar r k f)) x := by
  apply MaxTensor.commute_of_legs (StarAlgHom.id ℂ _) _
  · intro a
    exact (MaxTensor.legs_commute a (scalar r k f)).symm
  · intro b
    exact (scalar_commute f b).map MaxTensor.includeRight
lemma irreducible_left_evaluation
    (π : IrreducibleRepresentation (MaxTensor.Algebra (Algebra p q) (Algebra r k))) :
    ∃ s : unitInterval, ∀ f, π.representation (MaxTensor.includeLeft (scalar p q f))=
        algebraMap ℂ _ (f s) := by
  exact irreducible_central_evaluation π
    (MaxTensor.includeLeft.comp (scalar p q)) scalarLeft_commute
lemma irreducible_right_evaluation
    (π : IrreducibleRepresentation (MaxTensor.Algebra (Algebra p q) (Algebra r k))) :
    ∃ t : unitInterval, ∀ f, π.representation (MaxTensor.includeRight (scalar r k f))=
        algebraMap ℂ _ (f t) := by
  exact irreducible_central_evaluation π
    (MaxTensor.includeRight.comp (scalar r k)) scalarRight_commute
lemma sectionMap_evaluation (s t : unitInterval)
    (x : MaxTensor.Algebra (Algebra p q) (Algebra r k)) :
    fiberMap (evaluation p q s) (evaluation r k t) x=sectionMap x (s,t) := by
  have hsec : Continuous (sectionMap (p:=p) (q:=q) (r:=r) (k:=k)) := continuous_starHom (A:=MaxTensor.Algebra (Algebra p q) (Algebra r k))
    (B:=C(Square,SquareFiber p q r k)) _
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (map_continuous (fiberMap (evaluation p q s) (evaluation r k t)))
      ((continuous_eval_const (s,t)).comp hsec)
  | ih x =>
    change fiberMap (evaluation p q s) (evaluation r k t) (MaxTensor.of x)=sectionMap (MaxTensor.of x) (s,t)
    suffices ∀ tensor : Algebra p q ⊗[ℂ] Algebra r k,
        fiberMap (evaluation p q s) (evaluation r k t)
          (MaxTensor.of (MaxTensor.rawEquiv tensor)) =
        sectionMap (MaxTensor.of (MaxTensor.rawEquiv tensor)) (s,t) from
      this (MaxTensor.rawEquiv.symm x)
    intro tensor
    induction tensor using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add,ContinuousMap.add_apply,hx,hy]
    | tmul a b =>
      change fiberMap (evaluation p q s) (evaluation r k t) (MaxTensor.of (a ⊗ₜ[ℂ] b)) =
        sectionMap (MaxTensor.of (a ⊗ₜ[ℂ] b)) (s,t)
      rw [fiberMap_tmul,MaxTensor.of_tmul,map_mul,ContinuousMap.mul_apply,
        sectionMap_left,sectionMap_right]; rfl

lemma irreducible_fiber_bound_oai
    (π : IrreducibleRepresentation (MaxTensor.Algebra (Algebra p q) (Algebra r k))) :
    ∃ s t : unitInterval, ∀ x, ‖π.representation x‖ ≤ ‖sectionMap x (s,t)‖ := by
  obtain ⟨s,hs⟩ := irreducible_left_evaluation π
  obtain ⟨t,ht⟩ := irreducible_right_evaluation π
  have hkL : ∀ a, evaluation p q s a=0 → π.representation (MaxTensor.includeLeft a)=0 :=
    kills_evaluation_kernel (π.representation.comp MaxTensor.includeLeft) s hs
  have hkR : ∀ b, evaluation r k t b=0 → π.representation (MaxTensor.includeRight b)=0 :=
    kills_evaluation_kernel (π.representation.comp MaxTensor.includeRight) t ht
  have hb := representation_bound (evaluation p q s) (evaluation r k t) π.representation hkL hkR
  refine ⟨s,t,?_⟩
  intro x
  simpa only [sectionMap_evaluation] using hb x


end KirchbergRordam.PrimeTensorSections
end

end OAI
end

theorem solution : type_of% @OAI.KirchbergRordam.PrimeTensorSections.irreducible_fiber_bound_oai := @OAI.KirchbergRordam.PrimeTensorSections.irreducible_fiber_bound_oai
