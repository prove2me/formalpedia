-- Prove2me | solution 1 for OAI.KirchbergRordam.MatrixTensor.representation_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T17:12:31.601097+00:00
-- url     : https://prove2.me/submissions/6a35df4f-8f61-4f78-83f5-57823d6078a3

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr010
import Definitions.Def_OAIB3Kr012

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Pauli
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.DetectingSpace.quotientNormedRing _root_.OAI.KirchbergRordam.GenericRW.PureStates.locallyConvexReal _root_.OAI.KirchbergRordam.GenericRW.StarCompletion.completionNormedAlgebra _root_.OAI.KirchbergRordam.GenericRW.StarCompletion.completionStar _root_.OAI.KirchbergRordam.GenericRW.StarCompletion.completionStarRing _root_.OAI.KirchbergRordam.MatrixTensor.matrixFinite _root_.OAI.KirchbergRordam.MatrixTensor.subCStar _root_.OAI.KirchbergRordam.MatrixTensor.subClosed _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


namespace KirchbergRordam.MatrixTensor
open scoped Matrix Kronecker
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]


lemma algebra_legs_product (a : Matrix ι ι ℂ) (b : Matrix κ κ ℂ) :
    leftMatrixAlgebra (κ:=κ) a*rightMatrixAlgebra (ι:=ι) b=Matrix.kronecker a b := by
  change Matrix.kronecker a 1 * Matrix.kronecker 1 b = Matrix.kronecker a b
  dsimp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul]
  simp

lemma legs_product (a : Mat ι) (b : Mat κ) :
    leftMatrix (κ:=κ) a*rightMatrix (ι:=ι) b=CStarMatrix.ofMatrix (Matrix.kronecker a b) := by
  exact congrArg CStarMatrix.ofMatrix
    (algebra_legs_product (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b))
end KirchbergRordam.MatrixTensor

namespace KirchbergRordam.GenericRW

section
open scoped Matrix BigOperators
attribute [local instance] PauliData.finite PauliData.decidable

end
open scoped Matrix BigOperators

end KirchbergRordam.GenericRW

end

end OAI
end

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
namespace KirchbergRordam.MatrixTensor
open scoped TensorProduct Matrix Kronecker CStarAlgebra ComplexOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
lemma decompose (a : Mat ι) : (∑ ij : ι×ι, a ij.1 ij.2 • unit ij.1 ij.2)=a := by
  change (∑ ij : ι×ι, a ij.1 ij.2 • Matrix.single ij.1 ij.2 1)=a
  ext i j
  simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.single_apply,smul_eq_mul]
  simp [← Finset.univ_product_univ,Finset.sum_product,ite_and]

@[simp] lemma kroneckerRaw_tmul (a : Mat ι) (b : Mat κ) :
    kroneckerRaw (a ⊗ₜ[ℂ] b)=CStarMatrix.ofMatrix (Matrix.kronecker a b) := legs_product a b

lemma kroneckerInverse_tmul (a : Mat ι) (b : Mat κ) :
    kroneckerInverse (kroneckerRaw (a ⊗ₜ[ℂ] b))=a ⊗ₜ[ℂ] b := by
  rw [kroneckerRaw_tmul]
  let ca : ι×ι → ℂ := fun ij => a ij.1 ij.2
  let cb : κ×κ → ℂ := fun kl => b kl.1 kl.2
  change (∑ ij : ι×ι, ∑ kl : κ×κ,
    (ca ij * cb kl) • (unit ij.1 ij.2 ⊗ₜ[ℂ] unit kl.1 kl.2))=_
  have he (ij : ι×ι) (kl : κ×κ) :
      (ca ij * cb kl) • (unit ij.1 ij.2 ⊗ₜ[ℂ] unit kl.1 kl.2) =
        (ca ij • unit ij.1 ij.2) ⊗ₜ[ℂ] (cb kl • unit kl.1 kl.2) := by
    exact (TensorProduct.smul_tmul_smul _ _ _ _).symm
  simp_rw [he,← TensorProduct.tmul_sum]
  rw [← TensorProduct.sum_tmul]
  exact congrArg₂ (fun x y => x ⊗ₜ[ℂ] y) (decompose a) (decompose b)

lemma kroneckerRaw_injective : Function.Injective (kroneckerRaw (ι:=ι) (κ:=κ)) := by
  apply Function.LeftInverse.injective (g:=kroneckerInverse)
  intro x
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a b => exact kroneckerInverse_tmul a b
end KirchbergRordam.MatrixTensor
namespace KirchbergRordam.MatrixTensor
open scoped TensorProduct CStarAlgebra ComplexOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma subKronecker_eq (S : StarSubalgebra ℂ (Mat ι)) (T : StarSubalgebra ℂ (Mat κ))
    (x : S ⊗[ℂ] T) : subKronecker S T x=
      kroneckerRaw (TensorProduct.map S.subtype.toLinearMap T.subtype.toLinearMap x) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a b => rw [TensorProduct.map_tmul]; rfl

lemma subKronecker_injective (S : StarSubalgebra ℂ (Mat ι))
    (T : StarSubalgebra ℂ (Mat κ)) : Function.Injective (subKronecker S T) := by
  intro x y h
  rw [subKronecker_eq,subKronecker_eq] at h
  exact TensorProduct.map_injective_of_flat_flat S.subtype.toLinearMap T.subtype.toLinearMap
    Subtype.val_injective Subtype.val_injective (kroneckerRaw_injective h)


theorem norm_liftRaw_sub_le (S : StarSubalgebra ℂ (Mat ι))
    (T : StarSubalgebra ℂ (Mat κ)) {B : Type*} [CStarAlgebra B]
    (φ : S →⋆ₐ[ℂ] B) (ψ : T →⋆ₐ[ℂ] B)
    (hc : ∀ a b, Commute (φ a) (ψ b)) (x : S ⊗[ℂ] T) :
    ‖MaxTensor.liftRaw φ ψ hc (MaxTensor.rawEquiv x)‖ ≤ ‖subKronecker S T x‖ := by
  let f := subKronecker S T
  let g := (MaxTensor.liftRaw φ ψ hc).comp MaxTensor.rawEquiv.toStarAlgHom
  have hk (a : S ⊗[ℂ] T) (ha : f a=0) : g a=0 := by
    have hz : a=0 := subKronecker_injective S T (ha.trans (map_zero f).symm)
    rw [hz,map_zero]
  let d := StarRangeFactor.descend f g hk
  have hn := NonUnitalStarAlgHom.norm_apply_le d ⟨f x,⟨x,rfl⟩⟩
  change ‖d ⟨f x,⟨x,rfl⟩⟩‖ ≤ ‖f x‖ at hn
  rw [StarRangeFactor.descend_apply] at hn
  exact hn
end KirchbergRordam.MatrixTensor
namespace KirchbergRordam.StarRangeFactor
variable {A B C D E : Type*} [Ring A] [Ring B] [Ring C] [Ring D] [Ring E]
  [StarRing A] [StarRing B] [StarRing C] [StarRing D] [StarRing E]
  [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C] [Algebra ℂ D] [Algebra ℂ E]
  [instStarModuleℂA : StarModule ℂ A] [instStarModuleℂB : StarModule ℂ B] [StarModule ℂ C] [StarModule ℂ D] [StarModule ℂ E]
lemma descend_commute (f : A →⋆ₐ[ℂ] C) (g : A →⋆ₐ[ℂ] E)
    (h : B →⋆ₐ[ℂ] D) (j : B →⋆ₐ[ℂ] E)
    (hk : ∀ a, f a=0 → g a=0) (hl : ∀ b, h b=0 → j b=0)
    (hc : ∀ a b, Commute (g a) (j b))
    (a : f.range) (b : h.range) : Commute (descend f g hk a) (descend h j hl b) := by
  obtain ⟨a',ha⟩ := a.property
  obtain ⟨b',hb⟩ := b.property
  have heL : (⟨f a',⟨a',rfl⟩⟩:f.range)=a := Subtype.ext ha
  have heR : (⟨h b',⟨b',rfl⟩⟩:h.range)=b := Subtype.ext hb
  rw [← heL,← heR,descend_apply,descend_apply]
  exact hc a' b'
end KirchbergRordam.StarRangeFactor

namespace KirchbergRordam.MatrixTensor
open scoped CStarAlgebra ComplexOrder TensorProduct
variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]


theorem representation_bound_oai
    (eL : A →⋆ₐ[ℂ] Mat ι) (eR : B →⋆ₐ[ℂ] Mat κ)
    (π : MaxTensor.Algebra A B →⋆ₐ[ℂ] R)
    (hkL : ∀ a, eL a=0 → π (MaxTensor.includeLeft a)=0)
    (hkR : ∀ b, eR b=0 → π (MaxTensor.includeRight b)=0) :
    ∀ x, ‖π x‖≤‖fiberMap eL eR x‖ := by
  let πL := π.comp MaxTensor.includeLeft
  let πR := π.comp MaxTensor.includeRight
  let dL := StarRangeFactor.descend eL πL hkL
  let dR := StarRangeFactor.descend eR πR hkR
  have hd : ∀ a b, Commute (dL a) (dR b) :=
    StarRangeFactor.descend_commute eL πL eR πR hkL hkR
      (fun a b => (MaxTensor.legs_commute a b).map π)
  let E := TensorProduct.map eL.rangeRestrict.toLinearMap eR.rangeRestrict.toLinearMap
  have hdL (a : A) : dL (eL.rangeRestrict a)=πL a := StarRangeFactor.descend_apply eL πL hkL a
  have hdR (b : B) : dR (eR.rangeRestrict b)=πR b := StarRangeFactor.descend_apply eR πR hkR b
  have hπ (x : A ⊗[ℂ] B) :
      MaxTensor.liftRaw dL dR hd (MaxTensor.rawEquiv (E x)) =
        π (MaxTensor.of (MaxTensor.rawEquiv x)) := by
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul a b =>
      change dL (eL.rangeRestrict a) * dR (eR.rangeRestrict b) =
        π (MaxTensor.of (a ⊗ₜ[ℂ] b))
      rw [hdL,hdR]
      rw [MaxTensor.of_tmul,map_mul]
      rfl
  have he (x : A ⊗[ℂ] B) : subKronecker eL.range eR.range (E x)=
      fiberMap eL eR (MaxTensor.of (MaxTensor.rawEquiv x)) := by
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul a b =>
      change subKronecker eL.range eR.range (E (a ⊗ₜ[ℂ] b)) =
        fiberMap eL eR (MaxTensor.of (a ⊗ₜ[ℂ] b))
      rw [fiberMap_tmul]
      rfl
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (map_continuous π).norm (map_continuous (fiberMap eL eR)).norm
  | ih x =>
    change ‖π (MaxTensor.of (MaxTensor.rawEquiv (MaxTensor.rawEquiv.symm x)))‖ ≤
      ‖fiberMap eL eR (MaxTensor.of (MaxTensor.rawEquiv (MaxTensor.rawEquiv.symm x)))‖
    rw [← hπ,← he]
    exact norm_liftRaw_sub_le eL.range eR.range dL dR hd (E (MaxTensor.rawEquiv.symm x))
end KirchbergRordam.MatrixTensor

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.KirchbergRordam.MatrixTensor.representation_bound_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.KirchbergRordam.MatrixTensor.representation_bound_oai.{u_1, u_2, u_3, u_4, u_5}
