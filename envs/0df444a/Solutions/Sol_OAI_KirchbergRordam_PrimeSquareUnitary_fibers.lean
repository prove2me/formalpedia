-- Prove2me | solution 1 for OAI.KirchbergRordam.PrimeSquareUnitary.fibers
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T17:37:03.576011+00:00
-- url     : https://prove2.me/submissions/a1eabdf9-bd77-4600-a655-0797c7cc8caa

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr013
import Definitions.Def_OAIB3Kr014

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
-- module Solutions.OAIB3_Krc.CharacterCriterion_MatrixPaths
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
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

namespace KirchbergRordam.MatrixPermutationPath
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


lemma perm_conjugation (σ : Equiv.Perm ι) (a : Mat ι) :
    Unitary.conjStarAlgAut ℂ _ (perm σ) a = CStarMatrix.reindexₐ ℂ ℂ σ a := by
  change σ⁻¹.permMatrix ℂ * CStarMatrix.ofMatrix.symm a * (σ⁻¹.permMatrix ℂ)ᴴ =
    Matrix.reindex σ σ (CStarMatrix.ofMatrix.symm a)
  rw [Matrix.conjTranspose_permMatrix]
  change σ.symm.toPEquiv.toMatrix * CStarMatrix.ofMatrix.symm a * σ.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl


end KirchbergRordam.MatrixPermutationPath

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

end KirchbergRordam.MatrixTensor

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

namespace KirchbergRordam.PrimeDimensionDrop
open scoped CStarAlgebra ComplexOrder
open MatrixTensor
variable {p q : ℕ}

lemma evaluation_zero_range : (evaluation p q 0).range=MatrixTensor.leftMatrix.range := by
  ext a
  constructor
  · rintro ⟨f,rfl⟩
    exact f.property.1
  · rintro ⟨b,rfl⟩
    exact ⟨leftRamp b,by simp [evaluation_apply,leftRamp]⟩
lemma evaluation_one_range : (evaluation p q 1).range=MatrixTensor.rightMatrix.range := by
  ext a
  constructor
  · rintro ⟨f,rfl⟩
    exact f.property.2
  · rintro ⟨b,rfl⟩
    exact ⟨rightRamp b,by change (1:ℂ) • MatrixTensor.rightMatrix (ι:=Fin p) b=MatrixTensor.rightMatrix b; rw [one_smul]⟩

lemma evaluation_interior_surjective (t : unitInterval) (h0 : t≠0) (h1 : t≠1) :
    Function.Surjective (evaluation p q t) := by
  intro a
  have ht0 : (t:ℝ)≠0 := by intro h; apply h0; exact Subtype.ext h
  have ht1 : 1-(t:ℝ)≠0 := by intro h; apply h1; apply Subtype.ext; change (t:ℝ)=1; linarith
  refine ⟨interiorRamp t a,?_⟩
  change ((((t:ℝ)*(1-t)/(t*(1-t)):ℝ):ℂ) • a)=a
  rw [div_self (mul_ne_zero ht0 ht1)]
  simp
lemma evaluation_interior_range (t : unitInterval) (h0 : t≠0) (h1 : t≠1) :
    (evaluation p q t).range=⊤ := by
  ext a
  exact ⟨fun _ => trivial,fun _ => evaluation_interior_surjective t h0 h1 a⟩
end KirchbergRordam.PrimeDimensionDrop
namespace KirchbergRordam.MatrixTensor
open scoped TensorProduct CStarAlgebra ComplexOrder Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
lemma tensorRange_tmul (S : StarSubalgebra ℂ (Mat ι)) (T : StarSubalgebra ℂ (Mat κ))
    {a : Mat ι} {b : Mat κ} (ha : a∈S) (hb : b∈T) :
    MatrixTensor.leftMatrix a*MatrixTensor.rightMatrix b∈tensorRange S T :=
  ⟨(⟨a,ha⟩:S) ⊗ₜ[ℂ] (⟨b,hb⟩:T),rfl⟩
lemma tensorRange_left (S : StarSubalgebra ℂ (Mat ι)) (T : StarSubalgebra ℂ (Mat κ))
    {a : Mat ι} (ha : a∈S) : MatrixTensor.leftMatrix a∈tensorRange S T := by
  simpa only [map_one,mul_one] using tensorRange_tmul S T ha (T.one_mem)
lemma tensorRange_right (S : StarSubalgebra ℂ (Mat ι)) (T : StarSubalgebra ℂ (Mat κ))
    {b : Mat κ} (hb : b∈T) : MatrixTensor.rightMatrix b∈tensorRange S T := by
  simpa only [map_one,one_mul] using tensorRange_tmul S T (S.one_mem) hb
lemma tensorRange_mono {S₁ S₂ : StarSubalgebra ℂ (Mat ι)}
    {T₁ T₂ : StarSubalgebra ℂ (Mat κ)} (hS : S₁≤S₂) (hT : T₁≤T₂) :
    tensorRange S₁ T₁ ≤ tensorRange S₂ T₂ := by
  rintro a ⟨b,rfl⟩
  change subKronecker S₁ T₁ b ∈ (tensorRange S₂ T₂).toSubalgebra
  induction b using OAI.tensorInductionOn with
  | add x y hx hy => rw [map_add]; exact (tensorRange S₂ T₂).add_mem hx hy
  | tmul a b => exact tensorRange_tmul S₂ T₂ (hS a.property) (hT b.property)
lemma matrixUnit_kronecker (i j : ι) (k l : κ) :
    MatrixTensor.leftMatrix (unit i j)*MatrixTensor.rightMatrix (unit k l)=unit (i,k) (j,l) := by
  rw [legs_product]
  ext a b
  change (Matrix.single i j (1:ℂ)) a.1 b.1 * (Matrix.single k l (1:ℂ)) a.2 b.2 =
    (Matrix.single (i,k) (j,l) (1:ℂ)) a b
  rcases a with ⟨a,c⟩; rcases b with ⟨b,d⟩
  simp only [Matrix.single_apply,Prod.mk.injEq]
  split_ifs <;> simp_all
lemma tensorRange_top_top : tensorRange (⊤ : StarSubalgebra ℂ (Mat ι))
    (⊤ : StarSubalgebra ℂ (Mat κ))=⊤ := by
  apply top_unique
  intro a _
  rw [←decompose a]
  change _∈(tensorRange (⊤ : StarSubalgebra ℂ (Mat ι)) (⊤ : StarSubalgebra ℂ (Mat κ))).toSubalgebra
  apply Subalgebra.sum_mem
  intro ij _
  apply Subalgebra.smul_mem
  rw [←matrixUnit_kronecker]
  exact tensorRange_tmul _ _ trivial trivial
end KirchbergRordam.MatrixTensor
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FourLegSymmetries
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

namespace KirchbergRordam.FourLegSymmetries
open scoped CStarAlgebra ComplexOrder Matrix Kronecker
open MatrixTensor MatrixPermutationPath
variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
lemma flip_product : H (P:=P) (Q:=Q)*K=perm (Equiv.prodComm (P×Q) (P×Q)) := by
  rw [H,K,←perm_mul]
  rfl
lemma conj_flip_left (a : MatrixTensor.Mat (P×Q)) :
    Unitary.conjStarAlgAut ℂ _ (H (P:=P) (Q:=Q)*K) (MatrixTensor.leftMatrix a)=MatrixTensor.rightMatrix a := by
  rw [flip_product,perm_conjugation]
  ext i j
  change a i.2 j.2 * (1:Matrix (P×Q) (P×Q) ℂ) i.1 j.1 =
    (1:Matrix (P×Q) (P×Q) ℂ) i.1 j.1 * a i.2 j.2
  exact mul_comm _ _

lemma conj_K_left_left (a : MatrixTensor.Mat P) :
    Unitary.conjStarAlgAut ℂ _ (K (P:=P) (Q:=Q)) (MatrixTensor.leftMatrix (MatrixTensor.leftMatrix a))=
      MatrixTensor.leftMatrix (MatrixTensor.leftMatrix a) := by
  rw [K,perm_conjugation]
  ext i j
  change (a i.1.1 j.1.1 * (1:Matrix Q Q ℂ) i.2.2 j.2.2) *
    (1:Matrix (P×Q) (P×Q) ℂ) (i.2.1,i.1.2) (j.2.1,j.1.2) =
    (a i.1.1 j.1.1 * (1:Matrix Q Q ℂ) i.1.2 j.1.2) *
    (1:Matrix (P×Q) (P×Q) ℂ) i.2 j.2
  simp only [Matrix.one_apply,Prod.mk.injEq]
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

end KirchbergRordam.FourLegSymmetries
namespace KirchbergRordam.FourLegSymmetries
open MatrixTensor MatrixPermutationPath
open scoped CStarAlgebra ComplexOrder Matrix Kronecker TensorProduct
variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
lemma H_decompose : (H (P:=P) (Q:=Q) : Algebra P Q) =
    ∑ ij : P×P, MatrixTensor.leftMatrix (MatrixTensor.leftMatrix (κ:=Q) (unit ij.1 ij.2))*
      MatrixTensor.rightMatrix (MatrixTensor.leftMatrix (κ:=Q) (unit ij.2 ij.1)) := by
  simp_rw [legs_product]
  ext i j
  change (hflip⁻¹.permMatrix ℂ) i j =
    (∑ ab : P×P, Matrix.kronecker (Matrix.kronecker (Matrix.single ab.1 ab.2 (1:ℂ)) 1)
      (Matrix.kronecker (Matrix.single ab.2 ab.1 (1:ℂ)) 1)) i j
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
    Option.mem_some_iff,hflip,Equiv.Perm.inv_def,Equiv.coe_fn_symm_mk,Prod.mk.injEq,
    Matrix.sum_apply]
  simp [←Finset.univ_product_univ,Finset.sum_product,ite_and,Matrix.single_apply,Matrix.one_apply,eq_comm]
  split_ifs <;> simp_all
lemma K_decompose : (K (P:=P) (Q:=Q) : Algebra P Q) =
    ∑ ij : Q×Q, MatrixTensor.leftMatrix (MatrixTensor.rightMatrix (ι:=P) (unit ij.1 ij.2))*
      MatrixTensor.rightMatrix (MatrixTensor.rightMatrix (ι:=P) (unit ij.2 ij.1)) := by
  simp_rw [legs_product]
  ext i j
  change (kflip⁻¹.permMatrix ℂ) i j =
    (∑ ab : Q×Q, Matrix.kronecker (Matrix.kronecker 1 (Matrix.single ab.1 ab.2 (1:ℂ)))
      (Matrix.kronecker 1 (Matrix.single ab.2 ab.1 (1:ℂ)))) i j
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
    Option.mem_some_iff,kflip,Equiv.Perm.inv_def,Equiv.coe_fn_symm_mk,Prod.mk.injEq,
    Matrix.sum_apply]
  simp [←Finset.univ_product_univ,Finset.sum_product,ite_and,Matrix.single_apply,Matrix.one_apply,eq_comm]
  split_ifs <;> simp_all
lemma H_mem : (H (P:=P) (Q:=Q) : Algebra P Q)∈
    tensorRange (MatrixTensor.leftMatrix (ι:=P) (κ:=Q)).range (MatrixTensor.leftMatrix (ι:=P) (κ:=Q)).range := by
  rw [H_decompose]
  apply Subalgebra.sum_mem
  intro ij _
  exact tensorRange_tmul _ _ ⟨_,rfl⟩ ⟨_,rfl⟩
lemma K_mem : (K (P:=P) (Q:=Q) : Algebra P Q)∈
    tensorRange (MatrixTensor.rightMatrix (ι:=P) (κ:=Q)).range (MatrixTensor.rightMatrix (ι:=P) (κ:=Q)).range := by
  rw [K_decompose]
  apply Subalgebra.sum_mem
  intro ij _
  exact tensorRange_tmul _ _ ⟨_,rfl⟩ ⟨_,rfl⟩
lemma conj_K_left_right (b : MatrixTensor.Mat Q) :
    Unitary.conjStarAlgAut ℂ _ (K (P:=P) (Q:=Q)) (MatrixTensor.leftMatrix (MatrixTensor.rightMatrix b))=
      MatrixTensor.rightMatrix (MatrixTensor.rightMatrix b) := by
  rw [K,perm_conjugation]
  ext i j
  change ((1:Matrix P P ℂ) i.1.1 j.1.1 * b i.2.2 j.2.2) *
    (1:Matrix (P×Q) (P×Q) ℂ) (i.2.1,i.1.2) (j.2.1,j.1.2) =
    (1:Matrix (P×Q) (P×Q) ℂ) i.1 j.1 *
    ((1:Matrix P P ℂ) i.2.1 j.2.1 * b i.2.2 j.2.2)
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Matrix.one_apply,Prod.mk.injEq]
  split_ifs <;> simp_all
lemma conj_H_left_left (a : MatrixTensor.Mat P) :
    Unitary.conjStarAlgAut ℂ _ (H (P:=P) (Q:=Q)) (MatrixTensor.leftMatrix (MatrixTensor.leftMatrix a))=
      MatrixTensor.rightMatrix (MatrixTensor.leftMatrix a) := by
  rw [H,perm_conjugation]
  ext i j
  change (a i.2.1 j.2.1 * (1:Matrix Q Q ℂ) i.1.2 j.1.2) *
    (1:Matrix (P×Q) (P×Q) ℂ) (i.1.1,i.2.2) (j.1.1,j.2.2) =
    (1:Matrix (P×Q) (P×Q) ℂ) i.1 j.1 *
    (a i.2.1 j.2.1 * (1:Matrix Q Q ℂ) i.2.2 j.2.2)
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Matrix.one_apply,Prod.mk.injEq]
  split_ifs <;> simp_all
lemma conj_H_left_right (b : MatrixTensor.Mat Q) :
    Unitary.conjStarAlgAut ℂ _ (H (P:=P) (Q:=Q)) (MatrixTensor.leftMatrix (MatrixTensor.rightMatrix b))=
      MatrixTensor.leftMatrix (MatrixTensor.rightMatrix b) := by
  rw [H,perm_conjugation]
  ext i j
  change ((1:Matrix P P ℂ) i.2.1 j.2.1 * b i.1.2 j.1.2) *
    (1:Matrix (P×Q) (P×Q) ℂ) (i.1.1,i.2.2) (j.1.1,j.2.2) =
    ((1:Matrix P P ℂ) i.1.1 j.1.1 * b i.1.2 j.1.2) *
    (1:Matrix (P×Q) (P×Q) ℂ) i.2 j.2
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Matrix.one_apply,Prod.mk.injEq]
  split_ifs <;> simp_all

lemma K_cross_mem (a : MatrixTensor.Mat (P×Q)) :
    Unitary.conjStarAlgAut ℂ _ (K (P:=P) (Q:=Q)) (MatrixTensor.leftMatrix a) ∈
      tensorRange (MatrixTensor.leftMatrix (ι:=P) (κ:=Q)).range (MatrixTensor.rightMatrix (ι:=P) (κ:=Q)).range := by
  rw [←decompose a,map_sum,map_sum]
  apply Subalgebra.sum_mem
  intro ij _
  rw [map_smul,map_smul]
  apply Subalgebra.smul_mem
  rcases ij with ⟨⟨i,k⟩,⟨j,l⟩⟩
  rw [←matrixUnit_kronecker,map_mul,map_mul,conj_K_left_left,conj_K_left_right]
  exact tensorRange_tmul _ _ ⟨_,rfl⟩ ⟨_,rfl⟩
lemma H_cross_mem (a : MatrixTensor.Mat (P×Q)) :
    Unitary.conjStarAlgAut ℂ _ (H (P:=P) (Q:=Q)) (MatrixTensor.leftMatrix a) ∈
      tensorRange (MatrixTensor.rightMatrix (ι:=P) (κ:=Q)).range (MatrixTensor.leftMatrix (ι:=P) (κ:=Q)).range := by
  rw [←decompose a,map_sum,map_sum]
  apply Subalgebra.sum_mem
  intro ij _
  rw [map_smul,map_smul]
  apply Subalgebra.smul_mem
  rcases ij with ⟨⟨i,k⟩,⟨j,l⟩⟩
  rw [←matrixUnit_kronecker,map_mul,map_mul,conj_H_left_left,conj_H_left_right,
    (legs_commute _ _).symm.eq]
  exact tensorRange_tmul _ _ ⟨_,rfl⟩ ⟨_,rfl⟩
end KirchbergRordam.FourLegSymmetries


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_SymmetryFlow
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

open scoped CStarAlgebra ComplexOrder
namespace KirchbergRordam.SymmetryFlow

variable {A : Type*} [CStarAlgebra A]

lemma flow_commute (U : unitary A) (hs) (a : A) (ha : Commute (U:A) a) (t : ℝ) :
    Commute (flow U hs t : A) a :=
  ((Commute.one_left a).smul_left _).add_left (ha.smul_left _)
end KirchbergRordam.SymmetryFlow


namespace KirchbergRordam.UnitaryConjugacySquare
open Filter Topology
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A]

lemma flow_neg (V : Flow A) (s : ℝ) : V (-s)=star (V s) := by
  have h := V.add (-s) s
  rw [neg_add_cancel,V.zero] at h
  exact (eq_inv_iff_mul_eq_one.mpr h.symm).trans rfl

lemma square_bottom (V : Flow A) (U : ℝ → unitary A) (s : unitInterval) :
    square V U (s,0)=U s := by simp [square,ratio,radius]
lemma square_right (V : Flow A) (U : ℝ → unitary A) (t : unitInterval) :
    square V U (1,t)=V t*U 1 := by simp [square,ratio,radius]
lemma square_top (V : Flow A) (U : ℝ → unitary A) (s : unitInterval) :
    square V U (s,1)=V 1*U 1*star (V 1)*V s := by
  have hr : radius (s,1)=1 := by simp [radius]
  have ha : ratio (s,1)=1 := by simp [ratio,hr]
  have h : -((1:ℝ)-(s:ℝ)) = -1+(s:ℝ) := by ring
  change V (ratio (s,1))*U (radius (s,1))*V (-((1-(s:ℝ))*ratio (s,1)))=_
  rw [hr,ha,mul_one,h,flow_add,flow_neg,mul_assoc]
  simp only [mul_assoc]
lemma square_left (V : Flow A) (U : ℝ → unitary A) (hzero : U 0=1)
    (t : unitInterval) : square V U (0,t)=V 1*U t*star (V 1) := by
  by_cases ht : (t:ℝ)=0
  · have he : t=0 := Subtype.ext ht
    subst t
    simp [square_origin V U hzero,hzero]
  · simp [square,ratio,radius,ht,flow_neg]
end KirchbergRordam.UnitaryConjugacySquare


namespace KirchbergRordam.SymmetryConjugacyDiagram
open UnitaryConjugacySquare
variable {A : Type*} [CStarAlgebra A]

namespace Data
variable (D : Data A)
lemma H_inv : D.H⁻¹=D.H := D.H_star
lemma K_inv : D.K⁻¹=D.K := D.K_star
lemma Hp_commute (r : ℝ) : Commute (D.Hp r) D.K := by
  apply Subtype.ext
  exact SymmetryFlow.flow_commute D.H D.hH (D.K:A)
    (show Commute (D.H:A) (D.K:A) from congrArg Subtype.val D.commute.eq) r
lemma Kp_commute (r : ℝ) : Commute D.H (D.Kp r) := by
  apply Subtype.ext
  exact (SymmetryFlow.flow_commute D.K D.hK (D.H:A)
    (show Commute (D.K:A) (D.H:A) from congrArg Subtype.val D.commute.symm.eq) r).symm
@[simp] lemma HH : D.H*D.H=1 := by simpa only [D.H_inv] using inv_mul_cancel D.H
@[simp] lemma KK : D.K*D.K=1 := by simpa only [D.K_inv] using inv_mul_cancel D.K

lemma W_bottom (s : unitInterval) :
    D.W (s,0)=D.H*star (D.L 1)*D.Hp s*D.L 1*star (D.L s) := by
  simp only [W,R_zero,one_mul,square_bottom,U,mul_assoc]

lemma W_right (t : unitInterval) :
    D.W (1,t)=D.R t*D.Kp t*(D.H*star (D.L 1)*D.H) := by
  simp only [W,square_right,U,Hp_one]
  calc
    _ = D.R t*(D.H*D.Kp t)*(star (D.L 1)*D.H) := by
      simp only [Unitary.star_eq_inv]; group
    _ = _ := by rw [(D.Kp_commute t).eq]; simp only [mul_assoc]

lemma W_left (t : unitInterval) :
    D.W (0,t)=D.R t*D.H*star (D.K*D.L 1*D.K)*D.Hp t*(D.K*D.L 1*D.K) := by
  simp only [W,square_left D.Kp D.U D.U_zero,Kp_one,D.L_zero,star_one,mul_one,U]
  simp only [star_mul,D.K_star]
  calc
    _ = D.R t*D.H*D.K*star (D.L 1)*((D.Hp t*D.K)*D.K)*D.L 1*D.K := by
      rw [mul_assoc (D.Hp t),D.KK,mul_one]
      simp only [mul_assoc]
    _ = _ := by rw [(D.Hp_commute t).eq]; simp only [mul_assoc]

lemma W_top (s : unitInterval) :
    D.W (s,1)=(D.K*D.L 1*D.K)*D.Kp s*star (D.L s) := by
  simp only [W,square_top,Kp_one,U,Hp_one,R]
  calc
    _ = D.H*D.K*D.H*D.L 1*star D.K*D.Kp s*star (D.L s) := by
      simp only [Unitary.star_eq_inv]; group
    _ = _ := by
      rw [D.commute.eq,mul_assoc D.K,D.HH,mul_one,D.K_star]

end Data
end KirchbergRordam.SymmetryConjugacyDiagram


namespace KirchbergRordam.SymmetryConjugacyDiagram
variable {A : Type*} [CStarAlgebra A]
lemma symmetry_mem (S : StarSubalgebra ℂ A) (u : unitary A)
    (hu : star (u:A)=u) (hm : (u:A) ∈ S) (r : ℝ) :
    (SymmetryFlow.flow u hu r : A) ∈ S := by
  exact S.add_mem (S.smul_mem (S.one_mem) _) (S.smul_mem hm _)
namespace Data
variable (D : Data A)


lemma W_bottom_mem (S : StarSubalgebra ℂ A) (hH : (D.H:A) ∈ S)
    (hL : ∀ t, (D.L t:A) ∈ S) (s : unitInterval) : (D.W (s,0):A) ∈ S := by
  rw [D.W_bottom]
  exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem hH (S.star_mem' (hL 1)))
    (symmetry_mem S D.H D.hH hH s)) (hL 1)) (S.star_mem' (hL s))
lemma W_right_mem (S : StarSubalgebra ℂ A) (hK : (D.K:A) ∈ S)
    (hR : ∀ t, (D.R t:A) ∈ S) (hcross : ((D.H*D.L 1*D.H):A) ∈ S)
    (t : unitInterval) : (D.W (1,t):A) ∈ S := by
  rw [D.W_right]
  apply S.mul_mem (S.mul_mem (hR t) (symmetry_mem S D.K D.hK hK t))
  have hh := S.star_mem' hcross
  change (D.H:A) * star (D.L 1:A) * (D.H:A) ∈ S
  simpa only [star_mul,D.hH,mul_assoc,StarSubalgebra.mem_carrier] using hh
lemma W_left_mem (S : StarSubalgebra ℂ A) (hH : (D.H:A) ∈ S)
    (hR : ∀ t, (D.R t:A) ∈ S) (hcross : ((D.K*D.L 1*D.K):A) ∈ S)
    (t : unitInterval) : (D.W (0,t):A) ∈ S := by
  rw [D.W_left]
  exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (hR t) hH) (S.star_mem' hcross))
    (symmetry_mem S D.H D.hH hH t)) hcross
lemma W_top_mem (S : StarSubalgebra ℂ A) (hK : (D.K:A) ∈ S)
    (hL : ∀ t, (D.L t:A) ∈ S) (hcross : ((D.K*D.L 1*D.K):A) ∈ S)
    (s : unitInterval) : (D.W (s,1):A) ∈ S := by
  rw [D.W_top]
  exact S.mul_mem (S.mul_mem hcross (symmetry_mem S D.K D.hK hK s)) (S.star_mem' (hL s))
end Data
end KirchbergRordam.SymmetryConjugacyDiagram
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimeSquare
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
open scoped CStarAlgebra ComplexOrder

namespace KirchbergRordam.PrimeSquareUnitary
open scoped CStarAlgebra ComplexOrder
open MatrixTensor PrimeDimensionDrop PrimeTensorSections FourLegSymmetries
variable {p q : ℕ}

variable (u : unitInterval → unitary (Fiber p q)) (hu : Continuous u) (h0 : u 0=1)

lemma R_eq (t : unitInterval) : ((diagram u hu h0).R t : (SquareFiber p q p q))=MatrixTensor.rightMatrix (ι:=Fin p×Fin q) (κ:=Fin p×Fin q) (u t : (Fiber p q)) := by
  exact conj_flip_left (u t : (Fiber p q))
lemma cross_H : (((diagram u hu h0).H*(diagram u hu h0).L 1*(diagram u hu h0).H):(SquareFiber p q p q)) ∈
    tensorRange (MatrixTensor.rightMatrix (ι:=Fin p) (κ:=Fin q)).range (MatrixTensor.leftMatrix (ι:=Fin p) (κ:=Fin q)).range := by
  change (H (P:=Fin p) (Q:=Fin q) : SquareFiber p q p q)*MatrixTensor.leftMatrix (u 1 : Fiber p q)*(H (P:=Fin p) (Q:=Fin q) : SquareFiber p q p q)∈_
  simpa only [Unitary.conjStarAlgAut_apply,H_selfadjoint] using H_cross_mem (u 1 : Fiber p q)
lemma cross_K : (((diagram u hu h0).K*(diagram u hu h0).L 1*(diagram u hu h0).K):(SquareFiber p q p q)) ∈
    tensorRange (MatrixTensor.leftMatrix (ι:=Fin p) (κ:=Fin q)).range (MatrixTensor.rightMatrix (ι:=Fin p) (κ:=Fin q)).range := by
  change (K (P:=Fin p) (Q:=Fin q) : SquareFiber p q p q)*MatrixTensor.leftMatrix (u 1 : Fiber p q)*(K (P:=Fin p) (Q:=Fin q) : SquareFiber p q p q)∈_
  simpa only [Unitary.conjStarAlgAut_apply,K_selfadjoint] using K_cross_mem (u 1 : Fiber p q)

lemma bottom (s : unitInterval) : ((diagram u hu h0).W (s,0):(SquareFiber p q p q))∈tensorRange (⊤ : StarSubalgebra ℂ (Fiber p q)) (MatrixTensor.leftMatrix (ι:=Fin p) (κ:=Fin q)).range := by
  apply (diagram u hu h0).W_bottom_mem
  · exact tensorRange_mono le_top le_rfl H_mem
  · intro t
    exact tensorRange_left _ _ trivial
lemma left (t : unitInterval) : ((diagram u hu h0).W (0,t):(SquareFiber p q p q))∈tensorRange (MatrixTensor.leftMatrix (ι:=Fin p) (κ:=Fin q)).range (⊤ : StarSubalgebra ℂ (Fiber p q)) := by
  apply (diagram u hu h0).W_left_mem
  · exact tensorRange_mono le_rfl le_top H_mem
  · intro t; rw [R_eq]; exact tensorRange_right _ _ trivial
  · exact tensorRange_mono le_rfl le_top (cross_K u hu h0)
lemma right (t : unitInterval) : ((diagram u hu h0).W (1,t):(SquareFiber p q p q))∈tensorRange (MatrixTensor.rightMatrix (ι:=Fin p) (κ:=Fin q)).range (⊤ : StarSubalgebra ℂ (Fiber p q)) := by
  apply (diagram u hu h0).W_right_mem
  · exact tensorRange_mono le_rfl le_top K_mem
  · intro t; rw [R_eq]; exact tensorRange_right _ _ trivial
  · exact tensorRange_mono le_rfl le_top (cross_H u hu h0)
lemma top (s : unitInterval) : ((diagram u hu h0).W (s,1):(SquareFiber p q p q))∈tensorRange (⊤ : StarSubalgebra ℂ (Fiber p q)) (MatrixTensor.rightMatrix (ι:=Fin p) (κ:=Fin q)).range := by
  apply (diagram u hu h0).W_top_mem
  · exact tensorRange_mono le_top le_rfl K_mem
  · intro t; exact tensorRange_left _ _ trivial
  · exact tensorRange_mono le_top le_rfl (cross_K u hu h0)

lemma corner00 : (diagram u hu h0).W (0,0)=(diagram u hu h0).H := by
  rw [(diagram u hu h0).W_bottom]
  simp [SymmetryConjugacyDiagram.Data.Hp,(diagram u hu h0).L_zero,mul_assoc]
lemma corner10 : (diagram u hu h0).W (1,0)=star ((diagram u hu h0).H*(diagram u hu h0).L 1*(diagram u hu h0).H) := by
  rw [(diagram u hu h0).W_right]
  simp only [(diagram u hu h0).R_zero,SymmetryConjugacyDiagram.Data.Kp,UnitaryConjugacySquare.symmetry,
    show ((0:unitInterval):ℝ)=0 from rfl,
    SymmetryFlow.flow_zero,one_mul,star_mul,(diagram u hu h0).H_star,mul_assoc]
lemma corner01 : (diagram u hu h0).W (0,1)=(diagram u hu h0).K*(diagram u hu h0).L 1*(diagram u hu h0).K := by
  rw [(diagram u hu h0).W_top]
  simp [SymmetryConjugacyDiagram.Data.Kp,(diagram u hu h0).L_zero]
lemma corner11 : (diagram u hu h0).W (1,1)=(diagram u hu h0).K := by
  rw [(diagram u hu h0).W_top]
  simp only [show ((1:unitInterval):ℝ)=1 from rfl,(diagram u hu h0).Kp_one]
  rw [mul_assoc ((diagram u hu h0).K*(diagram u hu h0).L 1), (diagram u hu h0).KK,mul_one]
  simp [mul_assoc]

lemma fibers_oai (x : Square) : ((diagram u hu h0).W x:(SquareFiber p q p q))∈fiberRange (p:=p) (q:=q) (r:=p) (k:=q) x := by
  rcases x with ⟨s,t⟩
  change _∈tensorRange (evaluation p q s).range (evaluation p q t).range
  by_cases hs0 : s=0
  · subst s
    rw [evaluation_zero_range]
    by_cases ht0 : t=0
    · subst t; rw [evaluation_zero_range,corner00]; exact H_mem
    by_cases ht1 : t=1
    · subst t; rw [evaluation_one_range,corner01]; exact cross_K u hu h0
    rw [evaluation_interior_range t ht0 ht1]; exact left u hu h0 t
  by_cases hs1 : s=1
  · subst s
    rw [evaluation_one_range]
    by_cases ht0 : t=0
    · subst t; rw [evaluation_zero_range,corner10]
      exact (tensorRange _ _).star_mem' (cross_H u hu h0)
    by_cases ht1 : t=1
    · subst t; rw [evaluation_one_range,corner11]; exact K_mem
    rw [evaluation_interior_range t ht0 ht1]; exact right u hu h0 t
  rw [evaluation_interior_range s hs0 hs1]
  by_cases ht0 : t=0
  · subst t; rw [evaluation_zero_range]; exact bottom u hu h0 s
  by_cases ht1 : t=1
  · subst t; rw [evaluation_one_range]; exact top u hu h0 s
  rw [evaluation_interior_range t ht0 ht1,tensorRange_top_top]
  trivial

end KirchbergRordam.PrimeSquareUnitary


end

end OAI
end

theorem solution : type_of% @OAI.KirchbergRordam.PrimeSquareUnitary.fibers_oai := @OAI.KirchbergRordam.PrimeSquareUnitary.fibers_oai
