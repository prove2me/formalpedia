-- Prove2me | solution 1 for OAI.KirchbergRordam.PrimeDropPresentation.HalfFlip.finite_stage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T17:30:58.852501+00:00
-- url     : https://prove2.me/submissions/443381a0-122e-4a93-b3c3-c3410d6178fd

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr014
import Definitions.Def_OAIB3Kr015
import Theorems.Thm_OAI_KirchbergRordam_PrimeSquareUnitary_exists_unitary
import Theorems.Thm_OAI_KirchbergRordam_PrimeTensorSections_irreducible_fiber_bound

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
-- module Solutions.OAIB3_Krc.CharacterCriterion_RepresentationTheory
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
namespace KirchbergRordam
namespace PureStates
variable (A : Type*) [CStarAlgebra A]

lemma normStates_compact : IsCompact (normStates A) := by
  have h := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 1).inter_right
    (isClosed_eq (WeakDual.eval_continuous (1 : A)) (continuous_const (y := (1 : ℂ))))
  convert h using 1
  ext φ
  simp [normStates, Metric.mem_closedBall]

end PureStates
end KirchbergRordam

open scoped InnerProductSpace
namespace KirchbergRordam

universe u

attribute [instance] IrreducibleRepresentation.normed IrreducibleRepresentation.inner
  IrreducibleRepresentation.complete IrreducibleRepresentation.nontrivial

end KirchbergRordam

namespace KirchbergRordam.PureStates
open scoped ComplexOrder
variable (A : Type*) [CStarAlgebra A] [Nontrivial A]
    [instPartialOrderA : PartialOrder A] [instStarOrderedRingA : StarOrderedRing A]
lemma exists_norming_dual (a : A) : ∃ φ : A →L[ℂ] ℂ,
    ‖φ‖ ≤ 1 ∧ φ 1=1 ∧ φ (star a*a)=(‖star a*a‖:ℂ) := by
  let b := star a * a
  have hb : 0 ≤ b := star_mul_self_nonneg a
  let : IsStarNormal b := (IsSelfAdjoint.of_nonneg hb).isStarNormal
  let S := StarAlgebra.elemental ℂ b
  have hs : (‖b‖ : ℂ) ∈ spectrum ℂ b := by
    exact spectrum.algebraMap_mem ℂ (CStarAlgebra.norm_mem_spectrum_of_nonneg hb)
  obtain ⟨χ,hχ⟩ := (StarAlgebra.elemental.bijective_characterSpaceToSpectrum b).surjective
    ⟨(‖b‖ : ℂ),hs⟩
  let g : S →ₐ[ℂ] ℂ := WeakDual.CharacterSpace.equivAlgHom χ
  let : StarHomClass (S →ₐ[ℂ] ℂ) S ℂ := AlgHomClass.instStarHomClass
  have hg : ‖g.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul, AlgHom.coe_toContinuousLinearMap] using NonUnitalStarAlgHom.norm_apply_le g x
  obtain ⟨ψ,hψ,hψnorm⟩ := exists_extension_norm_eq S.toSubalgebra.toSubmodule
    g.toContinuousLinearMap
  have hψ1 : ψ 1 = 1 := by
    exact (hψ (1 : S)).trans (map_one g)
  have hψb : ψ b = (‖b‖ : ℂ) := by
    have hh := congrArg Subtype.val hχ
    exact (hψ ⟨b,StarAlgebra.elemental.self_mem ℂ b⟩).trans hh
  exact ⟨ψ,hψnorm.trans_le hg,hψ1,hψb⟩


theorem exists_pure_norming (a : A) : ∃ φ : A →L[ℂ] ℂ,
    IsPure A φ ∧ (φ (star a*a)).re=‖star a*a‖ := by
  let b := star a*a
  let F : Set (WeakDual ℂ A) := {φ | φ ∈ normStates A ∧ (φ b).re=‖b‖}
  have hc : IsCompact F := (normStates_compact A).inter_right
    (isClosed_eq (Complex.continuous_re.comp (WeakDual.eval_continuous b)) continuous_const)
  have hn : F.Nonempty := by
    obtain ⟨φ,hφ,h1,hb⟩ := exists_norming_dual A a
    exact ⟨StrongDual.toWeakDual φ,⟨hφ,h1⟩,by change (φ b).re=‖b‖; rw [hb]; rfl⟩
  obtain ⟨φ,hφ⟩ := hc.extremePoints_nonempty hn
  refine ⟨φ.toStrongDual,⟨hφ.1.1,?_⟩,hφ.1.2⟩
  intro ψ hψ χ hχ he
  obtain ⟨s,t,hs,ht,hst,heq⟩ := he
  have hψb : (ψ b).re ≤ ‖b‖ := (Complex.re_le_norm _).trans <|
    (ψ.toStrongDual.le_opNorm b).trans (by nlinarith [norm_nonneg b,hψ.1])
  have hχb : (χ b).re ≤ ‖b‖ := (Complex.re_le_norm _).trans <|
    (χ.toStrongDual.le_opNorm b).trans (by nlinarith [norm_nonneg b,hχ.1])
  have hv := congrArg (fun f : WeakDual ℂ A => (f b).re) heq
  change ((s • ψ b+t • χ b):ℂ).re=(φ b).re at hv
  simp only [Complex.add_re,Complex.smul_re,smul_eq_mul] at hv
  rw [hφ.1.2] at hv
  have hw : s * ‖b‖ + t * ‖b‖ = ‖b‖ := by rw [← add_mul,hst,one_mul]
  have hψF : ψ ∈ F := ⟨hψ,by
    apply le_antisymm hψb
    by_contra! hlt
    nlinarith [mul_pos hs (sub_pos.mpr hlt), mul_nonneg ht.le (sub_nonneg.mpr hχb)]⟩
  have hχF : χ ∈ F := ⟨hχ,by
    apply le_antisymm hχb
    by_contra! hlt
    nlinarith [mul_pos ht (sub_pos.mpr hlt), mul_nonneg hs.le (sub_nonneg.mpr hψb)]⟩
  exact hφ.2 hψF hχF ⟨s,t,hs,ht,hst,heq⟩
end KirchbergRordam.PureStates

namespace KirchbergRordam

theorem irreducible_separate_zero {A : Type*} [CStarAlgebra A] [Nontrivial A]
    (a : A) (ha : ∀ π : IrreducibleRepresentation A, π.representation a=0) : a=0 := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  obtain ⟨φ,hp,hb⟩ := PureStates.exists_pure_norming A a
  let π := Representations.pureRepresentation φ hp
  have hz : φ (star a*a)=0 := by
    have hh := congrArg (fun f : A →L[ℂ] ℂ => f (star a*a))
      (Representations.pure_gns_coefficient φ hp)
    rw [Representations.coefficient_apply] at hh
    have hs : π.representation (star a*a)=0 := by rw [map_mul,ha π,mul_zero]
    have he := hs
    change (Representations.stateOfPure φ hp).gnsStarAlgHom (star a*a)=0 at he
    rw [he] at hh
    simpa using hh.symm
  rw [hz,Complex.zero_re] at hb
  apply norm_eq_zero.mp
  have hs : ‖star a * a‖ = ‖a‖ * ‖a‖ := CStarRing.norm_star_mul_self
  rw [← hb] at hs
  nlinarith [norm_nonneg a]
end KirchbergRordam
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


theorem sectionMap_injective : Function.Injective (sectionMap (p:=p) (q:=q) (r:=r) (k:=k)) := by
  cases subsingleton_or_nontrivial (MaxTensor.Algebra (Algebra p q) (Algebra r k))
  · exact fun _ _ _ => Subsingleton.elim _ _
  intro x y h
  have hz : sectionMap (x-y)=0 := by rw [map_sub,h,sub_self]
  apply sub_eq_zero.mp
  apply irreducible_separate_zero
  intro π
  obtain ⟨s,t,hst⟩ := irreducible_fiber_bound π
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [hz,ContinuousMap.zero_apply,norm_zero] using hst (x-y)

end KirchbergRordam.PrimeTensorSections
namespace KirchbergRordam.PrimeTensorSections
open scoped CStarAlgebra ComplexOrder TensorProduct
open PrimeDimensionDrop MatrixTensor ContinuousSectionLocality
variable {p q r k : ℕ}

lemma sectionMap_isometry : Isometry (sectionMap (p:=p) (q:=q) (r:=r) (k:=k)) :=
  NonUnitalStarAlgHom.isometry _ sectionMap_injective
end KirchbergRordam.PrimeTensorSections
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


namespace KirchbergRordam.UnitaryDisplacement
variable {A : Type*} [CStarAlgebra A]
lemma conj_mul (u v : unitary A) (a : A) : conj (u*v) a=conj u (conj v a) := by
  simp only [conj,Unitary.conjStarAlgAut_apply,Submonoid.coe_mul,star_mul,mul_assoc]
lemma conj_star (u : unitary A) (a : A) : conj (star u) (conj u a)=a := by
  simp only [conj,Unitary.conjStarAlgAut_apply,Unitary.coe_star,star_star]
  rw [← mul_assoc,← mul_assoc,u.property.1,one_mul,mul_assoc,u.property.1,mul_one]
lemma norm_sub (u : unitary A) (a b : A) : ‖conj u a-conj u b‖=‖a-b‖ := by
  rw [← map_sub,StarAlgEquiv.norm_map]
lemma displacement_mul (u v : unitary A) (a : A) :
    displacement (u*v) a ≤ displacement u a+displacement v a := by
  have he : conj (u*v) a-a = conj u (conj v a-a)+(conj u a-a) := by
    rw [map_sub,conj_mul]; abel
  unfold displacement
  rw [he]
  have h := norm_add_le (conj u (conj v a-a)) (conj u a-a)
  rw [StarAlgEquiv.norm_map] at h
  linarith

lemma displacement_conjugate (u v : unitary A) (a : A) :
    displacement (star u*v*u) a=displacement v (conj u a) := by
  unfold displacement
  rw [conj_mul,conj_mul,← StarAlgEquiv.norm_map (conj u),map_sub]
  have h : conj u (conj (star u) (conj v (conj u a))) = conj v (conj u a) := by
    simpa only [star_star] using conj_star (star u) (conj v (conj u a))
  rw [h]
lemma conj_eq_of_commute (u : unitary A) (a : A) (ha : Commute (u:A) a) : conj u a=a := by
  dsimp only [conj,Unitary.conjStarAlgAut_apply]
  rw [ha.eq,mul_assoc,u.property.2,mul_one]
lemma displacement_near_fixed (u : unitary A) (a b : A) (hb : conj u b=b) :
    displacement u a ≤ 2*‖a-b‖ := by
  have he : conj u a-a=(conj u a-conj u b)+(b-a) := by rw [hb]; abel
  unfold displacement
  rw [he]
  calc
    _ ≤ ‖conj u a-conj u b‖+‖b-a‖ := norm_add_le _ _
    _ = _ := by rw [norm_sub,norm_sub_rev]; ring
lemma transport_error (u : unitary A) (a a₀ b b₀ : A) :
    ‖conj u a-b‖ ≤ ‖a-a₀‖+‖conj u a₀-b₀‖+‖b₀-b‖ := by
  have he : conj u a-b=(conj u a-conj u a₀)+(conj u a₀-b₀)+(b₀-b) := by abel
  rw [he]
  calc
    _ ≤ ‖conj u a-conj u a₀‖+‖conj u a₀-b₀‖+‖b₀-b‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = _ := by rw [norm_sub]

end KirchbergRordam.UnitaryDisplacement


namespace KirchbergRordam.SymmetryConjugacyDiagram
section
open UnitaryConjugacySquare UnitaryDisplacement
variable {A : Type*} [CStarAlgebra A]
namespace Data
variable (D : Data A)
lemma Kp_fixes (a : A) (ha : Commute (D.K:A) a) (r : ℝ) : conj (D.Kp r) a=a :=
  conj_eq_of_commute _ _ (SymmetryFlow.flow_commute D.K D.hK a ha r)
lemma Hp_fixes (b : A) (hb : Commute (D.H:A) b) (r : ℝ) : conj (D.Hp r) b=b :=
  conj_eq_of_commute _ _ (SymmetryFlow.flow_commute D.H D.hH b hb r)

lemma U_control (a b : A) (hb : Commute (D.H:A) b) (r : ℝ) :
    displacement (D.U r) a ≤ 2*‖conj (D.L 1) a-b‖ := by
  rw [U,displacement_conjugate]
  exact displacement_near_fixed _ _ b (D.Hp_fixes b hb r)

lemma square_control (a b : A) (ha : Commute (D.K:A) a)
    (hb : Commute (D.H:A) b) (x : Square) :
    displacement (square D.Kp D.U x) a ≤ 2*‖conj (D.L 1) a-b‖ := by
  have hz (r : ℝ) : displacement (D.Kp r) a=0 := by
    simp [displacement,D.Kp_fixes a ha]
  unfold square
  calc
    _ ≤ displacement (D.Kp (ratio x)*D.U (radius x)) a+
        displacement (D.Kp (-((1-(x.1:ℝ))*ratio x))) a := displacement_mul _ _ _
    _ ≤ (displacement (D.Kp (ratio x)) a+displacement (D.U (radius x)) a)+0 :=
      add_le_add (displacement_mul _ _ _) (le_of_eq (hz _))
    _ ≤ _ := by simpa only [hz,zero_add,add_zero] using D.U_control a b hb (radius x)


theorem half_flip_control (a : unitInterval → A) (b : A)
    (ha : Commute (D.K:A) (a 0)) (hb : Commute (D.H:A) b)
    (δ : ℝ) (hn : ∀ t, ‖a t-a 0‖ ≤ δ)
    (hend : ‖conj (D.L 1) (a 0)-b‖ ≤ δ) (s t : unitInterval) :
    ‖conj (D.W (s,t)) (conj (D.L s) (a s))-
        conj (D.R t) (conj (D.H*D.K) (a t))‖ ≤ 4*δ := by
  have he : conj (D.W (s,t)) (conj (D.L s) (a s)) =
      conj (D.R t) (conj D.H (conj (square D.Kp D.U (s,t)) (a s))) := by
    simp only [W,UnitaryDisplacement.conj_mul,conj_star]
  rw [he,UnitaryDisplacement.conj_mul,UnitaryDisplacement.norm_sub,UnitaryDisplacement.norm_sub]
  have hk : conj D.K (a 0)=a 0 := conj_eq_of_commute _ _ ha
  have hnorm : ‖a 0-conj D.K (a t)‖=‖a t-a 0‖ := by
    calc
      _ = ‖conj D.K (a 0)-conj D.K (a t)‖ := by rw [hk]
      _ = _ := by rw [UnitaryDisplacement.norm_sub,norm_sub_rev]
  have h := transport_error (square D.Kp D.U (s,t)) (a s) (a 0) (conj D.K (a t)) (a 0)
  rw [hnorm] at h
  have hc := D.square_control (a 0) b ha hb (s,t)
  change ‖conj (square D.Kp D.U (s,t)) (a 0)-a 0‖ ≤ _ at hc
  linarith [hn s,hn t]
end Data
end
end KirchbergRordam.SymmetryConjugacyDiagram
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimeSquare
attribute [-instance] _root_.OAI.KirchbergRordam.MinTensor.instCStarRingAlgebra
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
end KirchbergRordam.PrimeSquareUnitary
namespace KirchbergRordam.PrimeSquareUnitary
open scoped CStarAlgebra ComplexOrder
open MatrixTensor PrimeDimensionDrop PrimeTensorSections FourLegSymmetries
open UnitaryDisplacement
variable {p q : ℕ}

lemma conj_map {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (u : unitary A) (a : A) :
    conj (Unitary.map (StarMonoidHom.ofClass φ) u) (φ a)=φ (conj u a) := by
  change φ (u:A)*φ a*star (φ (u:A))=φ ((u:A)*a*star (u:A))
  rw [map_mul,map_mul,map_star]
lemma conj_commute (u : unitary (SquareFiber p q p q)) (a : (SquareFiber p q p q)) (h : conj u a=a) : Commute (u:(SquareFiber p q p q)) a := by
  have hh := congrArg (fun x : (SquareFiber p q p q) => x*(u:(SquareFiber p q p q))) h
  change (u:SquareFiber p q p q)*a=a*(u:SquareFiber p q p q)
  simpa only [conj,Unitary.conjStarAlgAut_apply,mul_assoc,Unitary.coe_star_mul_self,mul_one] using hh

lemma pointwise_control (u : unitInterval → unitary (Fiber p q)) (hu : Continuous u) (h0 : u 0=1)
    (f : PrimeDimensionDrop.Algebra p q) (δ : ℝ)
    (hf : ∀ t, ‖conj (star (u t)) (f.val t)-f.val 0‖≤δ) (s t : unitInterval) :
    ‖conj ((diagram u hu h0).W (s,t)) (MatrixTensor.leftMatrix (f.val s))-
      MatrixTensor.rightMatrix (f.val t)‖≤4*δ := by
  let a : unitInterval → (SquareFiber p q p q) := fun t => MatrixTensor.leftMatrix (conj (star (u t)) (f.val t))
  let b : (SquareFiber p q p q) := MatrixTensor.leftMatrix (f.val 1)
  have ha0 : a 0=MatrixTensor.leftMatrix (f.val 0) := by simp [a,h0,conj]
  have ha : Commute ((diagram u hu h0).K:(SquareFiber p q p q)) (a 0) := by
    rw [ha0]
    obtain ⟨v,hv⟩ := f.property.1
    change MatrixTensor.leftMatrix v=f.val 0 at hv
    rw [←hv]
    exact conj_commute _ _ (conj_K_left_left v)
  have hb : Commute ((diagram u hu h0).H:(SquareFiber p q p q)) b := by
    obtain ⟨v,hv⟩ := f.property.2
    change Commute _ (MatrixTensor.leftMatrix (f.val 1))
    change MatrixTensor.rightMatrix v=f.val 1 at hv
    rw [←hv]
    exact conj_commute _ _ (conj_H_left_right v)
  have haN (r : unitInterval) : ‖a r-a 0‖≤δ := by
    rw [ha0]
    change ‖MatrixTensor.leftMatrix _-MatrixTensor.leftMatrix _‖≤δ
    rw [←map_sub]
    exact (NonUnitalStarAlgHom.norm_apply_le (MatrixTensor.leftMatrix (ι:=Fin p×Fin q) (κ:=Fin p×Fin q)) _).trans (hf r)
  have hcancel (r : unitInterval) : conj ((diagram u hu h0).L r) (a r)=MatrixTensor.leftMatrix (f.val r) := by
    rw [show (diagram u hu h0).L r=Unitary.map (StarMonoidHom.ofClass (MatrixTensor.leftMatrix (ι:=Fin p×Fin q) (κ:=Fin p×Fin q))) (u r) from rfl]
    change conj (Unitary.map (StarMonoidHom.ofClass (MatrixTensor.leftMatrix (ι:=Fin p×Fin q) (κ:=Fin p×Fin q))) (u r))
      (MatrixTensor.leftMatrix (conj (star (u r)) (f.val r)))=_
    rw [conj_map]
    congr 1
    simpa only [star_star] using conj_star (star (u r)) (f.val r)
  have hend : ‖conj ((diagram u hu h0).L 1) (a 0)-b‖≤δ := by
    change ‖conj ((diagram u hu h0).L 1) (a 0)-MatrixTensor.leftMatrix (f.val 1)‖≤δ
    rw [←hcancel 1,norm_sub,norm_sub_rev]
    exact haN 1
  have hh := (diagram u hu h0).half_flip_control a b ha hb δ haN hend s t
  rw [hcancel] at hh
  have hr : conj ((diagram u hu h0).R t)
      (conj ((diagram u hu h0).H*(diagram u hu h0).K) (a t))=MatrixTensor.rightMatrix (f.val t) := by
    change conj ((diagram u hu h0).R t) (conj (H*K) (MatrixTensor.leftMatrix (conj (star (u t)) (f.val t))))=_
    rw [conj_flip_left]
    have hm : (diagram u hu h0).R t=Unitary.map
        (StarMonoidHom.ofClass (MatrixTensor.rightMatrix (ι:=Fin p×Fin q) (κ:=Fin p×Fin q))) (u t) :=
      Subtype.ext (R_eq u hu h0 t)
    rw [hm,conj_map]
    congr 1
    simpa only [star_star] using conj_star (star (u t)) (f.val t)
  rwa [hr] at hh

lemma norm_bound_in_sections {A B X : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [TopologicalSpace X] [CompactSpace X] (φ : A →⋆ₐ[ℂ] C(X,B)) (hφ : Isometry φ)
    (w : unitary A) (a b : A) (c : ℝ) (hc : 0≤c)
    (h : ∀ x, ‖(φ (w:A)) x*(φ a) x*star ((φ (w:A)) x)-(φ b) x‖≤c) :
    ‖conj w a-b‖≤c := by
  rw [←hφ.norm_map_of_map_zero (map_zero φ)]
  apply (ContinuousMap.norm_le _ hc).mpr
  intro x
  simpa only [conj,Unitary.conjStarAlgAut_apply,map_sub,map_mul,map_star,
    ContinuousMap.sub_apply,ContinuousMap.mul_apply,ContinuousMap.star_apply] using h x


theorem exists_half_flip_control (u : unitInterval → unitary (Fiber p q))
    (hu : Continuous u) (h0 : u 0=1) :
    ∃ w : unitary (MaxTensor.Algebra (PrimeDimensionDrop.Algebra p q) (PrimeDimensionDrop.Algebra p q)),
      ∀ (f : PrimeDimensionDrop.Algebra p q) (δ : ℝ),
        (∀ t, ‖conj (star (u t)) (f.val t)-f.val 0‖≤δ) →
        ‖conj w (MaxTensor.includeLeft f)-MaxTensor.includeRight f‖≤4*δ := by
  obtain ⟨w,hw⟩ := exists_unitary u hu h0
  refine ⟨w,fun f δ hf => ?_⟩
  have hδ : 0≤δ := (norm_nonneg _).trans (hf 0)
  apply norm_bound_in_sections sectionMap sectionMap_isometry w
    (MaxTensor.includeLeft f) (MaxTensor.includeRight f) (4*δ) (by positivity)
  intro x
  rcases x with ⟨s,t⟩
  rw [hw,sectionMap_left,sectionMap_right]
  exact pointwise_control u hu h0 f δ hf s t
end KirchbergRordam.PrimeSquareUnitary


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_DiagonalIteration
attribute [-instance] _root_.OAI.KirchbergRordam.MinTensor.instCStarRingAlgebra
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

namespace KirchbergRordam.DiagonalIteration
open scoped CStarAlgebra ComplexOrder
open Filter Topology
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
lemma conj_mul (u v : unitary A) (a : A) : conj (u*v) a=conj u (conj v a) := by
  simp [conj,Unitary.conjStarAlgAut_apply,mul_assoc]
lemma conj_star (u : unitary A) (a : A) : conj (star u) (conj u a)=a := by
  simp only [conj,Unitary.conjStarAlgAut_apply,Unitary.coe_star,star_star]
  rw [←mul_assoc,←mul_assoc,u.property.1,one_mul,mul_assoc,u.property.1,mul_one]
lemma normalize_cancel (u v : unitary A) (a : A) :
    conj (star (u*star v)) (conj u a)=conj v a := by
  rw [star_mul,star_star,conj_mul,conj_star]

lemma map_pi_conj {ι : Type*} [Fintype ι] (φ : (ι→A) →⋆ₐ[ℂ] B)
    (v : ι→unitary A) (a : ι→A) : φ (fun i => conj (v i) (a i)) =
      conj (Unitary.map (StarMonoidHom.ofClass φ) (piUnitary v)) (φ a) := by
  change φ ((fun i => (v i:A))*a*star (fun i => (v i:A)))=
    φ (fun i => (v i:A))*φ a*star (φ (fun i => (v i:A)))
  rw [map_mul,map_mul,map_star]

attribute [instance] System.cstar System.finite
namespace System
variable (S : System)

lemma full_eq (n k : ℕ) (f : unitInterval → S.obj n) (t : unitInterval) :
    S.full n k f t=conj (S.unitaryPath n k t) (S.flat n k f t) := by
  induction k generalizing t with
  | zero => exact (conj_one _).symm
  | succ k ih =>
    simp only [full,flat,unitaryPath,ih,map_pi_conj,conj_mul]
    rfl

lemma flat_bound (hlip : ∀ n i, LipschitzWith (1/2) (S.eigen n i))
    (n k : ℕ) (f : unitInterval → S.obj n) (ε r : ℝ) (hε : 0≤ε)
    (hf : ∀ s t : unitInterval, dist s t ≤ (1/2:ℝ)^k*r → ‖f s-f t‖≤ε)
    (s t : unitInterval) (hst : dist s t≤r) :
    ‖S.flat n k f s-S.flat n k f t‖≤ε := by
  induction k generalizing r s t with
  | zero => exact hf s t (by simpa using hst)
  | succ k ih =>
    rw [flat,flat,←map_sub]
    apply (NonUnitalStarAlgHom.norm_apply_le (S.diagonal (n+k)) _).trans
    apply (pi_norm_le_iff_of_nonneg hε).mpr
    intro i
    apply ih (r/2)
    · intro x y hxy
      apply hf x y
      convert hxy using 1; ring
    · calc
        dist (S.eigen (n+k) i s) (S.eigen (n+k) i t) ≤
            (1/2:ℝ)*dist s t := (hlip (n+k) i).dist_le_mul s t
        _ ≤ r/2 := by linarith

lemma flat_eventually_small (hlip : ∀ n i, LipschitzWith (1/2) (S.eigen n i))
    (n : ℕ) (f : C(unitInterval,S.obj n)) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k in atTop, ∀ s t : unitInterval, ‖S.flat n k f s-S.flat n k f t‖≤ε := by
  obtain ⟨δ,hδ,hf⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous) ε hε
  have hp : Tendsto (fun k : ℕ => (1/2:ℝ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [hp.eventually (gt_mem_nhds hδ)] with k hk s t
  apply S.flat_bound hlip n k f ε 1 hε.le
  · intro x y hxy
    apply le_of_lt
    rw [←dist_eq_norm]
    apply hf
    exact lt_of_le_of_lt (by simpa using hxy) hk
  · change |(s:ℝ)-(t:ℝ)|≤1
    exact abs_le.mpr ⟨by linarith [s.property.1,t.property.2],by linarith [s.property.2,t.property.1]⟩
end System
end KirchbergRordam.DiagonalIteration
namespace KirchbergRordam.BalancedDropHalfFlip
open scoped CStarAlgebra ComplexOrder
open Filter Topology
open UnitaryDisplacement
universe u

variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
lemma squareMap_left (φ : A →⋆ₐ[ℂ] B) (a : A) :
    squareMap φ (MaxTensor.includeLeft a)=MaxTensor.includeLeft (φ a) := by
  exact DFunLike.congr_fun (MaxTensor.lift_includeLeft _ _ _) a
lemma squareMap_right (φ : A →⋆ₐ[ℂ] B) (a : A) :
    squareMap φ (MaxTensor.includeRight a)=MaxTensor.includeRight (φ a) := by
  exact DFunLike.congr_fun (MaxTensor.lift_includeRight _ _ _) a

lemma control_map (φ : A →⋆ₐ[ℂ] B) (w : unitary (MaxTensor.Algebra A A)) (a : A) :
    ‖conj (Unitary.map (StarMonoidHom.ofClass (squareMap φ)) w)
        (MaxTensor.includeLeft (φ a))-MaxTensor.includeRight (φ a)‖≤
      ‖conj w (MaxTensor.includeLeft a)-MaxTensor.includeRight a‖ := by
  rw [←squareMap_left,←squareMap_right,PrimeSquareUnitary.conj_map,←map_sub]
  exact NonUnitalStarAlgHom.norm_apply_le (squareMap φ) _

end KirchbergRordam.BalancedDropHalfFlip
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_GeneralSystem
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
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.GeneralDropSystem
open MatrixDiagonalPath MatrixBlockReindex
open BalancedDropSystem (half lowerPath upperPath lower_zero lower_one upper_zero upper_one)
open scoped CStarAlgebra Matrix ComplexOrder

variable {p q P Q : ℕ} (d : Data p q P Q)
lemma eigen_lipschitz (i : Slot d) : LipschitzWith (1/2) (eigenpath d i) := by
  rcases i with i|i|i
  · apply LipschitzWith.of_dist_le_mul
    intro s t
    change |(s:ℝ)/2-(t:ℝ)/2|≤(1/2:ℝ)*|(s:ℝ)-(t:ℝ)|
    rw [←sub_div,abs_div]
    norm_num
    linarith
  · apply LipschitzWith.of_dist_le_mul
    intro s t
    change |((s:ℝ)+1)/2-((t:ℝ)+1)/2|≤(1/2:ℝ)*|(s:ℝ)-(t:ℝ)|
    rw [←sub_div,add_sub_add_right_eq_sub,abs_div]
    norm_num
    linarith
  · exact (LipschitzWith.const _).weaken (by norm_num)
end KirchbergRordam.GeneralDropSystem
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimePresentation
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
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.PrimeDropPresentation
open scoped CStarAlgebra ComplexOrder
variable (S : PrimeDropPresentation)
lemma inclusion_map (i j : ℕ) (hij : i≤j) (x : S.Stage i) :
    S.inclusion j (S.chain.map i j hij x)=S.inclusion i x := CStarInductiveLimit.of_map _ _ _ _ _
end KirchbergRordam.PrimeDropPresentation
namespace KirchbergRordam.PrimeDropPresentation.Iteration
open scoped CStarAlgebra ComplexOrder
open Filter Topology
open MatrixDiagonalPath DiagonalIteration GeneralDropSystem
variable (S : PrimeDropPresentation)

lemma eigen_lipschitz : ∀ n i, LipschitzWith (1/2) ((diagonalSystem S).eigen n i) :=
  fun n i => GeneralDropSystem.eigen_lipschitz (S.stepData n) i

lemma iterate_full (n k : ℕ) (f : S.Stage n) (t : unitInterval) :
    (S.chain.map n (n+k) (Nat.le_add_right n k) f).val t =
      (diagonalSystem S).full n k f.val t := by
  induction k generalizing t with
  | zero => simp only [Nat.add_zero,S.chain.map_self,DiagonalIteration.System.full]; rfl
  | succ k ih =>
    erw [S.chain.map_succ n (n+k) (Nat.le_add_right n k)]
    change MatrixDiagonalPath.interpolate _ _ t
      (block (fun i => (S.chain.map n (n+k) _ f).val (eigenpath (S.stepData (n+k)) i t))) = _
    simp only [ih]
    rfl

lemma untwist (n k : ℕ) (f : S.Stage n) (t : unitInterval) :
    conj (star (normalizedPath S n k t))
      ((S.chain.map n (n+k) (Nat.le_add_right n k) f).val t) =
      conj ((diagonalSystem S).unitaryPath n k 0) ((diagonalSystem S).flat n k f.val t) := by
  rw [iterate_full S,(diagonalSystem S).full_eq]
  exact DiagonalIteration.normalize_cancel _ _ _

lemma untwist_norm (n k : ℕ) (f : S.Stage n) (t : unitInterval) :
    ‖conj (star (normalizedPath S n k t))
      ((S.chain.map n (n+k) (Nat.le_add_right n k) f).val t)-
      (S.chain.map n (n+k) (Nat.le_add_right n k) f).val 0‖ =
      ‖(diagonalSystem S).flat n k f.val t-(diagonalSystem S).flat n k f.val 0‖ := by
  rw [untwist S,iterate_full S,(diagonalSystem S).full_eq]
  rw [←map_sub,StarAlgEquiv.norm_map]

lemma eventually_untwist_small (n : ℕ) (f : S.Stage n) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k in atTop, ∀ t : unitInterval,
      ‖conj (star (normalizedPath S n k t))
        ((S.chain.map n (n+k) (Nat.le_add_right n k) f).val t)-
        (S.chain.map n (n+k) (Nat.le_add_right n k) f).val 0‖≤ε := by
  filter_upwards [(diagonalSystem S).flat_eventually_small (eigen_lipschitz S) n f.val ε hε] with k hk t
  rw [untwist_norm S]
  exact hk t 0
end KirchbergRordam.PrimeDropPresentation.Iteration
namespace KirchbergRordam.PrimeDropPresentation.HalfFlip
open scoped CStarAlgebra ComplexOrder
open Filter Topology
open PrimeDropPresentation.Iteration
open UnitaryDisplacement BalancedDropHalfFlip

lemma mappedUnitary_control {A B : Type} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (w : unitary (MaxTensor.Algebra A A)) (a : A) :
    ‖conj (mappedUnitary φ w) (MaxTensor.includeLeft (φ a))-MaxTensor.includeRight (φ a)‖≤
      ‖conj w (MaxTensor.includeLeft a)-MaxTensor.includeRight a‖ := by
  exact control_map φ w a
variable (S : PrimeDropPresentation)
lemma finite_stage_oai (n : ℕ) (F : Finset (S.Stage n)) (ε : ℝ) (hε : 0<ε) :
    ∃ w : unitary (MaxTensor.Algebra S.Algebra S.Algebra), ∀ f∈F,
      ‖conj w (MaxTensor.includeLeft (S.inclusion n f))-
        MaxTensor.includeRight (S.inclusion n f)‖≤ε := by
  have he : ∀ᶠ k in atTop, ∀ f∈F, ∀ t : unitInterval,
      ‖conj (star (normalizedPath S n k t))
        ((S.chain.map n (n+k) (Nat.le_add_right n k) f).val t)-
        (S.chain.map n (n+k) (Nat.le_add_right n k) f).val 0‖≤ε/4 := by
    apply (Filter.eventually_all_finset F).mpr
    intro f hf
    exact eventually_untwist_small S n f (ε/4) (by positivity)
  obtain ⟨k,hk⟩ := he.exists
  obtain ⟨w,hw⟩ := PrimeSquareUnitary.exists_half_flip_control (p:=S.size (n+k)) (q:=S.size (n+k)+1) (normalizedPath S n k)
    (normalizedPath_continuous S n k) (normalizedPath_zero S n k)
  refine ⟨mappedUnitary (S.inclusion (n+k)) w,fun f hf => ?_⟩
  have hc := (mappedUnitary_control (S.inclusion (n+k)) w (S.chain.map n (n+k) (Nat.le_add_right n k) f)).trans
    (hw _ (ε/4) (hk f hf))
  have hm : S.inclusion (n+k) (S.chain.map n (n+k) (Nat.le_add_right n k) f)=S.inclusion n f :=
    S.inclusion_map n (n+k) (Nat.le_add_right n k) f
  rw [hm] at hc
  have he : 4*(ε/4)=ε := by ring
  rwa [he] at hc

end KirchbergRordam.PrimeDropPresentation.HalfFlip
end

end OAI
end

theorem solution : type_of% @OAI.KirchbergRordam.PrimeDropPresentation.HalfFlip.finite_stage_oai := @OAI.KirchbergRordam.PrimeDropPresentation.HalfFlip.finite_stage_oai
