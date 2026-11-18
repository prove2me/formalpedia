-- Prove2me | solution 1 for OAI.ElementaryPositivity.RawShuffle.slopeStringCoefficient_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T19:49:22.002585+00:00
-- url     : https://prove2.me/submissions/9b7afad9-bccc-471b-be10-8b2f49c42583

import Mathlib
import Definitions.Def_OAIQ368Chrom051
import Definitions.Def_OAIQ368Chrom052
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_primitiveBasisFamilyWords_independent
import Definitions.Def_OAIQ368Chrom001
import Definitions.Def_OAIQ368Chrom017
import Definitions.Def_OAIQ368Chrom021
import Definitions.Def_OAIQ368Chrom022
import Definitions.Def_OAIQ368Chrom023
import Definitions.Def_OAIQ368Chrom026
import Definitions.Def_OAIQ368Chrom027
import Definitions.Def_OAIQ368Chrom030
import Definitions.Def_OAIQ368Chrom035
import Definitions.Def_OAIQ368Chrom040

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TensorFiltrationInterchange
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
variable {M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
lemma map_eq_zero (F F' : Submodule ℚ M) (G G' : Submodule ℚ N)
    (f : M →ₗ[ℚ] N) (h : ∀ x∈F,f x∈G) (h' : ∀ x∈F',f x∈G')
    (hz : ∀ x∈F,f x∈G') : map F F' G G' f h h'=0 := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change Submodule.Quotient.mk (restrict F G f h x) = (0 : G ⧸ next G G')
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hz x.val x.property)
end ElementaryPositivity.LinearFiltration

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_OriginalDegree
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma associatedComponent_upper (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (hd : d≠0) (hθ : SlopeArithmetic.slope c η d=θ)
    (W ℓ : ℤ) (hw : 2*ℓ+eulerForm a d d<W) :
    associatedComponent a c η hc θ d W ℓ=0 := by
  apply LinearFiltration.map_eq_zero
  intro f hf
  have hmem : componentB a (SlopeArithmetic.slope c η) d ℓ f∈
      gradeB a (SlopeArithmetic.slope c η) d ℓ ⊓ sourceFiltration a c η hc θ d W :=
    ⟨⟨f,rfl⟩,sourceFiltration_component_mem a c η hc θ d W ℓ f hf⟩
  rw [sourceFiltration_upper a c η hc θ d hd hθ ℓ W hw] at hmem
  rw [Submodule.mem_bot] at hmem
  rw [hmem]
  exact (sourceFiltration a c η hc θ d (W+1)).zero_mem

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalLocalPrimitives
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial CommonTranslation
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma meanS_homogeneous (d : I → ℕ) :
    (meanS d).val.IsWeightedHomogeneous (fun _=>(1:ℤ)) 1 := by
  classical
  apply (weightedHomogeneousSubmodule ℚ (fun _ : (Σ i,Fin (d i))=>(1:ℤ)) 1).smul_mem
  exact IsWeightedHomogeneous.sum _ _ 1 (fun v _=>isWeightedHomogeneous_X ℚ (fun _=>(1:ℤ)) v)

omit [DecidableEq I] in
lemma componentS_mean (d : I → ℕ) (ℓ : ℤ) (f : S d) :
    componentS d (ℓ+1) (meanS d*f)=meanS d*componentS d ℓ f := by
  apply Subtype.ext
  change weightedHomogeneousComponent (fun _=>(1:ℤ)) (ℓ+1) ((meanS d).val*f.val)=_
  rw [add_comm ℓ 1,Homogeneity.component_mul _ _ (meanS_homogeneous d) ℓ]
  rfl

lemma meanMultiplyB_component (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) (ℓ : ℤ) (f : B a μ d) :
    componentB a μ d (ℓ+1) (meanMultiplyB a μ d f)=meanMultiplyB a μ d (componentB a μ d ℓ f) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change componentB a μ d (ℓ+1) (quotientAlg a μ d (meanS d)*quotientAlg a μ d f)=
      quotientAlg a μ d (meanS d)*quotientAlg a μ d (componentS d ℓ f)
    rw [←map_mul,←map_mul]
    change quotientAlg a μ d (componentS d (ℓ+1) (meanS d*f))=_
    rw [componentS_mean]

variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)

lemma gradeMeanMultiply_component (d : I → ℕ) (W ℓ : ℤ) (f : SourceAssociatedGrade a c η hc θ d W) :
    associatedComponent a c η hc θ d W (ℓ+1) (gradeMeanMultiply a c η hc θ d W f)=
      gradeMeanMultiply a c η hc θ d W (associatedComponent a c η hc θ d W ℓ f) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    apply congrArg (LinearFiltration.mk (sourceFiltration a c η hc θ d W) (sourceFiltration a c η hc θ d (W+1)))
    apply Subtype.ext
    exact meanMultiplyB_component a (SlopeArithmetic.slope c η) d ℓ f.val

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.instAddCommGroupSubtypeSourceAssociatedGradeMemSubmoduleRatPrimitiveSpace
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.instModuleRatSubtypeSourceAssociatedGradeMemSubmodulePrimitiveSpace
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.instAddCommGroupSubtypeSourceAssociatedGradeMemSubmoduleRatPrimitiveSpaceKerPrimitiveDerivative
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.instModuleRatSubtypeSourceAssociatedGradeMemSubmodulePrimitiveSpaceKerPrimitiveDerivative
lemma primitiveMeanMultiply_component (ℓ : ℤ) (x : primitiveSpace a c η hc θ hχ d W) :
    primitiveComponent a c η hc θ hχ d W (ℓ+1) (primitiveMeanMultiply a c η hc θ hχ d W x)=
      primitiveMeanMultiply a c η hc θ hχ d W (primitiveComponent a c η hc θ hχ d W ℓ x) :=
  Subtype.ext (gradeMeanMultiply_component a c η hc θ d W ℓ x.val)

lemma stringBaseDegree_spec (i : StringBaseIndex a c η hc θ hχ d W) :
    primitiveComponent a c η hc θ hχ d W (stringBaseDegree a c η hc θ hχ d W i)
      (homogeneousStringBaseBasis a c η hc θ hχ d W i).val=
      (homogeneousStringBaseBasis a c η hc θ hχ d W i).val :=
  congrArg Subtype.val (homogeneousStringBaseBasis_exists_degree a c η hc θ hχ d W i).choose_spec

lemma primitiveMeanMultiply_pow_component (ℓ : ℤ) (n : ℕ) (x : primitiveSpace a c η hc θ hχ d W)
    (hx : primitiveComponent a c η hc θ hχ d W ℓ x=x) :
    primitiveComponent a c η hc θ hχ d W (ℓ+n) ((primitiveMeanMultiply a c η hc θ hχ d W^n) x)=
      ((primitiveMeanMultiply a c η hc θ hχ d W^n) x) := by
  induction n with
  | zero => simpa only [Nat.cast_zero,add_zero,pow_zero,Module.End.one_apply] using hx
  | succ n ih =>
    rw [Nat.cast_succ,←add_assoc,pow_succ',Module.End.mul_apply,primitiveMeanMultiply_component,ih]

lemma homogeneousPrimitiveStringBasis_apply (hd : d≠0)
    (i : Σ _ : ℕ,StringBaseIndex a c η hc θ hχ d W) :
    homogeneousPrimitiveStringBasis a c η hc θ hχ d W hd i=
      (primitiveMeanMultiply a c η hc θ hχ d W^i.1) (homogeneousStringBaseBasis a c η hc θ hχ d W i.2).val := by
  rw [homogeneousPrimitiveStringBasis,Module.Basis.map_apply,Finsupp.coe_basis]
  exact PrimitiveStrings.evaluate_single _ _ _ _

lemma homogeneousPrimitiveStringBasis_degree (hd : d≠0)
    (i : Σ _ : ℕ,StringBaseIndex a c η hc θ hχ d W) :
    primitiveComponent a c η hc θ hχ d W (stringBaseDegree a c η hc θ hχ d W i.2+i.1)
      (homogeneousPrimitiveStringBasis a c η hc θ hχ d W hd i)=
      homogeneousPrimitiveStringBasis a c η hc θ hχ d W hd i := by
  rw [homogeneousPrimitiveStringBasis_apply]
  exact primitiveMeanMultiply_pow_component a c η hc θ hχ d W _ _ _
    (stringBaseDegree_spec a c η hc θ hχ d W i.2)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalPBWBasis
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable Classical.decEq
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*} [LinearOrder J] (b : J → UnitalShuffle a c η hc θ)
  (w : J → SlopeWeight c η hc θ)
  (hw : ∀ i,b i∈globalHomogeneous a c η hc θ (w i))
  (hp : ∀ i,b i∈globalPrimitives a c η hc θ)
  (hspan : Submodule.span ℚ (Set.range b)=globalPrimitives a c η hc θ)
  (hli : LinearIndependent ℚ b)

lemma primitiveBasisPBW_apply (l : PBWWord a c η hc θ w) :
    primitiveBasisPBW a c η hc θ b w hw hp hspan hli l=primitiveWord a c η hc θ b l.val :=
  Module.Basis.mk_apply _ _ _

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalPrimitiveStrings
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

lemma globalStringPBWBasis_apply (l : PBWWord a c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val)) :
    globalStringPBWBasis a c η hc θ l=primitiveWord a c η hc θ (globalStringFamily a c η hc θ) l.val :=
  primitiveBasisPBW_apply a c η hc θ _ _ _ _ _ _ l

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalOriginalDegree
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)

lemma unitalOriginalHomogeneous_representative (d : I → ℕ) (W ℓ : ℤ)
    (x : UnitalSourceGrade a c η hc θ d W) (hx : x∈unitalOriginalHomogeneous a c η hc θ d W ℓ) :
    ∃ f : unitalSourceFiltration a c η hc θ d W,
      f.val∈gradeB a (slope c η) d ℓ ∧ Submodule.Quotient.mk f=x := by
  obtain ⟨f,rfl⟩:=(LinearFiltration.next _ _).mkQ_surjective x
  refine ⟨⟨componentB a (slope c η) d ℓ f.val,
    unitalSourceFiltration_component_mem a c η hc θ d W ℓ f.val f.property⟩,⟨f.val,rfl⟩,?_⟩
  exact (mem_unitalOriginalHomogeneous a c η hc θ d W ℓ _).mp hx

lemma unitalOriginalHomogeneous_mk (d : I → ℕ) (W ℓ : ℤ)
    (f : unitalSourceFiltration a c η hc θ d W) (hf : f.val∈gradeB a (slope c η) d ℓ) :
    (Submodule.Quotient.mk f : UnitalSourceGrade a c η hc θ d W)∈
      unitalOriginalHomogeneous a c η hc θ d W ℓ := by
  apply (mem_unitalOriginalHomogeneous a c η hc θ d W ℓ _).mpr
  rw [unitalAssociatedComponent_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact (mem_gradeB_iff a (slope c η) d ℓ f.val).mp hf

lemma shuffleBUnit_graded (d e : I → ℕ)
    (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (m n : ℤ)
    (f : B a (slope c η) d) (g : B a (slope c η) e)
    (hf : f∈gradeB a (slope c η) d m) (hg : g∈gradeB a (slope c η) e n) :
    shuffleBUnit a c η hc d e hs f g∈gradeB a (slope c η) (d+e) (m+n-eulerForm a d e) := by
  obtain ⟨f,hfp,rfl⟩:=gradeB_homogeneous_representative a _ d m f hf
  obtain ⟨g,hgp,rfl⟩:=gradeB_homogeneous_representative a _ e n g hg
  rw [shuffleBUnit_mk,mem_gradeB_iff,componentB_mk,
    componentS_of_homogeneous _ _ (shufflePolynomial_homogeneous a f g hfp hgp),ite_eq_left rfl]

lemma unitalGradeShuffle_original (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e) (U V m n : ℤ)
    (x : UnitalSourceGrade a c η hc θ d U) (y : UnitalSourceGrade a c η hc θ e V)
    (hx : x∈unitalOriginalHomogeneous a c η hc θ d U m)
    (hy : y∈unitalOriginalHomogeneous a c η hc θ e V n) :
    unitalGradeShuffle a c η hc θ hχ d e hd he U V x y∈
      unitalOriginalHomogeneous a c η hc θ (d+e) (U+V) (m+n-eulerForm a d e) := by
  obtain ⟨x,hfx,rfl⟩:=unitalOriginalHomogeneous_representative a c η hc θ d U m x hx
  obtain ⟨y,hgy,rfl⟩:=unitalOriginalHomogeneous_representative a c η hc θ e V n y hy
  rw [unitalGradeShuffle_mk]
  exact unitalOriginalHomogeneous_mk a c η hc θ _ _ _ _
    (shuffleBUnit_graded a c η hc d e (hd.compatible he) m n x.val y.val hfx hgy)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [hχ : Fact (SlopeEulerSymmetric a c η θ)]

lemma globalOriginalHomogeneous_mul {k l : SlopeWeight c η hc θ} {m n : ℤ}
    {x y : UnitalShuffle a c η hc θ}
    (hx : x∈globalOriginalHomogeneous a c η hc θ k m)
    (hy : y∈globalOriginalHomogeneous a c η hc θ l n) :
    x*y∈globalOriginalHomogeneous a c η hc θ (k+l) (m+n-eulerForm a k.1.val l.1.val) := by
  obtain ⟨x,hx,rfl⟩:=hx
  obtain ⟨y,hy,rfl⟩:=hy
  exact ⟨GradedMonoid.GMul.mul x y,
    unitalGradeShuffle_original a c η hc θ hχ.out k.1.val l.1.val k.1.property l.1.property k.2 l.2 m n x y hx hy,
    (globalLof_mul a c η hc θ k l x y).symm⟩

lemma gradeB_one (d : I → ℕ) : (1 : B a (slope c η) d)∈gradeB a (slope c η) d 0 := by
  change (destabilizingSpace a (slope c η) d).mkQ (1 : S d)∈_
  rw [mem_gradeB_iff,componentB_mk,componentS_of_homogeneous _ _ (MvPolynomial.isWeightedHomogeneous_one ℚ (fun _=>(1:ℤ))),ite_eq_left rfl]

omit hχ in
lemma globalOriginalHomogeneous_one : (1 : UnitalShuffle a c η hc θ)∈globalOriginalHomogeneous a c η hc θ 0 0 := by
  refine ⟨unitalGradeOne a c η hc θ,?_,rfl⟩
  exact unitalOriginalHomogeneous_mk a c η hc θ 0 0 0 _ (gradeB_one a c η 0)

lemma localPrimitiveGlobal_original (k : NonzeroSlopeWeight c η hc θ) (ℓ : ℤ)
    (x : primitiveSpace a c η hc θ hχ.out k.val.1.val k.val.2)
    (hx : associatedComponent a c η hc θ k.val.1.val k.val.2 ℓ x.val=x.val) :
    localPrimitiveGlobal a c η hc θ k x∈globalOriginalHomogeneous a c η hc θ k.val ℓ := by
  refine ⟨localPrimitiveInclusion a c η hc θ k x,?_,rfl⟩
  apply (mem_unitalOriginalHomogeneous a c η hc θ _ _ _ _).mpr
  apply (unitalGradeNonzeroEquiv a c η hc θ k.val.1.val k.property k.val.2).injective
  rw [unitalAssociatedComponent_nonzero]
  change associatedComponent a c η hc θ k.val.1.val k.val.2 ℓ
    ((unitalGradeNonzeroEquiv a c η hc θ k.val.1.val k.property k.val.2)
    ((unitalGradeNonzeroEquiv a c η hc θ k.val.1.val k.property k.val.2).symm x.val))=_
  rw [LinearEquiv.apply_symm_apply]
  simpa only [localPrimitiveInclusion,LinearMap.comp_apply,Submodule.subtype_apply,
    LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] using hx

lemma globalStringFamily_original (i : GlobalStringIndex a c η hc θ) :
    globalStringFamily a c η hc θ i∈globalOriginalHomogeneous a c η hc θ i.1.val
      (globalStringPolynomialDegree a c η hc θ i) := by
  apply localPrimitiveGlobal_original a c η hc θ
  exact congrArg Subtype.val (homogeneousPrimitiveStringBasis_degree a c η hc θ hχ.out
    i.1.val.1.val i.1.val.2 i.1.property i.2)

variable {J : Type*}

lemma primitiveWord_original (w : J → SlopeWeight c η hc θ) (p : J → ℤ)
    (b : J → UnitalShuffle a c η hc θ)
    (hb : ∀ i,b i∈globalOriginalHomogeneous a c η hc θ (w i) (p i)) (l : List J) :
    primitiveWord a c η hc θ b l∈globalOriginalHomogeneous a c η hc θ
      (wordWeight c η hc θ w l) (wordPolynomialDegree a c η hc θ w p l) := by
  induction l with
  | nil => exact globalOriginalHomogeneous_one a c η hc θ
  | cons i l ih => exact globalOriginalHomogeneous_mul a c η hc θ (hb i) ih

lemma globalStringPBWBasis_original
    (l : PBWWord a c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val)) :
    globalStringPBWBasis a c η hc θ l∈globalOriginalHomogeneous a c η hc θ
      (wordWeight c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val) l.val)
      (wordPolynomialDegree a c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val)
        (globalStringPolynomialDegree a c η hc θ) l.val) := by
  rw [globalStringPBWBasis_apply]
  exact primitiveWord_original a c η hc θ _ _ _ (globalStringFamily_original a c η hc θ) l.val

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PrimitiveStringBounds
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)

noncomputable local instance instAddCommGroupSubtypeSourceAssociatedGradeMemSubmoduleRatPrimitiveSpace_2_r036b63_1 : AddCommGroup (primitiveSpace a c η hc θ hχ d W) := Submodule.addCommGroup _
noncomputable local instance instModuleRatSubtypeSourceAssociatedGradeMemSubmodulePrimitiveSpace_2_r036b63_1 : Module ℚ (primitiveSpace a c η hc θ hχ d W) := Submodule.module _
noncomputable local instance instAddCommGroupSubtypeSourceAssociatedGradeMemSubmoduleRatPrimitiveSpaceKerPrimitiveDerivative_1_r036b63_1 : AddCommGroup (LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) := Submodule.addCommGroup _
noncomputable local instance instModuleRatSubtypeSourceAssociatedGradeMemSubmodulePrimitiveSpaceKerPrimitiveDerivative_1_r036b63_1 : Module ℚ (LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) := Submodule.module _
lemma associatedGrade_eq_zero_below (hW : W < -interaction a d d)
    (x : SourceAssociatedGrade a c η hc θ d W) : x=0 := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change x.val∈sourceFiltration a c η hc θ d (W+1)
    exact sourceFiltration_antitone a c η hc θ d (show W+1≤-interaction a d d by omega)
      (by rw [sourceFiltration_lower]; trivial)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

lemma globalOriginal_nonzero_bounds (d : slopeDimensions c η hc θ) (hd : d.val≠0)
    (W k : ℤ) (x : UnitalShuffle a c η hc θ)
    (hx : x∈globalOriginalHomogeneous a c η hc θ (d,W) k) (hne : x≠0) :
    -interaction a d.val d.val≤W ∧ W≤2*k+eulerForm a d.val d.val := by
  obtain ⟨y,hy,rfl⟩:=hx
  have hyne : y≠0 := fun h=>hne (by rw [h,map_zero])
  let e := unitalGradeNonzeroEquiv a c η hc θ d.val hd W
  have he : e y≠0 := fun h=>hyne (e.injective (h.trans e.map_zero.symm))
  have H:=congrArg e (mem_unitalOriginalHomogeneous a c η hc θ d.val W k y |>.mp hy)
  rw [unitalAssociatedComponent_nonzero] at H
  constructor
  · by_contra h
    exact he (associatedGrade_eq_zero_below a c η hc θ d.val W (lt_of_not_ge h) (e y))
  · by_contra h
    rw [associatedComponent_upper a c η hc θ d.val hd (d.property.resolve_left hd) W k
      (lt_of_not_ge h),LinearMap.zero_apply] at H
    exact he H.symm

lemma slopeStringCoefficient_bounds_oai (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ)
    (k : ℤ) (i : SlopeStringCoefficient a c η hc θ d hs k) :
    -interaction a d d ≤ i.1 ∧ i.1 ≤ 2*k+eulerForm a d d := by
  exact globalOriginal_nonzero_bounds a c η hc θ ⟨d,Or.inr hs⟩ hd i.1 k
    (globalStringPBWBasis a c η hc θ i.2.val)
    ((congrArg (fun z : SlopeWeight c η hc θ × ℤ=>
      globalStringPBWBasis a c η hc θ i.2.val ∈ globalOriginalHomogeneous a c η hc θ z.1 z.2)
      i.2.property).mp (globalStringPBWBasis_original a c η hc θ i.2.val))
    ((globalStringPBWBasis a c η hc θ).ne_zero i.2.val)

end ElementaryPositivity.RawShuffle

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElementaryPositivity.RawShuffle.slopeStringCoefficient_bounds_oai.{u_1} := @OAI.ElementaryPositivity.RawShuffle.slopeStringCoefficient_bounds_oai.{u_1}
