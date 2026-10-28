-- Prove2me | solution 1 for OAI.KirchbergRordam.PrimeSquareUnitary.exists_unitary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T17:16:55.266918+00:00
-- url     : https://prove2.me/submissions/7999740b-2b80-45b7-9b84-b1f9fcde27de

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr014
import Theorems.Thm_OAI_KirchbergRordam_PrimeSquareUnitary_fibers
import Theorems.Thm_OAI_KirchbergRordam_PrimeTensorSections_irreducible_fiber_bound
import Theorems.Thm_OAI_KirchbergRordam_PrimeTensorSections_sectionRange_scalar

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
namespace KirchbergRordam.ContinuousSectionLocality
section
variable {X E : Type*} [TopologicalSpace X] [instCompactSpaceX : CompactSpace X] [instT2SpaceX : T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem mem_of_pointwise (S : Submodule ℝ C(X,E)) (hS : IsClosed (S : Set C(X,E)))
    (hw : ∀ (f : C(X,ℝ)) (g : C(X,E)), g∈S → weight f g∈S)
    (f : C(X,E)) (hf : ∀ x, ∃ g∈S, g x=f x) : f∈S := by
  classical
  change f ∈ (S : Set C(X,E))
  rw [← hS.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  choose g hg he using hf
  let U : X → Set X := fun x => {y | ‖g x y-f y‖<ε/2}
  have ho (x : X) : IsOpen (U x) :=
    isOpen_lt ((g x).continuous.sub f.continuous).norm continuous_const
  have hcover : Set.univ ⊆ ⋃ x, U x := by
    intro x _
    apply Set.mem_iUnion.mpr
    refine ⟨x,?_⟩
    change ‖g x x-f x‖<ε/2
    rw [he,sub_self,norm_zero]
    linarith
  obtain ⟨J,hJ⟩ := isCompact_univ.elim_finite_subcover U ho hcover
  have hc : Set.univ ⊆ ⋃ i : J, U i.val := by
    intro x hx
    obtain ⟨i,hiJ,hi⟩ := Set.mem_iUnion₂.mp (hJ hx)
    exact Set.mem_iUnion.mpr ⟨⟨i,hiJ⟩,hi⟩
  obtain ⟨ρ,hρ⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite
    isClosed_univ (fun i : J => U i.val) (fun i => ho i.val)
      (locallyFinite_of_finite _) hc
  let G : C(X,E) := ∑ i : J, weight (ρ i) (g i.val)
  have hGS : G∈S := S.sum_mem (fun i _ => hw (ρ i) (g i.val) (hg i.val))
  have hsum (x : X) : ∑ i : J, ρ i x=1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (x:=x) (Set.mem_univ x)
  have hn : ‖G-f‖≤ε/2 := by
    apply (ContinuousMap.norm_le _ (by linarith)).mpr
    intro x
    have heq : (G-f) x=∑ i : J, ρ i x • (g i.val x-f x) := by
      simp only [ContinuousMap.sub_apply,G,ContinuousMap.sum_apply,weight_apply,smul_sub,
        Finset.sum_sub_distrib,← Finset.sum_smul,hsum,one_smul]
    rw [heq]
    calc
      ‖∑ i : J, ρ i x • (g i.val x-f x)‖ ≤
          ∑ i : J, ‖ρ i x • (g i.val x-f x)‖ := norm_sum_le _ _
      _ ≤ ∑ i : J, ρ i x * (ε/2) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul_of_nonneg (ρ.nonneg i x)]
        by_cases hi : ρ i x=0
        · simp [hi]
        apply mul_le_mul_of_nonneg_left _ (ρ.nonneg i x)
        exact (hρ i (subset_closure (show x∈Function.support (ρ i) from hi))).le
      _ = ε/2 := by rw [← Finset.sum_mul,hsum,one_mul]
  refine ⟨G,hGS,?_⟩
  rw [dist_comm,dist_eq_norm]
  exact hn.trans_lt (by linarith)
end
open scoped CStarAlgebra ComplexOrder
variable {X E : Type*} [TopologicalSpace X] [instCompactSpaceX : CompactSpace X] [instT2SpaceX : T2Space X] [CStarAlgebra E]

theorem mem_of_pointwise_star (S : StarSubalgebra ℂ C(X,E)) (hS : IsClosed (S : Set C(X,E)))
    (hs : ∀ f : C(X,ℂ), scalarMap f∈S) (f : C(X,E))
    (hf : ∀ x, ∃ g∈S, g x=f x) : f∈S := by
  apply mem_of_pointwise (S.toSubalgebra.toSubmodule.restrictScalars ℝ) hS _ f hf
  intro c g hg
  let z : C(X,ℂ) := ⟨fun x => (c x : ℂ),Complex.continuous_ofReal.comp c.continuous⟩
  have hh : scalarMap z * g∈S := S.mul_mem (hs z) hg
  have he : weight c g=scalarMap z * g := by
    apply ContinuousMap.ext
    intro x
    change c x • g x=((c x:ℂ) • (1:E))*g x
    rw [smul_mul_assoc,one_mul,Complex.coe_smul]
  rw [he]
  exact hh

end KirchbergRordam.ContinuousSectionLocality
namespace KirchbergRordam.PrimeTensorSections
open scoped CStarAlgebra ComplexOrder TensorProduct
open PrimeDimensionDrop MatrixTensor ContinuousSectionLocality
variable {p q r k : ℕ}

lemma sectionMap_isometry : Isometry (sectionMap (p:=p) (q:=q) (r:=r) (k:=k)) :=
  NonUnitalStarAlgHom.isometry _ sectionMap_injective
lemma sectionRange_closed : IsClosed (sectionRange (p:=p) (q:=q) (r:=r) (k:=k) :
    Set C(Square,SquareFiber p q r k)) := sectionMap_isometry.isClosedEmbedding.isClosed_range

lemma sectionMap_raw (a : Algebra p q ⊗[ℂ] Algebra r k) (x : Square) :
    sectionMap (MaxTensor.of (MaxTensor.rawEquiv a)) x =
      subKronecker (evaluation p q x.1).range (evaluation r k x.2).range
        (TensorProduct.map (evaluation p q x.1).rangeRestrict.toLinearMap
          (evaluation r k x.2).rangeRestrict.toLinearMap a) := by
  induction a using OAI.tensorInductionOn with
  | add a b ha hb => simp only [map_add,ContinuousMap.add_apply,ha,hb]
  | tmul a b =>
    change sectionMap (MaxTensor.of (a ⊗ₜ[ℂ] b)) x = _
    rw [TensorProduct.map_tmul,sectionMap_tmul]; rfl

lemma fiberRange_lift (x : Square) (a : SquareFiber p q r k)
    (ha : a∈fiberRange (p:=p) (q:=q) (r:=r) (k:=k) x) :
    ∃ b : MaxTensor.Algebra (Algebra p q) (Algebra r k), sectionMap b x=a := by
  obtain ⟨c,hc⟩ := ha
  have hL : Function.Surjective (evaluation p q x.1).rangeRestrict := by
    rintro ⟨a,⟨b,hb⟩⟩
    exact ⟨b,Subtype.ext hb⟩
  have hR : Function.Surjective (evaluation r k x.2).rangeRestrict := by
    rintro ⟨a,⟨b,hb⟩⟩
    exact ⟨b,Subtype.ext hb⟩
  obtain ⟨d,hd⟩ := TensorProduct.map_surjective
    (g:=(evaluation p q x.1).rangeRestrict.toLinearMap)
    (g':=(evaluation r k x.2).rangeRestrict.toLinearMap) hL hR c
  exact ⟨MaxTensor.of (MaxTensor.rawEquiv d),by rw [sectionMap_raw,hd]; exact hc⟩


theorem mem_sectionRange_of_fibers (f : C(Square,SquareFiber p q r k))
    (hf : ∀ x, f x∈fiberRange (p:=p) (q:=q) (r:=r) (k:=k) x) :
    f∈sectionRange (p:=p) (q:=q) (r:=r) (k:=k) := by
  apply mem_of_pointwise_star _ sectionRange_closed sectionRange_scalar f
  intro x
  obtain ⟨b,hb⟩ := fiberRange_lift x (f x) (hf x)
  exact ⟨sectionMap b,⟨b,rfl⟩,hb⟩
end KirchbergRordam.PrimeTensorSections
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

lemma section_mem : unitarySection u hu h0∈sectionRange (p:=p) (q:=q) (r:=p) (k:=q) :=
  mem_sectionRange_of_fibers _ (fibers u hu h0)

lemma section_unitary : unitarySection u hu h0∈unitary C(Square,SquareFiber p q p q) := by
  constructor
  · apply ContinuousMap.ext; intro x
    exact ((diagram u hu h0).W x).property.1
  · apply ContinuousMap.ext; intro x
    exact ((diagram u hu h0).W x).property.2

lemma section_exists_raw : ∃ w : MaxTensor.Algebra (Algebra p q) (Algebra p q),
    sectionMap w=unitarySection u hu h0 := section_mem (p:=p) (q:=q) u hu h0

lemma section_image_unitary (w : MaxTensor.Algebra (Algebra p q) (Algebra p q))
    (hw : sectionMap w=unitarySection u hu h0) :
    sectionMap (p:=p) (q:=q) (r:=p) (k:=q) w∈unitary C(Square,SquareFiber p q p q) := by
  rw [hw]
  exact section_unitary u hu h0

lemma section_reflect (w : MaxTensor.Algebra (Algebra p q) (Algebra p q))
    (hw : sectionMap w=unitarySection u hu h0) :
    w∈unitary (MaxTensor.Algebra (Algebra p q) (Algebra p q)) := by
  have h := section_image_unitary u hu h0 w hw
  constructor
  · apply sectionMap_injective (p:=p) (q:=q) (r:=p) (k:=q)
    calc
      sectionMap (star w*w) = star (sectionMap w)*sectionMap w := by rw [map_mul,map_star]
      _ = 1 := h.1
      _ = sectionMap 1 := (sectionMap (p:=p) (q:=q) (r:=p) (k:=q)).map_one'.symm
  · apply sectionMap_injective (p:=p) (q:=q) (r:=p) (k:=q)
    calc
      sectionMap (w*star w) = sectionMap w*star (sectionMap w) := by rw [map_mul,map_star]
      _ = 1 := h.2
      _ = sectionMap 1 := (sectionMap (p:=p) (q:=q) (r:=p) (k:=q)).map_one'.symm


theorem exists_unitary_oai : ∃ w : unitary (MaxTensor.Algebra (Algebra p q) (Algebra p q)),
    sectionMap (w : MaxTensor.Algebra (Algebra p q) (Algebra p q))=unitarySection u hu h0 := by
  obtain ⟨w,hw⟩ := section_exists_raw (p:=p) (q:=q) u hu h0
  exact ⟨⟨w,section_reflect u hu h0 w hw⟩,hw⟩
end KirchbergRordam.PrimeSquareUnitary


end

end OAI
end

theorem solution : type_of% @OAI.KirchbergRordam.PrimeSquareUnitary.exists_unitary_oai := @OAI.KirchbergRordam.PrimeSquareUnitary.exists_unitary_oai
