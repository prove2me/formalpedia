-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormCharacterH1Exactness.hasExactCharacterH1Sequence_of_intertwiners
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T02:28:08.482187+00:00
-- url     : https://prove2.me/submissions/ddca86aa-fd8e-48bf-bede-e54fbd3c101d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an actual norm-character representation sequence is exact
at the EXISTING continuous H1 globally and after restriction to every subgroup.
Named downstream consumer: kernel control for actual norm Selmer images.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterH1ExactSequenceData
import Theorems.Thm_MazurTransfer_ContinuousFirstCohomologyExactSequence_range_eq_ker
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormContinuousCocycles_kernel_continuousSMul

noncomputable section
namespace MazurTransfer.RepresentationCoefficientExactSequenceProofHelper20261018
open RepresentationDiscreteCoefficients RepresentationDiscreteCoefficientInclusion
variable {k G V W M : Type} [Semiring k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [CommGroup M] [MulDistribMulAction G M] [Module k (Additive M)]
variable [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M]
  [DiscreteTopology M] [ContinuousSMul G M]
variable (σ : Representation k G V) (ρ : Representation k G (Additive M))
  (τ : Representation k G W)
variable (i : Representation.IntertwiningMap σ ρ) (p : Representation.IntertwiningMap ρ τ)
variable (hρ : ∀ (g : G) (m : M), ρ g (Additive.ofMul m) = Additive.ofMul (g • m))

theorem range_inclusionH1_eq_ker_mapH1
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) :
    (inclusionH1 σ ρ i hρ).range = (mapH1 ρ τ p hρ).ker :=
  ContinuousFirstCohomologyExactSequence.range_eq_ker
    G (Coefficient σ) M (Coefficient τ) (toIntertwining σ ρ i) (fromIntertwining ρ τ p)
    (toIntertwining_equivariant σ ρ i hρ) (fromIntertwining_equivariant ρ τ p hρ)
    (toIntertwining_injective σ ρ i hi) (fromIntertwining_surjective ρ τ p hp)
    (coefficient_exact σ ρ τ i p hk)

end MazurTransfer.RepresentationCoefficientExactSequenceProofHelper20261018

noncomputable section
namespace MazurTransfer.ActualNormCharacterExactH1ProofHelpers20261018
open MazurTransfer.Order13ActualNormCharacterH1Exactness
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualExactH1ProofHelperProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualExactH1ProofHelperProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualExactH1ProofHelperProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance actualExactH1ProofHelperProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance actualExactH1ProofHelperProvider520261018 : TopologicalSpace (Points K) := pointsTopology K
local instance actualExactH1ProofHelperProvider620261018 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualExactH1ProofHelperProvider720261018 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualExactH1ProofHelperProvider820261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance actualExactH1ProofHelperProvider920261018 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance actualExactH1ProofHelperProvider1020261018 : Module (ZMod 19) (ContinuousH1 K φ) := globalH1ZModModule K φ
local instance actualExactH1ProofHelperProvider1120261018 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ
open RepresentationDiscreteCoefficientInclusion
open MazurTransfer.RepresentationCoefficientExactSequenceProofHelper20261018
open Order13ActualNormCharacterContinuousH1
variable {U V : Type} [AddCommGroup U] [Module (ZMod 19) U]
  [AddCommGroup V] [Module (ZMod 19) V]
variable (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U)
  (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (i : Representation.IntertwiningMap σ (kernelRepresentation K φ))
  (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
local instance actualExactH1ProofHelperProvider1220261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ)) :=
  coefficientH1ZModModule σ
local instance actualExactH1ProofHelperProvider1320261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient τ)) :=
  coefficientH1ZModModule τ

theorem range_inclusionClass_eq_ker_mapClass
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) :
    LinearMap.range (inclusionClass K φ σ i) = LinearMap.ker (mapClass K φ τ p) := by
  ext x
  exact SetLike.ext_iff.mp (range_inclusionH1_eq_ker_mapH1 σ (kernelRepresentation K φ) τ i p
    (by intro g m; rfl) hi hp hk) x

theorem characterCoefficient_continuousSMul (hi : Function.Injective i) :
    ContinuousSMul (K ≃ₐ[ℚ] K) (Coefficient σ) := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro x
  have heq : (MulAction.stabilizer (K ≃ₐ[ℚ] K) x : Set (K ≃ₐ[ℚ] K)) =
      (MulAction.stabilizer (K ≃ₐ[ℚ] K) (toIntertwining σ (kernelRepresentation K φ) i x) :
        Set (K ≃ₐ[ℚ] K)) := by
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    rw [← toIntertwining_equivariant σ (kernelRepresentation K φ) i (by intro g m; rfl)]
    exact (toIntertwining_injective σ (kernelRepresentation K φ) i hi).eq_iff.symm
  rw [heq]
  let y : Kernel K φ := toIntertwining σ (kernelRepresentation K φ) i x
  have hc : Continuous (fun g : K ≃ₐ[ℚ] K => g • y) := continuous_id.smul continuous_const
  change IsOpen {g : K ≃ₐ[ℚ] K | g • y = y}
  exact (isOpen_discrete ({y} : Set (Kernel K φ))).preimage hc

variable (S : Subgroup (K ≃ₐ[ℚ] K))
local instance actualExactH1ProofHelperProvider1420261018 : Module (ZMod 19) (localContinuousH1 K φ S) := restrictedH1ZModModule K φ S
local instance actualExactH1ProofHelperProvider1520261018 : Module (ZMod 19) (ContinuousFirstCohomologyPresentation.H1 S (Coefficient σ)) :=
  restrictedCoefficientH1ZModModule σ S
local instance actualExactH1ProofHelperProvider1620261018 : Module (ZMod 19) (ContinuousFirstCohomologyPresentation.H1 S (Coefficient τ)) :=
  restrictedCoefficientH1ZModModule τ S
local instance actualExactH1ProofHelperProvider1720261018 : ContinuousSMul S (Kernel K φ) := subgroup_kernelContinuousSMul K φ S

theorem range_localInclusionClass_eq_ker_localMapClass
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) :
    LinearMap.range (localInclusionClass K φ σ i S) = LinearMap.ker (localMapClass K φ τ p S) := by
  ext x
  exact SetLike.ext_iff.mp (ContinuousFirstCohomologyExactSequence.range_eq_ker
    S (Coefficient σ) (Kernel K φ) (Coefficient τ)
    (toIntertwining σ (kernelRepresentation K φ) i)
    (fromIntertwining (kernelRepresentation K φ) τ p)
    (fun s y => toIntertwining_equivariant σ (kernelRepresentation K φ) i
      (by intro g m; rfl) s.val y)
    (fun s y => fromIntertwining_equivariant (kernelRepresentation K φ) τ p
      (by intro g m; rfl) s.val y)
    (toIntertwining_injective σ (kernelRepresentation K φ) i hi)
    (fromIntertwining_surjective (kernelRepresentation K φ) τ p hp)
    (coefficient_exact σ (kernelRepresentation K φ) τ i p hk)) x

end MazurTransfer.ActualNormCharacterExactH1ProofHelpers20261018

noncomputable section

open MazurTransfer
open MazurTransfer.Order13ActualPicardNormContinuousCocycles
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormCharacterExactH1SequenceSourceProvider20261018920261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormCharacterExactH1SequenceSourceProvider202610181020261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormCharacterExactH1SequenceSourceProvider202610181120261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormCharacterExactH1SequenceSourceProvider202610181220261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
local instance actualNormCharacterExactH1SequenceSourceProvider202610181320261017 (K : Type) [Field K] [CharZero K] : TopologicalSpace (Points K) := pointsTopology K
local instance actualNormCharacterExactH1SequenceSourceProvider202610181420261017 (K : Type) [Field K] [CharZero K] : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualNormCharacterExactH1SequenceSourceProvider202610181520261017 (K : Type) [Field K] [CharZero K] : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualNormCharacterExactH1SequenceSourceProvider202610181620261017 (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

open MazurTransfer.Order13ActualPicardNormAlgebraicCohomology

open MazurTransfer.Order13ActualNormKernelF19Representation
local instance actualCharacterExactSequenceFiniteSourceProvider20261018 (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] :
    Finite (Kernel K φ) := MazurTransfer.Order13ActualNormKernelFiniteModule.kernel_finite K φ
local instance actualCharacterExactSequenceModuleSourceProvider20261018 (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] : Module (ZMod 19) (Additive (Kernel K φ)) :=
  MazurTransfer.Order13ActualNormKernelFiniteModule.kernelZModModule K φ
local instance actualCharacterExactSequenceContinuousSourceProvider20261018 (K : Type) [Field K] [CharZero K]
    [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    [IsMonHom φ] [IsFinite φ.left] : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) :=
  MazurTransfer.Order13ActualPicardNormContinuousCocycles.kernel_continuousSMul K φ

open MazurTransfer.Order13ActualNormCharacterH1Exactness
open MazurTransfer.Order13ActualNormCharacterContinuousH1

theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
    {U V : Type} [AddCommGroup U] [Module (ZMod 19) U] [AddCommGroup V] [Module (ZMod 19) V]
    (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U)
    (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
    (i : Representation.IntertwiningMap σ (kernelRepresentation K φ))
    (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) :
    HasExactCharacterH1Sequence K φ σ τ :=
  ⟨i, p, hi, hp, hk, MazurTransfer.ActualNormCharacterExactH1ProofHelpers20261018.characterCoefficient_continuousSMul K φ σ i hi,
    coefficient_continuousSMul K φ τ p hp,
    MazurTransfer.ActualNormCharacterExactH1ProofHelpers20261018.range_inclusionClass_eq_ker_mapClass K φ σ τ i p hi hp hk,
    fun S => MazurTransfer.ActualNormCharacterExactH1ProofHelpers20261018.range_localInclusionClass_eq_ker_localMapClass K φ σ τ i p S hi hp hk⟩


#print axioms solution
