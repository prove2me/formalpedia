-- Prove2me | solution 1 for MazurTransfer.original_actual_integral_arithmetic_kernel_hopf_models
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T06:41:39.773879+00:00
-- url     : https://prove2.me/submissions/db9e9944-fef1-4526-ab8c-e4fe8af4d09f

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: finite-free cocommutative integral Hopf models carry the same integral point functor with full algebra naturality, and labels into the previously fixed arithmetic norm kernel preserving addition and the existing Galois action for every field automorphism.
Named downstream consumer: actual finite-flat selected arithmetic character quotients and Kummer local conditions at nineteen.
-/
import Definitions.Def_MazurTransfer_OriginalActualIntegralArithmeticKernelHopfModelsData20261020
import Theorems.Thm_MazurTransfer_original_integral_hopf_arithmetic_kernel_labels_laws
import Theorems.Thm_MazurTransfer_original_integral_norm_kernel_hopf_models
noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTransfer.Order13IntegralHopfArithmeticKernelLabels MazurTransfer.Order13ActualArithmeticKernelAdditiveAction
open MazurTransfer.Order13IntegralArithmeticNormKernelComparison
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13GoodPrimeLocalPicardModels
open MazurTransfer.Order13GoodPrimeIntegralNormExtensions MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
open MazurTransfer.Order13ActualPicardSchemeNineteenNorm MazurTransfer.Order13ActualPicardSchemeNormGroupHom
open MazurTransfer.Order13ActualPicardGeometricNormPreimages MazurTransfer.Order13ActualPicardNormKummerCocycles
open MazurTransfer.Order13ActualPicardNormKernelGaloisAction MazurTransfer.Order13ExceptionalNineteenFlatNormFibres
open scoped CategoryTheory.MonObj
open MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels
attribute [local instance] MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualIntegralArithmeticKernelHopfModels
attribute [local instance] MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13ActualIntegralArithmeticKernelHopfModels
attribute [local instance] MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualIntegralArithmeticKernelHopfModels
attribute [local instance] MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualIntegralArithmeticKernelHopfModels
attribute [local instance] MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualIntegralArithmeticKernelHopfModels
attribute [local instance] MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.instFactPrimeOfNatNat_order13ActualIntegralArithmeticKernelHopfModels
namespace MazurTransfer.OriginalActualIntegralArithmeticKernelHopfModelsBoundary20261020
end MazurTransfer.OriginalActualIntegralArithmeticKernelHopfModelsBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: finite-free cocommutative integral Hopf models labelled
by the SAME FIXED arithmetic norm kernel, retaining the SAME integral point functor
and its all-algebra naturality, addition and the
PREVIOUSLY DEFINED arithmetic Galois action for every field automorphism.
Named downstream consumer: actual finite-flat selected character quotients
at nineteen and their Kummer local conditions. No splitting is assumed.
-/

noncomputable section
namespace MazurTransfer.OriginalActualIntegralArithmeticKernelHopfModelsProof20261020
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open Order13IntegralHopfArithmeticKernelLabels Order13ActualArithmeticKernelAdditiveAction
open Order13IntegralArithmeticNormKernelComparison
open Order13LocalIntegralCoefficientMaps Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeIntegralNormExtensions RelativeGroupLawFiniteFlatKernelHopf
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13ActualPicardNormKernelGaloisAction Order13ExceptionalNineteenFlatNormFibres
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
variable (K : Type) [Field K] [CharZero K]
variable [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K]

variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]





theorem has_arithmetic_integral_kernel_hopf_model
    (hmodel : HasFiniteFreeKernelHopfModel (localLaw q hq) (integralNorm q hq φ)) :
    HasArithmeticIntegralKernelHopfModel q hq K φ := by
  obtain ⟨H, iCR, iHA, hFin, hFree, hComm, e, hMul, hNat⟩ := hmodel
  letI := iCR
  letI := iHA
  letI := hFin
  letI := hFree
  letI := hComm
  refine ⟨H, iCR, iHA, hFin, hFree, hComm, e, hMul, hNat, arithmeticKernelLabel q hq K φ (e K), ?_, ?_, ?_⟩
  · exact (MazurTransfer.original_integral_hopf_arithmetic_kernel_labels_laws).2.2.1 q hq K φ (e K) (hMul K)
  · intro σ f g hfg
    apply (MazurTransfer.original_integral_hopf_arithmetic_kernel_labels_laws).2.2.2 q hq K φ (e K) σ f g
    have heq : g = WithConv.toConv
        (((σ : K →ₐ[ℚ] K).restrictScalars (LocalRing q)).comp f.ofConv) := by
      apply WithConv.ofConv_injective
      ext x
      exact hfg x
    calc
      (e K g).val.val = (e K (WithConv.toConv
          (((σ : K →ₐ[ℚ] K).restrictScalars (LocalRing q)).comp f.ofConv))).val.val :=
        congrArg (fun a => (e K a).val.val) heq
      _ = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (e K f).val.val :=
        hNat K K ((σ : K →ₐ[ℚ] K).restrictScalars (LocalRing q)) f

  · intro f
    exact (kernelPointEquiv q hq K φ).apply_symm_apply (e K f)




include hq in
theorem actual_integral_arithmetic_norm_kernel_hopf_models :
    HasArithmeticIntegralKernelHopfModel q hq K schemePi ∧
      HasArithmeticIntegralKernelHopfModel q hq K schemePiConjugate := by
  have h := (MazurTransfer.original_integral_norm_kernel_hopf_models).1 q hq
  exact ⟨has_arithmetic_integral_kernel_hopf_model q hq K schemePi h.1,
    has_arithmetic_integral_kernel_hopf_model q hq K schemePiConjugate h.2⟩


theorem actual_nineteen_arithmetic_norm_kernel_hopf_models
    (F : Type) [Field F] [CharZero F] [Algebra (LocalRing 19) F]
    [IsScalarTower (LocalRing 19) ℚ F] :
    HasArithmeticIntegralKernelHopfModel 19 nineteen_good F schemePi ∧
      HasArithmeticIntegralKernelHopfModel 19 nineteen_good F schemePiConjugate :=
  actual_integral_arithmetic_norm_kernel_hopf_models 19 nineteen_good F

end MazurTransfer.OriginalActualIntegralArithmeticKernelHopfModelsProof20261020

theorem solution : (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], ∀ (hmodel : HasFiniteFreeKernelHopfModel (localLaw q hq) (integralNorm q hq φ)),
HasArithmeticIntegralKernelHopfModel q hq K φ) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K], HasArithmeticIntegralKernelHopfModel q hq K schemePi ∧
      HasArithmeticIntegralKernelHopfModel q hq K schemePiConjugate) ∧ (∀ (F : Type) [Field F] [CharZero F] [Algebra (LocalRing 19) F]
    [IsScalarTower (LocalRing 19) ℚ F],
HasArithmeticIntegralKernelHopfModel 19 nineteen_good F schemePi ∧
      HasArithmeticIntegralKernelHopfModel 19 nineteen_good F schemePiConjugate) := by
  exact ⟨MazurTransfer.OriginalActualIntegralArithmeticKernelHopfModelsProof20261020.has_arithmetic_integral_kernel_hopf_model, MazurTransfer.OriginalActualIntegralArithmeticKernelHopfModelsProof20261020.actual_integral_arithmetic_norm_kernel_hopf_models, MazurTransfer.OriginalActualIntegralArithmeticKernelHopfModelsProof20261020.actual_nineteen_arithmetic_norm_kernel_hopf_models⟩
#print axioms solution
