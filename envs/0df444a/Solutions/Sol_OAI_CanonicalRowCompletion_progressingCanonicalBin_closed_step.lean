-- Prove2me | solution 1 for OAI.CanonicalRowCompletion.progressingCanonicalBin_closed_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:38:03.123489+00:00
-- url     : https://prove2.me/submissions/635ab83a-566f-4fb5-8548-daec8e4574d9

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_UnitNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_CubicReopening
import Theorems.Thm_OAI_CanonicalRowCompletion_outside_pool_coprime_excluded
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIdeal_primeProduct_norm
import Theorems.Thm_OAI_CanonicalRowCompletion_progressingActiveBin_cube_bound
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalCoefficientClass_IsBaseRayTwist_norm_le
import Theorems.Thm_OAI_CanonicalCubeSeparation_cubeFrequencyFactor_norm
import Theorems.Thm_OAI_CanonicalCubeSeparation_sourceLogProfile_apply
import Theorems.Thm_OAI_CanonicalQuadraticSieve_poolPrimary_coprime
import Theorems.Thm_OAI_CanonicalQuadraticSieve_poolPrimary_odd
import Theorems.Thm_OAI_CanonicalRowCompletion_activeCubeLogBin_norms
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIndex_apply
import Theorems.Thm_OAI_CanonicalRowCompletion_outside_separated_cube_coefficient_bound
import Theorems.Thm_OAI_CanonicalRowCompletion_progressingActiveBin_progress
import Theorems.Thm_OAI_CompletedHeight_completedT_normHeight_norm
import Theorems.Thm_OAI_CompletedHeight_shortCompletedSum_normHeight_norm
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelTruncatedWeight_apply
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_InitialMeanSquare_initialLogProfile_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_append_first
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_first_append
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_source_append
import Theorems.Thm_OAI_SecondPassArithmetic_normHeightTwist_norm_le
import Theorems.Thm_OAI_SecondPassArithmetic_normLogScale_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_normLogScale_pos
import Theorems.Thm_OAI_SecondPassArithmetic_reopenedCanonicalRow_closed_step
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothBCF_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CanonicalCubeSeparation.cubeFrequencyFactor_norm
attribute [local simp] OAI.CanonicalCubeSeparation.sourceLogProfile_apply
attribute [local simp] OAI.CanonicalRowCompletion.cubeIndex_apply
attribute [local simp] OAI.CompletedHeight.completedT_normHeight_norm
attribute [local simp] OAI.CompletedHeight.shortCompletedSum_normHeight_norm
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_apply
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_source
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.kernelLocalLift_symm
attribute [local simp] OAI.CubicEisenstein.kernelQuotientChart_symm
attribute [local simp] OAI.CubicEisenstein.kernelTruncatedWeight_apply
attribute [local simp] OAI.CubicEisenstein.spatialTriple_one
attribute [local simp] OAI.CubicEisenstein.spatialTriple_two
attribute [local simp] OAI.CubicEisenstein.spatialTriple_zero
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.FirstPassCubeLabels.coreRayTwist_prod
attribute [local simp] OAI.FirstPassCubeLabels.twisted_core_product
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.InitialMeanSquare.initialLogProfile_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_apply
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_zero
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.append_first
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.first_append
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.source_append
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newLabel
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newRow
attribute [local simp] OAI.SecondPassIntegration.conjugateProfile_apply
attribute [local simp] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothBCF_apply



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open OAI.CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation JointLogSeparation
open FirstPassCubeLabels (columnLog)
namespace OAI.CanonicalRowCompletion
theorem _root_.solution
    (g V : 𝓢(ℝ,ℂ)) (A M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss η : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (hη : 0<η)
    (hηsmall : η≤(1:ℝ)/1000) (hbudget : 3000*η≤(1:ℝ)/40) (J : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (C : ℝ), 0≤C ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+7) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+7) ∧
      ∀(S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
      (base : ActualEisensteinCubic.O→*ℂ) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
      (X F K E oldHeight : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      (∀u,‖base u‖≤1) → 1<Z → Real.exp 9000≤Z → 1≤X → X≤Z^3 → F≤Z^3 → 1≤E →
      let P:=InitialMeanSquare.outsideSquarefreeIdeals S D
      let hP:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
      letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
        fun i=>by rw [poolPrimary_span P hP i];infer_instance
      (∀side : Bool, let windows:=if side then windows₁ else windows₂
        ∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base (∏Q∈S,Q) Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z K → ∀s : ℝ,
        (canonicalLogEnergy (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
          (poolPrimary_good P hP) Finset.univ (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
          (poolPrimary_good P hP) Finset.univ (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      ∀j∈cubeLogRange (Real.exp A) X,
      let B:=normLogScale j
      let H₀:=if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0
      let Q':=progressingCubes S D H₀ (activeCubeLogBin S D (Real.exp A) X j)
      Q'.Nonempty → ∀ξ : ℝ,
      B*rowFamilyEnergy labels (fun I z=>
        reopenedCanonicalRow (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
          (poolPrimary_good P hP) Finset.univ Q'
          (separatedCubeCoefficient
            (fun v=>reopenedCubeCoefficient H₀
              (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) 1)
              (cubeIdeal P v))
            (fun v=>(Ideal.absNorm (cubeIdeal P v):ℝ)) B ξ)
          Ψ m (idealGenerator I)
          (fun T=>frequencyTwist g (oldHeight+ξ) (columnLog (poolPrimary P) (X/B^3) T)) z) K≤
        C*(X*F)^2*Z^(η+17*deltaLoss+38*ε)*E*(1+|oldHeight+ξ|)^(2*J) := by
  obtain ⟨w₁,w₂,C₀,hC₀,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,hstep⟩ :=
    reopenedCanonicalRow_closed_step g V A M Nv hM hNv hgM hV hWin
      ε deltaLoss η hε hδ hη hηsmall hbudget J
  obtain ⟨Cβ,hCβ,hβbound⟩:=outside_separated_cube_coefficient_bound ε hε
  let Cg:=Cβ*(Real.exp (A+1))^ε
  refine ⟨w₁,w₂,C₀*Cg^2,by positivity,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro S D hbad hSp base Z Ψ m labels X F K E oldHeight hstate hbase hZ hZbig hX hXZ hFZ hE
  dsimp only
  let P:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hP:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span P hP i];infer_instance
  intro ih j hj hQ ξ
  let B:=normLogScale j
  let H₀:=if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0
  let Q':=progressingCubes S D H₀ (activeCubeLogBin S D (Real.exp A) X j)
  let β:=fun I v=>separatedCubeCoefficient
    (fun u=>reopenedCubeCoefficient H₀
      (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal P u))
    (fun u=>(Ideal.absNorm (cubeIdeal P u):ℝ)) B ξ v
  have hB : 1≤B:=normLogScale_ge_one j
  have hBp : 0<B:=normLogScale_pos j
  have hactive : B^3≤Real.exp A*X:=progressingActiveBin_cube_bound S D (Real.exp A) X H₀ j hQ
  have hBscale : Real.exp 1*B≤Real.exp (A+1)*Z^3 := by
    calc
      _ ≤ Real.exp 1*(Real.exp A*X) :=
        mul_le_mul_of_nonneg_left ((le_self_pow₀ hB (by decide : (3:ℕ)≠0)).trans hactive) (Real.exp_pos _).le
      _ ≤ Real.exp 1*(Real.exp A*Z^3) := by gcongr
      _ = _ := by rw [Real.exp_add];ring
  have hbgrowth : (Real.exp 1*B)^ε≤(Real.exp (A+1))^ε*Z^(3*ε) := by
    calc
      _ ≤ (Real.exp (A+1)*Z^3)^ε :=
        Real.rpow_le_rpow (by positivity) hBscale hε.le
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast_mul (by linarith : 0≤Z)]
        norm_num
  have hΨ : ∀u,‖normHeightTwist Ψ oldHeight u‖≤1 :=
    fun u=>(normHeightTwist_norm_le Ψ oldHeight u).trans (hstate.coefficient.norm_le hbase u)
  have hcoeff : ∀I∈labels,∀v∈Q',‖β I v‖≤Cg*Z^(3*ε) := by
    intro I hI v hv
    have hvbin: v∈activeCubeLogBin S D (Real.exp A) X j:=(Finset.mem_filter.mp hv).1
    obtain ⟨hlo,hhi⟩:=activeCubeLogBin_norms S D (Real.exp A) X j v hvbin
    exact (hβbound S D _ hΨ m (idealGenerator I) H₀ B ξ v hBp hlo hhi).trans
      ((mul_le_mul_of_nonneg_left hbgrowth hCβ.le).trans_eq (by dsimp only [Cg];ring))
  have hinj : Function.Injective (fun i:primePool P=>Ideal.span {poolPrimary P i}) := by
    intro i k he
    exact Subtype.ext (by simpa only [poolPrimary_span P hP] using he)
  have hpr (i : primePool P) : lambda^2∣poolPrimary P i-1 :=
    (primaryPrime_spec i.val (poolPrimary_ne_zero P hP i)).2.2.2
  have hn : ∀v∈Q',‖ConcreteTraceCRT.eisEmbedding
      (FirstPassCubeLabels.primeProduct (poolPrimary P) v.support v)‖^2≤Real.exp 1*B := by
    intro v hv
    rw [cubeIdeal_primeProduct_norm P hP]
    exact (activeCubeLogBin_norms S D (Real.exp A) X j v (Finset.mem_filter.mp hv).1).2
  have hp := hstep (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
    (poolPrimary_good P hP) (poolPrimary_odd P hP) hinj hpr base (∏Q∈S,Q) Z Ψ m labels
    X F K hstate Finset.univ Q' β (Cg*Z^(3*ε)) (oldHeight+ξ) B E hbase
    (outside_pool_coprime_excluded S D hbad hSp) hZ hZbig hX hXZ hFZ
    (by dsimp only [Cg];positivity) hE hB hactive
    (progressingActiveBin_progress S D (Real.exp A) X Z F j hstate.label_ge_one hQ)
    hcoeff (fun v hv=>Finset.subset_univ _) hn ih
  have hpower : (Z^(3*ε))^2*Z^(η+17*deltaLoss+32*ε)=Z^(η+17*deltaLoss+38*ε) := by
    rw [←Real.rpow_mul_natCast (by linarith : 0≤Z),←Real.rpow_add (by linarith : 0<Z)]
    congr 1
    norm_num
    ring
  have heq : C₀*(Cg*Z^(3*ε))^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε)*E*(1+‖oldHeight+ξ‖)^(2*J)=
      (C₀*Cg^2)*(X*F)^2*Z^(η+17*deltaLoss+38*ε)*E*(1+|oldHeight+ξ|)^(2*J) := by
    rw [Real.norm_eq_abs]
    calc
      _ = (C₀*Cg^2)*(X*F)^2*((Z^(3*ε))^2*Z^(η+17*deltaLoss+32*ε))*E*(1+|oldHeight+ξ|)^(2*J) := by ring
      _ = _ := by rw [hpower]
  exact (show _≤_ from hp).trans_eq heq
end OAI.CanonicalRowCompletion
