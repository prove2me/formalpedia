-- Prove2me | solution 1 for OAI.JointLogSeparation.twisted_profile_fourier_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:45:48.056686+00:00
-- url     : https://prove2.me/submissions/9e65e20a-e9af-4ac6-bb5c-b57bea2aa73a

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_SecondPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_PrincipalTruncation
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_FrequencyTwists
import Theorems.Thm_OAI_JointLogSeparation_profileSourceBound_frequencyTwist
import Theorems.Thm_OAI_JointLogSeparation_fourierPointBound_mono
import Theorems.Thm_OAI_JointLogSeparation_fourierPointBound_mul
import Theorems.Thm_OAI_FirstPassCubeLabels_firstLogDensity_nonneg
import Theorems.Thm_OAI_JointLogSeparation_profile_fourier_envelope


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
open OAI.JointLogSeparation
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open FourierBridge
namespace OAI.JointLogSeparation
theorem _root_.solution (g : 𝓢(ℝ, ℂ)) (t s : ℝ) (J : ℕ) :
    ‖(𝓕 (frequencyTwist g t)) s‖ ≤
      fourierPointBound (J + 2) (twistSourceBound g (J + 2)) *
        (1 + ‖t‖)^(J + 2) * FirstPassCubeLabels.firstLogDensity J s := by
  calc
    _ ≤ fourierPointBound (J + 2) (profileSourceBound (frequencyTwist g t) (J + 2)) *
        FirstPassCubeLabels.firstLogDensity J s := profile_fourier_envelope _ _ _
    _ ≤ fourierPointBound (J + 2) (twistSourceBound g (J + 2) * (1 + ‖t‖)^(J + 2)) *
        FirstPassCubeLabels.firstLogDensity J s :=
      mul_le_mul_of_nonneg_right (fourierPointBound_mono _ (profileSourceBound_frequencyTwist _ _ _))
        (FirstPassCubeLabels.firstLogDensity_nonneg _ _)
    _ = _ := by rw [fourierPointBound_mul]
end OAI.JointLogSeparation
