-- Prove2me | solution 1 for OAI.CubicEisenstein.whittakerIntegrand_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:12:15.909045+00:00
-- url     : https://prove2.me/submissions/ce00785b-65c0-416a-85f5-711f63210020

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CutoffApproximation
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConjugateLevelAction
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ScatteringCoefficients
import Theorems.Thm_OAI_CubicEisenstein_whittakerHeight_ge_one
import Theorems.Thm_OAI_CubicEisenstein_whittakerBase_ge
import Theorems.Thm_OAI_CubicEisenstein_whittakerBase_ge_one
import Theorems.Thm_OAI_CubicEisenstein_whittakerBase_pos
import Theorems.Thm_OAI_CubicEisenstein_whittakerIntegrand_norm

set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
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
open Filter MeasureTheory
open scoped BigOperators Classical Topology
namespace OAI.CubicEisenstein
theorem _root_.solution (freq s : ℂ) (p : ℝ × ℂ)
    (b : ℝ) (hb : 0≤b) (hs : b≤s.re) :
    ‖whittakerIntegrand freq s p‖≤(1+‖p.2‖^2)^(-b) := by
  rw [whittakerIntegrand_norm]
  calc
    _ ≤ (whittakerBase p)^(-s.re) := by
      exact mul_le_of_le_one_left (Real.rpow_nonneg (whittakerBase_pos p).le _)
        (inv_le_one_of_one_le₀ (whittakerHeight_ge_one p.1))
    _ ≤ (whittakerBase p)^(-b) :=
      Real.rpow_le_rpow_of_exponent_le (whittakerBase_ge_one p) (by linarith)
    _ ≤ (1+‖p.2‖^2)^(-b) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (whittakerBase_ge p) (by linarith)
end OAI.CubicEisenstein
