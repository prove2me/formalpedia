-- Prove2me | solution 1 for OAI.SecondPassArithmetic.canonicalBudgetScalar_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:35:22.233737+00:00
-- url     : https://prove2.me/submissions/fb114ed3-29c9-445f-8b35-423d7f40f0ff

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BarrierPotential
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ReopeningBounds
import Theorems.Thm_OAI_FirstPassCubeLabels_firstLogDensity_nonneg
import Theorems.Thm_OAI_SecondPassArithmetic_globalTerminalConstant_nonneg


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
open OAI.SecondPassArithmetic
open MeasureTheory
open FirstPassCubeLabels (firstLogDensity)
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (C Cd Ct Tmax Clo Chi A M Γ P E t B U deltaLoss ε tailFactor terminalFactor : ℝ) (J : ℕ)
    (hC : 0≤C) (hCd : 0≤Cd) (hCt : 0≤Ct) (hTmax : 0≤Tmax)
    (_hClo : 0≤Clo) (hChi : 0≤Chi) (hΓ : 0≤Γ) (hP : 0≤P)
    (hE : 1≤E) (hB : 0≤B) (hBU : B≤U) (hU : 1≤U) (hδ : 0≤deltaLoss) (hε : 0≤ε)
    (htail : tailFactor≤Tmax) (hterminal : terminalFactor≤1) :
    (∫s : ℝ,firstLogDensity 0 s)*(512*(512*32))*Γ*P*
      ((B*U)^ε*(Cd+Ct*tailFactor)+C*globalRayTripleConstant*U^(deltaLoss+8*ε)*
        (canonicalDensityConstant E J t*Clo+globalTerminalConstant A M*Chi*terminalFactor))≤
    canonicalBudgetCoefficient C Cd Ct Tmax Clo Chi A M*
      Γ*P*U^(deltaLoss+8*ε)*E*(1+‖t‖)^(2*J) := by
  have hi : 0≤∫s : ℝ,firstLogDensity 0 s :=
    integral_nonneg (fun s=>FirstPassCubeLabels.firstLogDensity_nonneg 0 s)
  have ht := globalTerminalConstant_nonneg A M
  have hRT : 0≤globalRayTripleConstant := by unfold globalRayTripleConstant;positivity
  have hU0 : 0<U := zero_lt_one.trans_le hU
  have hpow : (B*U)^ε≤U^(deltaLoss+8*ε) := by
    calc
      _ ≤ (U^2)^ε := Real.rpow_le_rpow (mul_nonneg hB hU0.le) (by nlinarith) hε
      _ = U^(2*ε) := by rw [←Real.rpow_natCast U 2,←Real.rpow_mul hU0.le];norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hheight : 1≤(1+‖t‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg t])
  have he : 1≤E*(1+‖t‖)^(2*J) := one_le_mul_of_one_le_of_one_le hE hheight
  have hdiag : (B*U)^ε*(Cd+Ct*tailFactor)≤
      U^(deltaLoss+8*ε)*(Cd+Ct*Tmax)*(E*(1+‖t‖)^(2*J)) := by
    calc
      _ ≤ (B*U)^ε*(Cd+Ct*Tmax) := by gcongr
      _ ≤ U^(deltaLoss+8*ε)*(Cd+Ct*Tmax) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) he
  have hchild : canonicalDensityConstant E J t*Clo+globalTerminalConstant A M*Chi*terminalFactor≤
      (6*(∫s : ℝ,firstLogDensity 0 s)^3*Clo+globalTerminalConstant A M*Chi)*
        (E*(1+‖t‖)^(2*J)) := by
    have hterm : globalTerminalConstant A M*Chi*terminalFactor≤
        globalTerminalConstant A M*Chi*(E*(1+‖t‖)^(2*J)) :=
      mul_le_mul_of_nonneg_left (hterminal.trans he) (mul_nonneg ht hChi)
    unfold canonicalDensityConstant
    nlinarith
  have hrest := mul_le_mul_of_nonneg_left hchild
    (mul_nonneg (mul_nonneg hC hRT) (Real.rpow_nonneg hU0.le (deltaLoss+8*ε)))
  have hsum := add_le_add hdiag hrest
  have hwhole := mul_le_mul_of_nonneg_left hsum
    (show 0≤(∫s : ℝ,firstLogDensity 0 s)*(512*(512*32))*Γ*P by positivity)
  exact hwhole.trans_eq (by unfold canonicalBudgetCoefficient;ring)
end OAI.SecondPassArithmetic
