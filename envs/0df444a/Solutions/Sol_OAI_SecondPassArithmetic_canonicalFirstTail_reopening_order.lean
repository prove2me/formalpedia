-- Prove2me | solution 1 for OAI.SecondPassArithmetic.canonicalFirstTail_reopening_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:42:25.1042+00:00
-- url     : https://prove2.me/submissions/ac730631-5373-4b8b-9f93-5c63caa78cc7

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BarrierPotential
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CutoffOrders
import Theorems.Thm_OAI_SecondPassArithmetic_exists_polynomial_cutoff_order
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalFirstTail_polynomial


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
open OAI.SecondPassArithmetic
namespace OAI.SecondPassArithmetic
theorem _root_.solution (η ε R : ℝ) (hη : 0<η) (hε : 0≤ε) :
    ∃N : ℕ,0<N ∧ ∀Cscale C Γ B₀ B lengthScale F Ksrc Z M : ℝ,
      1≤Cscale → 0≤C → 0≤B₀ → 0≤B → 0≤lengthScale → 0≤F → 1≤Ksrc → 1≤Z →
      B₀≤Cscale*Z^4 → B≤Cscale*Z^4 → lengthScale≤Cscale*Z^4 → F≤Cscale*Z^4 → Ksrc≤Cscale*Z^4 →
      B₀*(C*B^(4+ε)*lengthScale^4*F*Γ^2*Ksrc*(1+lengthScale^3*B^4/Ksrc)^2/
        (1+(Ksrc/(Ksrc/Z^η))/Real.exp (2*M))^N)≤
        (4*C*Γ^2*(Real.exp (2*M))^N*Cscale^(25+ε))*Z^(-R) := by
  obtain ⟨N,hN,horder⟩ := exists_polynomial_cutoff_order 4 (25+ε) η R hη
  refine ⟨N,hN,?_⟩
  intro Cscale C Γ B₀ B lengthScale F Ksrc Z M hCs hC hB₀ hB hL hF hK hZ hB₀U hBU hLU hFU hKU
  have hU : 1≤Cscale*Z^4 := one_le_mul_of_one_le_of_one_le hCs (one_le_pow₀ hZ)
  have hb := canonicalFirstTail_polynomial C Γ B₀ B lengthScale F Ksrc (Cscale*Z^4) Z η ε M N
    hC hB₀ hB hL hF hK hU hε (by linarith) hB₀U hBU hLU hFU hKU
  have ho := horder Cscale Z (by linarith) hZ
  have ho' : (Cscale*Z^4)^(25+ε)/Z^(η*N)≤Cscale^(25+ε)*Z^(-R) := by
    norm_num [Real.rpow_natCast] at ho ⊢
    exact ho
  apply hb.trans
  have hm := mul_le_mul_of_nonneg_left ho'
    (show 0≤4*C*Γ^2*(Real.exp (2*M))^N by positivity)
  convert hm using 1 <;> ring
end OAI.SecondPassArithmetic
