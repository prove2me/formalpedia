-- Prove2me | solution 1 for OAI.CompletedGauss.short_completed_branch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T08:43:19.818495+00:00
-- url     : https://prove2.me/submissions/adeed01e-eac7-4557-9f98-a0b7085b493d

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_ProductColumns
import Theorems.Thm_OAI_CompletedGauss_mem_shortCubeRange
import Theorems.Thm_OAI_CompletedGauss_short_completed_energy
import Theorems.Thm_OAI_CompletedGauss_short_cube_scales

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
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve
namespace OAI.CompletedGauss
theorem _root_.solution {κ : Type*} [Fintype κ]
    (Ψ : κ → O →* ℂ) (hΨ : ∀k z,‖Ψ k z‖≤1)
    (W : ℝ → ℂ) (Z K R X F A : ℝ)
    (hZ : 1≤Z) (hK : 1≤K) (hR : 1≤R) (hF : 1≤F)
    (hFZ : F≤Z^(1/1000:ℝ)) (hA : 0≤A)
    (hmargin : K*R≤X*F*Z^(-(1/40:ℝ)))
    (hcompleted : ∀H∈shortCubeRange (Z^(1/1000:ℝ)),
      (∑k,‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤
        A*(K+K^2*R*F*(Ideal.absNorm H:ℝ)^3/X)) :
    (∑k,‖shortCompletedSum (Ψ k) W X (Z^(1/1000:ℝ))‖^2)≤
      (2*A*K)*(256*(columnDyadicLength (Z^(1/1000:ℝ))+1:ℝ))^2 := by
  apply short_completed_energy Ψ hΨ W X _ (2*A*K) (by positivity)
  intro H hH
  have hs := (mem_shortCubeRange _ H).mp hH
  have hn : 1≤(Ideal.absNorm H:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hs.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hsc := short_cube_scales Z K R X F (Ideal.absNorm H:ℝ)
    hZ hK hR hF hFZ hn hs.2.le hmargin
  apply (hcompleted H hH).trans
  nlinarith
end OAI.CompletedGauss
