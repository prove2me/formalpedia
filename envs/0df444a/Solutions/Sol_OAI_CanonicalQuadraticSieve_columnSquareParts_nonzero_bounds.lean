-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.columnSquareParts_nonzero_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T08:20:57.104182+00:00
-- url     : https://prove2.me/submissions/5087d680-8d7b-4ffc-b17d-9c6b9720cd38

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_ProductColumns
import Theorems.Thm_OAI_QuadraticSquarefreeKernel_norm_decomposition


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
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (hA : A∈S.image squarePart) :
    A≠0 ∧ 1≤(Ideal.absNorm A:ℝ) ∧ (Ideal.absNorm A:ℝ)≤X ∧ 1≤X/(Ideal.absNorm A:ℝ)^2 := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
  have hi := hS I hI
  have hAz := squarePart_ne_zero hi.1
  have hDz := (squarefree_squarefreePart I).ne_zero
  have ha : 1≤(Ideal.absNorm (squarePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hAz (Ideal.absNorm_eq_zero_iff.mp hz))
  have hd : 1≤(Ideal.absNorm (squarefreePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hDz (Ideal.absNorm_eq_zero_iff.mp hz))
  have hn : (Ideal.absNorm (squarePart I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)=(Ideal.absNorm I:ℝ) := by
    exact_mod_cast norm_decomposition I
  refine ⟨hAz,ha,by nlinarith,?_⟩
  apply (le_div_iff₀ (by positivity : 0<(Ideal.absNorm (squarePart I):ℝ)^2)).mpr
  nlinarith
end OAI.CanonicalQuadraticSieve
