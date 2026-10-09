-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedRelativeFinalEnvelope_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T23:25:44.555412+00:00
-- url     : https://prove2.me/submissions/2d0f5a03-50a3-4788-8eea-7d0e1499b75e

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B032

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeFinalPower
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure C) (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))

include hweight

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ}
  {G X : Type*}
  [Fintype G]
  [Fintype X]
  {I : Fin m → Type*}
  [∀ j, Fintype (I j)]
  {n : Fin m → ℕ}
  {B : LayerSamplerAxis I n → Type*}
  [∀ a, Fintype (B a)]
  {J : Fin m → Type*}
  [∀ j, Fintype (J j)]
  {U : ∀ j, Submodule ℝ (J j → ℝ)}
  {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
  {R σ : Fin m → ℝ}
  {S : LayerSamplerScale (G := G) B U b R σ}
  {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
  {hR : ∀ j, 0 < R j}
  {hσ : ∀ j, 0 < σ j}
  {N : X → ℕ}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
  {hm : ∀ j e, coefficients (poly j) e ∈ U j}
  {τ ξ : ℝ}
  {stride : X → ℕ}
  {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
  [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSamplerFamily

end AllocatedExternalCandidateSamplerFamily

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedRelativeFinalEnvelope_bounds
    (degree basePower inputPower preparationPower requiredPower : ℕ)
    (discount : ℝ) {p K : ℝ} (hp : 0 ≤ p)
    (hK : K ≤ ((p + 2) ^ basePower + 2) ^ inputPower) :
    let t := preparedRelativeFinalEnvelope degree basePower inputPower
      preparationPower requiredPower discount p
    1 ≤ t ∧
      max ((p + 2) ^ preparationPower) ((p + 2) ^ requiredPower + 1) ≤ t ∧
      K ≤ t ∧ discount⁻¹ ≤ t ∧ (p + 2) ^ basePower ≤ t ∧
      (degree : ℝ) * p ≤ t ∧ max 1 (max discount⁻¹ K) ≤ t := by
  intro t
  have hb : 0 ≤ p + 2 := by linarith only [hp]
  have hprep := pow_nonneg hb preparationPower
  have hreq := pow_nonneg hb requiredPower
  have hbase := pow_nonneg hb basePower
  have hinput := pow_nonneg (add_nonneg hbase (by norm_num : (0 : ℝ) ≤ 2)) inputPower
  have hceil := Nat.cast_nonneg (α := ℝ) ⌈discount⁻¹⌉₊
  have hdegree := mul_nonneg (Nat.cast_nonneg (α := ℝ) degree) hp
  have hinv : discount⁻¹ ≤ (⌈discount⁻¹⌉₊ : ℝ) := Nat.le_ceil _
  have ht : 1 ≤ t := by
    dsimp only [t, preparedRelativeFinalEnvelope]
    linarith only [hprep, hreq, hbase, hinput, hceil, hdegree]
  have hlate : max ((p + 2) ^ preparationPower) ((p + 2) ^ requiredPower + 1) ≤ t := by
    apply max_le <;> dsimp only [t, preparedRelativeFinalEnvelope] <;>
      linarith only [hprep, hreq, hbase, hinput, hceil, hdegree]
  have hKt : K ≤ t := by
    dsimp only [t, preparedRelativeFinalEnvelope]
    linarith only [hK, hprep, hreq, hbase, hceil, hdegree]
  have hit : discount⁻¹ ≤ t := by
    dsimp only [t, preparedRelativeFinalEnvelope]
    linarith only [hinv, hprep, hreq, hbase, hinput, hdegree]
  have hbt : (p + 2) ^ basePower ≤ t := by
    dsimp only [t, preparedRelativeFinalEnvelope]
    linarith only [hprep, hreq, hinput, hceil, hdegree]
  have hdt : (degree : ℝ) * p ≤ t := by
    dsimp only [t, preparedRelativeFinalEnvelope]
    linarith only [hprep, hreq, hbase, hinput, hceil]
  exact ⟨ht, hlate, hKt, hit, hbt, hdt, max_le ht (max_le hit hKt)⟩

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedRelativeFinalEnvelope_bounds := @OAI.Erdos3.VectorPolynomial.preparedRelativeFinalEnvelope_bounds
