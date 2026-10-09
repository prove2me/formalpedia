-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedRelativeFinalExtraction_side_floor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T00:15:25.73544+00:00
-- url     : https://prove2.me/submissions/bd8c7330-5439-4c28-89ac-4327535bc8d2

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

theorem preparedRelativeFinalExtraction_side_floor
    {X : Type*} (N : X → ℕ) {p extraction : ℝ} {C passagePower : ℕ}
    (hp : 0 ≤ p) (hC : C ≤ passagePower)
    (hextraction : extraction ≤ (p + 2) ^ C)
    (hN : ∀ i, Real.exp ((p + 2) ^ passagePower) ≤ (N i : ℝ)) :
    extraction ≤ (p + 2) ^ passagePower ∧
      ∀ i, Real.exp extraction ≤ (N i : ℝ) := by
  have h := hextraction.trans (pow_le_pow_right₀ (by linarith only [hp]) hC)
  exact ⟨h, fun i => (Real.exp_le_exp.mpr h).trans (hN i)⟩

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.VectorPolynomial.preparedRelativeFinalExtraction_side_floor.{u_1} := @OAI.Erdos3.VectorPolynomial.preparedRelativeFinalExtraction_side_floor.{u_1}
