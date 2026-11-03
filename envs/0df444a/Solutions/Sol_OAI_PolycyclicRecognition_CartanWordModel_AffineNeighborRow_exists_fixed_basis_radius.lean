-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.exists_fixed_basis_radius
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:48:25.737114+00:00
-- url     : https://prove2.me/submissions/92668b03-e17a-471e-8fe5-9b084715db11

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D016

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanNeighborRowBasis
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed maximizing bases for affine neighboring rows -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier]


variable [Fintype I] [DecidableEq I]


variable (π : G →* Multiplicative W)
  (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  (cell : Set W) (βcell : M.Bases)
  (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (pivot : Fin M.letterCount → H) (shrink B δ : ℝ)
  (S : Set C((Fin (finrank ℝ H) → ℝ), W))
  [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
  {Λ : ℝ≥0}
  (D : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B δ S (Λ := Λ))

set_option maxHeartbeats 1000000 in
omit [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier] in
/-- The original row has a common subexponential radius in the fixed
maximizing basis, without changing any of its sampled group elements. -/
theorem AffineNeighborRow.exists_fixed_basis_radius_oai
    (hcell : IsCompact cell) (hne : cell.Nonempty)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (hδ : 0 ≤ δ) (hs : ∀ n, 0 ≤ D.scale n) :
    ∃ R : ℕ → ℝ, (∀ n, 0 ≤ R n) ∧ HasSubexponentialUpperBoundSeq D.scale R ∧
      (∀ n, D.base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        ((fun w => (1 + δ) • w) '' cell) βcell (D.scale n) (R n)) ∧
      (∀ n, D.step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        ((fun w => (1 + δ) • w) '' cell) βcell (D.scale n) (R n)) := by
  let E := D.fixedBasis T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B δ S hcell hne hβ hδ hs
  exact ⟨E.radius, E.radius_nonneg, E.radius_subexponential, E.base_mem, E.step_mem⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.exists_fixed_basis_radius_oai.{u_1, u_2, u_3, u_4} := @OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.exists_fixed_basis_radius_oai.{u_1, u_2, u_3, u_4}
