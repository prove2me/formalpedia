-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_neighbor_label_threshold_m
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:39:46.954204+00:00
-- url     : https://prove2.me/submissions/0133dd76-f5f1-4078-88a2-b49d7b9bc3ea

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D007
import Definitions.Def_OAIQ093D008
import Definitions.Def_OAIQ093D010
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_eventually_root_neighbor_labels_eq_m

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanUniformNeighborLabels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform positive threshold for affine neighboring labels -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
  [IsTopologicalGroup F.D.carrier]


variable [Fintype I] [DecidableEq I] {J : Type} [Fintype J]

set_option maxHeartbeats 1000000 in
/-- The shrinking-family contradiction gives a positive enlargement
threshold uniform over all admissible sampling rows in the compact profile
family. The reflection comparison uses the precisely stated published inputs. -/
theorem exists_uniform_neighbor_label_threshold_m_oai
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (rem : RemezPolynomialInput)
    (π : G →* Multiplicative W) {Kπ : ℝ≥0}
    (hLip : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))

    (cell : Set W) (hcell : IsCompact cell) (hconv : Convex ℝ cell)
    (hint : (interior cell).Nonempty)
    (pivot : Fin M.letterCount → H)
    (hpivot : ∀ i, eW (heightProjection T.character (pivot i)) ∈ cell)
    (α : J → W →ₗ[ℝ] ℝ) (c : J → ℝ)
    (hpoly : cell = {w | ∀ j, α j w ≤ c j})
    (hactive : ∀ i j, α j (eW (heightProjection T.character (pivot i))) = c j →
      ∃ t : ℝ, 0 < t ∧ α j = t • (M.supportIn T hunimod eW).weight i)
    (βcell : M.Bases)
    (hβcell : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)

    {cN : ℕ} (aN : DynkinCoefficients cN 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SigmaFinite νD]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ))
    (shrink B : ℝ)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W)) (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)] [HasOuterApproxClosed (S × S)] :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ D : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
        haarN chartN hchartN pivot shrink B δ S (Λ := Λ), D.label₁ = D.label₂ := by
  classical
  by_contra hn
  push Not at hn
  have hbad (j : ℕ) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / ((j : ℝ) + 1) ∧
      ∃ D : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
        haarN chartN hchartN pivot shrink B δ S (Λ := Λ), D.label₁ ≠ D.label₂ :=
    hn (1 / ((j : ℝ) + 1)) (by positivity)
  choose δ hδpos hδle D hne using hbad
  have hδ : Tendsto δ atTop (𝓝 0) := squeeze_zero
    (fun j => (hδpos j).le) hδle tendsto_one_div_add_atTop_nhds_zero_nat
  have he := M.eventually_root_neighbor_labels_eq_m T F hunimod eW hExpG hinjG realize rem π hLip
    hπExp chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN haarD b₀
    cell hcell hconv hint pivot hpivot (fun j => (D j).mode) α c hpoly hactive
    (fun j => (D j).label₁) (fun j => (D j).label₂) βcell hβcell X hDnil bD₀ βD hβD
    aN hm hdim (fun j => (D j).scale) (fun j => (D j).grows) νD hpath hΛ
    (fun j => (D j).pair) (fun j => (D j).center) (fun j => (D j).radius)
    (fun j => (D j).base) (fun j => (D j).step) (fun j => δ j * B) δ
    (fun j => (D j).time) (fun j => (D j).basis)
    (fun j => (D j).radius_nonneg) (fun j => (D j).radius_subexponential)
    (fun j => (hδpos j).le) hδ (fun j => (D j).base_mem) (fun j => (D j).step_mem)
    (by simpa only [zero_mul] using hδ.mul_const B)
    (fun j => (D j).time_bound) (fun j => (D j).root_step) S hS
    (fun j => (D j).profile) (fun j => (D j).measurable_profile)
    (fun j => (D j).actual) (fun j => (D j).law) (fun j => (D j).converges)
    (fun j => (D j).point) (fun j => (D j).supported)
    (fun j => (D j).offset₁) (fun j => (D j).offset₂) shrink
    (fun j => (D j).affine₁) (fun j => (D j).affine₂)
  obtain ⟨j, hj⟩ := he.exists
  exact hne j hj

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_neighbor_label_threshold_m_oai := @OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_neighbor_label_threshold_m_oai
