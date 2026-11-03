-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.gluedProfile_chart_m
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:30:01.466117+00:00
-- url     : https://prove2.me/submissions/2c0e09ea-01f3-496d-afcb-0abe48a20196

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D007

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanNeighborRowChart
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact group chart for an original neighboring-row profile -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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

local notation "profile" => D.gluedProfile T M F hunimod eW π b₀ cell βcell X βD
  haarN chartN hchartN pivot shrink B δ S

set_option maxHeartbeats 1000000 in
/-- At scales at least one, the glued original profile is precisely the
chart profile required by the polar source comparison. -/
theorem AffineNeighborRow.gluedProfile_chart_m_oai
    (hs : ∀ n, 1 ≤ D.scale n) :
    (∀ n, Measurable (profile n)) ∧
    (∀ n q, q ∈ (fun v => v * D.base n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (D.scale n) 1 ∪
      (fun v => v * D.base n * D.step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (D.scale n) 1 → ∀ z,
      (profile n q).val z = rescaledMapProfile
        (fun g => (π ((D.pair n).val.1 g)).toAdd) (D.center n) (F.inclusionN q)
        (max (Real.log (D.scale n)) 0)
        (F.profileChart (exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (max (Real.log (D.scale n)) 0))) z) ∧
    Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
        cell βcell (D.scale n) (D.base n))
      (f := (fun q => (profile n q, profile n (q * D.step n)))) ((((D.gluedProfile_properties T M F hunimod eW π b₀ cell βcell X βD haarN chartN hchartN pivot shrink B δ S).1 n).prodMk (((D.gluedProfile_properties T M F hunimod eW π b₀ cell βcell X βD haarN chartN hchartN pivot shrink B δ S).1 n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable)) atTop (𝓝 D.law) := by
  obtain ⟨hmeas, hactual, hlaw⟩ := D.gluedProfile_properties T M F hunimod eW π b₀
    cell βcell X βD haarN chartN hchartN pivot shrink B δ S
  refine ⟨hmeas, ?_, hlaw⟩
  intro n q hq z
  have hq' : q ∈ (fun v => v * D.base n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (D.scale n) 1 ∪
      (fun v => v * D.step n) '' ((fun v => v * D.base n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (D.scale n) 1) := by
    rcases hq with hq | ⟨v, hv, rfl⟩
    · exact Or.inl hq
    · exact Or.inr ⟨v * D.base n, ⟨v, hv, rfl⟩, rfl⟩
  have hlog : max (Real.log (D.scale n)) 0 = Real.log (D.scale n) :=
    max_eq_left (Real.log_nonneg (hs n))
  have h := hactual n q hq' z
  have hc (b : Basis (Fin (finrank ℝ H)) ℝ H) :
      F.profileChart b = fun z => ExpG (b.equivFun.symm z) := by
    funext z
    exact F.compatibleD _
  rw [hlog, hc]
  exact h

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.gluedProfile_chart_m_oai := @OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.gluedProfile_chart_m_oai
