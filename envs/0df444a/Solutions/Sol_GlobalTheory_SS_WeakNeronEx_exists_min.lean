-- Prove2me | solution 1 for GlobalTheory.SS.WeakNeronEx.exists_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:24:40.028237+00:00
-- url     : https://prove2.me/submissions/4b0d349a-e65e-4025-b635-8985a1e674e5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeakNeronModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WeakNeronEx
open GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out
namespace GlobalTheory.SS.WeakNeronEx
theorem _root_.solution {V L : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field L] [Algebra V L]
    [IsFractionRing V L] {I : Type} [Finite I] [Nonempty I] (c : I → L) :
    ∃ i, ∀ j, ∃ t : V, c j = algebraMap V L t * c i := by
  obtain ⟨i, hi⟩ := Finite.exists_max (fun j => ValuationRing.valuation V L (c j))
  refine ⟨i, fun j => ?_⟩
  by_cases h0 : c i = 0
  · have := hi j
    simp only [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact ⟨0, by simp [this]⟩
  · have : c j / c i ∈ (ValuationRing.valuation V L).integer := by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ (hi j) zero_le'
    obtain ⟨t, ht⟩ := (ValuationRing.mem_integer_iff V L _).1 this
    exact ⟨t, by rw [ht, div_mul_cancel₀ _ h0]⟩
end GlobalTheory.SS.WeakNeronEx
