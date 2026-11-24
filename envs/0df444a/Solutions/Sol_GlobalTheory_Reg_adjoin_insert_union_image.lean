-- Prove2me | solution 1 for GlobalTheory.Reg.adjoin_insert_union_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:55:16.301565+00:00
-- url     : https://prove2.me/submissions/bd2e46fb-f5f9-4618-932b-2baf8c00e588

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AdjoinRatiosOfSpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_NaturalRuleValueBaseChangeOfIsReducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_SpanEvalEqTopOfNoCommonZeroReducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsRefinedCoveringChartFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory GlobalTheory.Reg
namespace GlobalTheory.Reg
theorem _root_.solution {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [DecidableEq Ω] (x : Ω)
    (G : Finset Ω) {m : ℕ} (r : Fin m → Ω) :
    Algebra.adjoin K (insert x ((G ∪ Finset.univ.image r : Finset Ω) : Set Ω)) =
      Algebra.adjoin K ((Algebra.adjoin K (insert x (G : Set Ω)) : Set Ω) ∪ Set.range r) := by
  apply le_antisymm
  · apply Algebra.adjoin_mono
    intro z hz
    rcases hz with rfl | hz
    · exact Or.inl (Algebra.subset_adjoin (Or.inl rfl))
    · rcases Finset.mem_union.1 hz with h | h
      · exact Or.inl (Algebra.subset_adjoin (Or.inr h))
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
        exact Or.inr ⟨i, rfl⟩
  · apply Algebra.adjoin_le
    rintro z (hz | ⟨i, rfl⟩)
    · refine Algebra.adjoin_mono ?_ hz
      apply Set.insert_subset_insert
      intro g hg
      exact Finset.mem_coe.2 (Finset.mem_union_left _ hg)
    · exact Algebra.subset_adjoin (Or.inr (Finset.mem_coe.2 (Finset.mem_union_right _
        (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))))
end GlobalTheory.Reg
