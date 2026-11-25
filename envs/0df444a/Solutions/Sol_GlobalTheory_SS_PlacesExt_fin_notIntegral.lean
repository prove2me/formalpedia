-- Prove2me | solution 1 for GlobalTheory.SS.PlacesExt.fin_notIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:55:04.868813+00:00
-- url     : https://prove2.me/submissions/55e133ee-b1f3-4270-b0b7-f3497beb13f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesFunctionField
import Theorems.Thm_GlobalTheory_SS_PlacesExt_fin_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.PlacesExt
open IsDedekindDomain Polynomial ReciprocityTheory.ChartRestriction.G.T0
variable {k F : Type} [Field k] [Field F] [Algebra k F] (Pl : Places k F)
namespace GlobalTheory.SS.PlacesExt
theorem _root_.solution {L : Type} [Field L] [Algebra F L] [FiniteDimensional F L] (y : L) :
    {i | ¬ IsIntegral (Pl.O i) y}.Finite := by
  have hy : IsIntegral F y := IsIntegral.of_finite F y
  refine ((minpoly F y).support.finite_toSet.biUnion
    fun n _ => fin_notMem Pl ((minpoly F y).coeff n)).subset fun i hi => ?_
  by_contra hc
  simp only [Set.mem_iUnion, not_exists, Set.mem_setOf_eq, not_not] at hc
  apply hi
  have hl : minpoly F y ∈ lifts (algebraMap (Pl.O i) F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ∈ (minpoly F y).support
    · exact ⟨⟨_, hc n hn⟩, rfl⟩
    · rw [notMem_support_iff.1 hn]; exact ⟨0, map_zero _⟩
  obtain ⟨q, hq, -, hm⟩ := lifts_and_degree_eq_and_monic hl (minpoly.monic hy)
  refine ⟨q, hm, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap F, hq, minpoly.aeval]
end GlobalTheory.SS.PlacesExt
