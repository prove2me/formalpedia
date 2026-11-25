-- Prove2me | solution 1 for GlobalTheory.SS.PlacesExt.isAlgebraic_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:20:01.727363+00:00
-- url     : https://prove2.me/submissions/5ee6b792-a8c4-4a1d-8057-f090a05c56d2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesFunctionField

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
variable {k F L : Type} [Field k] [Field F] [Algebra k F] [Field L] [Algebra F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L] (Pl : Places k F)
namespace GlobalTheory.SS.PlacesExt
theorem _root_.solution [Algebra k L] [IsScalarTower k F L]
    (hc : ∀ c : F, (∀ i, c ∈ Pl.O i) → c ∈ Set.range (algebraMap k F)) (y : L)
    (hy : ∀ i, IsIntegral (Pl.O i) y) : IsAlgebraic k y := by
  have hyF : IsIntegral F y := IsIntegral.of_finite F y
  have hl : minpoly F y ∈ lifts (algebraMap k F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    refine hc _ fun i => ?_
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' F (hy i), coeff_map]
    exact ((minpoly (Pl.O i) y).coeff n).2
  obtain ⟨q, hq, -, hm⟩ := lifts_and_degree_eq_and_monic hl (minpoly.monic hyF)
  refine ⟨q, hm.ne_zero, ?_⟩
  rw [← aeval_map_algebraMap F, hq, minpoly.aeval]
end GlobalTheory.SS.PlacesExt
