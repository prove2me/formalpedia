-- Prove2me | solution 1 for GlobalTheory.SS.PlacesExt.projLine_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:33:03.859798+00:00
-- url     : https://prove2.me/submissions/f92f8237-0862-4892-a60d-1510f72a7f08

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
variable (k : Type) [Field k]
namespace GlobalTheory.SS.PlacesExt
theorem _root_.solution (c : RatFunc k) (h : ∀ i, c ∈ (projLinePlaces k).O i) :
    c ∈ Set.range (algebraMap k (RatFunc k)) := by
  classical
  obtain ⟨p, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := k[X]) (RatFunc k) c fun v => by
    obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal v.asIdeal).principal
    have hg0 : g ≠ 0 := by
      rintro rfl
      exact v.ne_bot (by simpa using hg)
    have hg' : v.asIdeal = Ideal.span {g} := hg
    have hp : Prime g := (Ideal.span_singleton_prime hg0).1 (hg' ▸ v.isPrime)
    have hn : Associated (normalize g) g := normalize_associated g
    let π : MonIrr k := ⟨normalize g, monic_normalize hg0, hn.symm.irreducible hp.irreducible⟩
    have : π.prime = v := HeightOneSpectrum.ext
      ((Ideal.span_singleton_eq_span_singleton.2 hn).trans hg'.symm)
    rw [← this]
    exact h (some π)
  by_cases hp : p = 0
  · exact ⟨0, by simp [hp]⟩
  have hp' : algebraMap k[X] (RatFunc k) p ≠ 0 := by simpa using hp
  have h1 : 0 ≤ plOrd k none (algebraMap k[X] (RatFunc k) p) :=
    ((projLinePlaces k).mem none (Units.mk0 _ hp')).1 (h none)
  rw [plOrd_none hp] at h1
  have h2 : p.natDegree = 0 := by omega
  refine ⟨p.coeff 0, ?_⟩
  rw [IsScalarTower.algebraMap_apply k k[X] (RatFunc k), algebraMap_eq, ← eq_C_of_natDegree_eq_zero h2]
end GlobalTheory.SS.PlacesExt
