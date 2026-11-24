-- Prove2me | solution 1 for GlobalTheory.AdaptedDet.prod_interp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:54:17.57199+00:00
-- url     : https://prove2.me/submissions/5b643456-1cf3-45db-9e43-e77f6d5c1c58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmUnitPowFourIdempotentModEight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AdaptedDet
namespace GlobalTheory.AdaptedDet
theorem _root_.solution {K : Type} [CommRing K] (n e t : K) (he : e * e - e = n * t)
    (hei : IsIntegral ℤ e) (hti : IsIntegral ℤ t) (s : Multiset K)
    (hs : ∀ μ ∈ s, IsIntegral ℤ μ) :
    ∃ y, IsIntegral ℤ y ∧ (s.map fun μ => e * μ + (1 - e)).prod = e * s.prod + (1 - e) + n * y := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, isIntegral_zero, by simp⟩
  | cons μ s ih =>
    obtain ⟨y, hy, h⟩ := ih fun a ha => hs a (Multiset.mem_cons_of_mem ha)
    have hμ := hs μ (Multiset.mem_cons_self _ _)
    have hQ : IsIntegral ℤ s.prod :=
      IsIntegral.multiset_prod fun a ha => hs a (Multiset.mem_cons_of_mem ha)
    refine ⟨y * (e * μ + (1 - e)) + t * (μ * s.prod - μ - s.prod + 1), ?_, ?_⟩
    · exact (hy.mul ((hei.mul hμ).add (isIntegral_one.sub hei))).add
        (hti.mul ((((hμ.mul hQ).sub hμ).sub hQ).add isIntegral_one))
    · rw [Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, h]
      linear_combination (μ * s.prod - μ - s.prod + 1) * he
end GlobalTheory.AdaptedDet
