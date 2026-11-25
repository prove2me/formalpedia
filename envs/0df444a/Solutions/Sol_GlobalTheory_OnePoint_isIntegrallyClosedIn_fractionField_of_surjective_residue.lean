-- Prove2me | solution 1 for GlobalTheory.OnePoint.isIntegrallyClosedIn_fractionField_of_surjective_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:09:52.338602+00:00
-- url     : https://prove2.me/submissions/86b4b61e-e416-4614-add2-c27707bd67cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
import Theorems.Thm_GlobalTheory_OnePoint_isIntegrallyClosedIn_fractionField_of_residue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
variable {K : Type u} [Field K]
namespace GlobalTheory.OnePoint
theorem _root_.solution (R : Type v) [CommRing R]
    [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] [Algebra K R] (L : Type w) [Field L]
    [Algebra R L] [IsFractionRing R L] [Algebra K L] [IsScalarTower K R L]
    (hres : Function.Surjective fun c : K ↦ IsLocalRing.residue R (algebraMap K R c)) :
    IsIntegrallyClosedIn K L := by
  refine isIntegrallyClosedIn_fractionField_of_residue R L fun r ↦ ?_
  obtain ⟨c, hc⟩ := hres (IsLocalRing.residue R r)
  refine ⟨c, ?_⟩
  rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff,
    map_sub, sub_eq_zero]
  exact hc.symm
end GlobalTheory.OnePoint
