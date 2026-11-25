-- Prove2me | solution 1 for GlobalTheory.integralClosure_eq_iInf_discreteValuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:54:27.584832+00:00
-- url     : https://prove2.me/submissions/313d3862-6a6b-48eb-a81d-ca1ce8292404

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_localSubring_range_le_valuationSubring_iff
import Theorems.Thm_GlobalTheory_exists_discreteValuationSubring_dominating_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {R L : Type*} [CommRing R] [IsLocalRing R] [Field L]
variable [IsNoetherianRing R] [Algebra R L]
namespace GlobalTheory
theorem _root_.solution [Algebra.EssFiniteType R L] :
    (integralClosure R L).toSubring =
      ⨅ V : {V : ValuationSubring L // IsDiscreteValuationRing V ∧
        LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring}, V.1.toSubring := by
  refine le_antisymm (le_iInf fun V x hx => ?_) fun x hx => ?_
  · have h := ((localSubring_range_le_valuationSubring_iff _ _).mp V.2.2).1
    letI : Algebra R V.1 := ((algebraMap R L).codRestrict V.1 h).toAlgebra
    have : IsScalarTower R V.1 L := .of_algebraMap_eq fun _ => rfl
    obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V.1) (K := L)).mp
      (IsIntegral.tower_top (R := R) hx)
    exact y.2
  · by_contra hn
    obtain ⟨V, h1, h2, h3⟩ := exists_discreteValuationSubring_dominating_notMem (R := R) hn
    exact h3 (iInf_le_of_le (α := Subring L) ⟨V, h1, h2⟩ le_rfl hx)
end GlobalTheory
