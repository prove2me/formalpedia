-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.valuation_ofHeightOneSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:52.661191+00:00
-- url     : https://prove2.me/submissions/33da6630-0ebb-4637-9b30-8f1e7cc0cdc4

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Theorems.Thm_GroundTheory_FunctionField_Place_eq_of_le
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_le_one_iff
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_surjective
import Theorems.Thm_GroundTheory_FunctionField_valuation_eq_of_isEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IsDedekindDomain IsLocalRing
open scoped WithZero
open GroundTheory.FunctionField.Place
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra B K] [IsFractionRing B K]
  (hk : ∀ c : k, algebraMap k K c ∈ (algebraMap B K).range)
variable [IsFunctionField k K]
namespace GroundTheory.FunctionField.Place
theorem _root_.solution (P : HeightOneSpectrum B) :
    (ofHeightOneSpectrum B hk P).valuation = P.valuation K := by
  refine valuation_eq_of_isEquiv ?_ (ofHeightOneSpectrum B hk P).valuation_surjective
    (HeightOneSpectrum.valuation_surjective K P)
  refine Valuation.isEquiv_iff_val_le_one.2 fun {x} => ?_
  rw [Place.valuation_le_one_iff]
  have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K) (v := P)
  let Q : Place k K :=
    { ring := (P.valuation K).valuationSubring
      ne_top := (ofHeightOneSpectrum B hk P).ne_top ∘ fun htop => by
        apply le_antisymm le_top
        intro y _
        obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer K
        have hmem : π⁻¹ ∈ (P.valuation K).valuationSubring := htop ▸ ValuationSubring.mem_top _
        rw [Valuation.mem_valuationSubring_iff, map_inv₀, hπ, ← WithZero.exp_neg,
          ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
        omega
      algebraMap_mem := fun c => hle ((ofHeightOneSpectrum B hk P).algebraMap_mem c) }
  have heq : ofHeightOneSpectrum B hk P = Q := Place.eq_of_le hle
  constructor
  · exact fun hx => hle hx
  · intro hx
    have hxQ : x ∈ Q.ring := hx
    rw [← heq] at hxQ
    exact hxQ
end GroundTheory.FunctionField.Place
