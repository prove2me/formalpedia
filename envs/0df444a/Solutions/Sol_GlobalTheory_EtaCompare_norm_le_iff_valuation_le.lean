-- Prove2me | solution 1 for GlobalTheory.EtaCompare.norm_le_iff_valuation_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:27:37.084911+00:00
-- url     : https://prove2.me/submissions/c2ee87db-0c7a-47b9-9e55-0e2966037331

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormLeIffValuationLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.EtaCompare
open WithZero
namespace GlobalTheory.EtaCompare
theorem _root_.solution (K : UQ) {E : Type} [NormedField E] (φ : K.E ≃+* E)
    (hball : ∀ y : K.E, ‖φ y‖ ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range) (a b : K.E) (hb : b ≠ 0) :
    ‖φ a‖ ≤ ‖φ b‖ ↔ (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E a ≤
      (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E b := by
  set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E
  have hint : ∀ y : K.E, v y ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range := by
    intro y
    refine ⟨fun h => IsDiscreteValuationRing.exists_lift_of_le_one h, ?_⟩
    rintro ⟨a, rfl⟩
    exact (IsDiscreteValuationRing.maximalIdeal K.O).valuation_le_one a
  have hφb : φ b ≠ 0 := by simpa using hb
  have hvb : v b ≠ 0 := (Valuation.ne_zero_iff v).2 hb
  rw [← div_le_one₀ (norm_pos_iff.2 hφb), ← norm_div, ← map_div₀, hball, ← hint, map_div₀,
    div_le_one₀ (zero_lt_iff.2 hvb)]
end GlobalTheory.EtaCompare
