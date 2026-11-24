-- Prove2me | solution 1 for GlobalTheory.EtaCompare.norm_eq_iff_valuation_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:49:15.241867+00:00
-- url     : https://prove2.me/submissions/4232dee0-cae7-4183-ab09-68ae227bb72e

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormLeIffValuationLe
import Theorems.Thm_GlobalTheory_EtaCompare_norm_le_iff_valuation_le

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
    (hball : ∀ y : K.E, ‖φ y‖ ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range) (a b : K.E) :
    ‖φ a‖ = ‖φ b‖ ↔ (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E a =
      (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E b := by
  set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E
  by_cases hb : b = 0
  · subst hb; simp [v]
  by_cases ha : a = 0
  · subst ha
    simp only [map_zero, norm_zero, v]
    constructor
    · intro h; exact absurd (norm_eq_zero.1 h.symm) (by simpa using hb)
    · intro h; exact absurd ((Valuation.zero_iff _).1 h.symm) hb
  rw [le_antisymm_iff, le_antisymm_iff, norm_le_iff_valuation_le K φ hball a b hb,
    norm_le_iff_valuation_le K φ hball b a ha]
end GlobalTheory.EtaCompare
