-- Prove2me | solution 1 for GlobalTheory.Ex.SymLift.odd_root_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:44:40.275576+00:00
-- url     : https://prove2.me/submissions/14da3c3b-4157-4d94-a2b8-9a9c0d33afb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.SymLift
namespace GlobalTheory.Ex.SymLift
theorem _root_.solution {U : Type} [CommGroup U] (j : ℕ) (E P w : U) (h : E ^ (2 * j + 1) = P ^ 2) :
    w = P / E ^ j ↔ (w ^ 2 = E ∧ w ^ (2 * j + 1) = P) := by
  constructor
  · rintro rfl
    have h' := congrArg Additive.ofMul h
    simp only [ofMul_pow] at h'
    constructor
    · apply Additive.ofMul.injective
      simp only [ofMul_pow, ofMul_div]
      linear_combination (norm := module) -h'
    · apply Additive.ofMul.injective
      simp only [ofMul_pow, ofMul_div]
      linear_combination (norm := module) -(j • h')
  · rintro ⟨rfl, rfl⟩
    rw [← pow_mul, pow_succ, mul_div_cancel_left]
end GlobalTheory.Ex.SymLift
