-- Prove2me | solution 1 for GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:24:31.648945+00:00
-- url     : https://prove2.me/submissions/07d6adc4-4a53-44ab-af1b-06a6cad6dc8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareMulOfNonsquareUnits
import Theorems.Thm_GlobalTheory_LocalQuad_isSquare_of_valued_sub_one_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm IsLocalRing
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain IsLocalRing
open scoped WithZero
namespace GlobalTheory.QNorm
namespace _root_.GlobalTheory.QNorm
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (h2 : Valued.v (2 : v.adicCompletion F) = 1)
    (z : v.adicCompletionIntegers F) (hz : Valued.v (z : v.adicCompletion F) = 1)
    (h : IsSquare (residue (v.adicCompletionIntegers F) z)) :
    IsSquare (z : v.adicCompletion F) := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨w, rfl⟩ := residue_surjective r
  have hmem : z - w * w ∈ maximalIdeal (v.adicCompletionIntegers F) := by
    rw [← residue_eq_zero_iff, map_sub, map_mul, hr, sub_self]
  have hlt : Valued.v ((z : v.adicCompletion F) - w * w) < 1 := by
    have hnu : ¬ IsUnit (z - w * w) := hmem
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hnu
    have hle := ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (z - w * w).2)
    push_cast at hnu hle
    exact lt_of_le_of_ne hle hnu
  have hw : Valued.v (w : v.adicCompletion F) = 1 := by
    by_contra hne
    have hwle := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 w.2
    have hw1 : Valued.v (w : v.adicCompletion F) < 1 := lt_of_le_of_ne hwle hne
    have : Valued.v (z : v.adicCompletion F) < 1 := by
      have hsplit : (z : v.adicCompletion F) = ((z : v.adicCompletion F) - w * w) + w * w := by ring
      rw [hsplit]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hlt ?_)
      rw [map_mul]
      calc Valued.v (w : v.adicCompletion F) * Valued.v (w : v.adicCompletion F)
          ≤ 1 * Valued.v (w : v.adicCompletion F) := by gcongr
        _ < 1 := by rw [one_mul]; exact hw1
    rw [hz] at this
    exact lt_irrefl _ this
  have hw0 : (w : v.adicCompletion F) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hw; exact zero_ne_one hw
  have h4 : Valued.v (4 : v.adicCompletion F) = 1 := by
    rw [show (4 : v.adicCompletion F) = 2 * 2 by norm_num, map_mul, h2, one_mul]
  have hsq : IsSquare ((z : v.adicCompletion F) / (w * w)) := by
    apply _root_.GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt
    rw [h4, show (z : v.adicCompletion F) / (w * w) - 1 = ((z : v.adicCompletion F) - w * w) / (w * w) by
      field_simp, map_div₀, map_mul, hw, mul_one, div_one]
    exact hlt
  obtain ⟨s, hs⟩ := hsq
  refine ⟨s * w, ?_⟩
  have : (z : v.adicCompletion F) = (z : v.adicCompletion F) / (w * w) * (w * w) := by
    field_simp
  rw [this, hs]
  ring
end _root_.GlobalTheory.QNorm
end GlobalTheory.QNorm
