-- Prove2me | solution 1 for GlobalTheory.CMFormBound.conj_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:03:57.260398+00:00
-- url     : https://prove2.me/submissions/8849f4d9-cae8-49e6-b49c-2fba0a695c43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodGaloisIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CMFormBound
namespace GlobalTheory.CMFormBound
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ) (hd : d.Prime) (r : E)
    (hr : r ^ 2 = -(d : E)) : IsCMField.complexConj E r = -r := by
  have h1 : (IsCMField.complexConj E r) ^ 2 = r ^ 2 := by
    rw [← map_pow, hr, map_neg, map_natCast]
  have hne : IsCMField.complexConj E r ≠ r := by
    intro h
    let ψ : E →+* ℂ := Classical.choice inferInstance
    have h2 : conj (ψ r) = ψ r := by rw [← IsCMField.complexEmbedding_complexConj, h]
    have h3 : (ψ r) ^ 2 = -(d : ℂ) := by rw [← map_pow, hr, map_neg, map_natCast]
    obtain ⟨x, hx⟩ : ∃ x : ℝ, (x : ℂ) = ψ r := ⟨(ψ r).re, Complex.conj_eq_iff_re.1 h2⟩
    rw [← hx] at h3
    have h4 : x ^ 2 = -(d : ℝ) := by exact_mod_cast h3
    have h5 : (0 : ℝ) < d := by exact_mod_cast hd.pos
    nlinarith [sq_nonneg x]
  have h6 : (IsCMField.complexConj E r - r) * (IsCMField.complexConj E r + r) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h6 with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact eq_neg_of_add_eq_zero_left h
end GlobalTheory.CMFormBound
