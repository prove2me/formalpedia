-- Prove2me | solution 1 for GlobalTheory.SW.exists_int_div_of_intM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:31:08.793972+00:00
-- url     : https://prove2.me/submissions/38fc080e-7b83-4242-a633-5c95ff3bf562

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CoeffEqZeroOfHasSumMFourierOrthonormalImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EqOfSiegelThetaSeriesRationalEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
theorem _root_.solution {κ ι : Type} (R S : ℕ) (hR : 0 < R) (hS : 0 < S)
    (x : Matrix κ ι ℚ) (h : IntM ((R : ℚ) • x)) :
    ∃ s : κ × ι → ℤ, (Matrix.of fun k i => (s (k, i) : ℚ) / ((R * S : ℕ) : ℚ)) = x := by
  have h' : ∀ p : κ × ι, ∃ n : ℤ, (n : ℚ) = (R : ℚ) * x p.1 p.2 := by
    intro p
    have := h p.1 p.2
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    exact ⟨n, by simpa using hn⟩
  choose n hn using h'
  refine ⟨fun p => n p * S, ?_⟩
  ext k i
  have hR' : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  have hS' : (S : ℚ) ≠ 0 := by exact_mod_cast hS.ne'
  simp only [Matrix.of_apply]
  push_cast
  rw [hn (k, i)]
  field_simp
end GlobalTheory.SW
