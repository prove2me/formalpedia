-- Prove2me | solution 1 for GlobalTheory.BCT.SuppFin.exists_ne_zero_intValuation_le_of_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:59:04.421717+00:00
-- url     : https://prove2.me/submissions/7ca1a364-a124-4cef-bf17-b267888746dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfValuationBoundedNormLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter
open GlobalTheory GlobalTheory.BCT GlobalTheory.BCT.SuppFin
namespace GlobalTheory.BCT.SuppFin
theorem _root_.solution {E : Type} [Field E] [NumberField E]
    (T : Finset (HeightOneSpectrum (𝓞 E))) (n : HeightOneSpectrum (𝓞 E) → ℕ) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ v ∈ T, v.intValuation d ≤ WithZero.exp (-(n v : ℤ)) := by
  classical
  have hJ : (∏ v ∈ T, v.asIdeal ^ n v) ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    exact fun v _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  exact ⟨d, hd0, fun v hv => (v.intValuation_le_pow_iff_mem d (n v)).mpr
    ((Ideal.prod_le_inf.trans (Finset.inf_le hv)) hd)⟩
end GlobalTheory.BCT.SuppFin
