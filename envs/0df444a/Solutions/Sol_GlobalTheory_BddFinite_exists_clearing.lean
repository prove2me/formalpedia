-- Prove2me | solution 1 for GlobalTheory.BddFinite.exists_clearing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:15:57.629537+00:00
-- url     : https://prove2.me/submissions/aa4473e7-7e89-433d-a965-275f4cb3a9df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfBoundedEmbeddingsAndValuations
import Theorems.Thm_GlobalTheory_BddFinite_exists_le_exp_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter
open GlobalTheory GlobalTheory.BddFinite
namespace GlobalTheory.BddFinite
theorem _root_.solution {K : Type} [Field K] [NumberField K] (A : Set K)
    (w : HeightOneSpectrum (𝓞 K)) (B : WithZero (Multiplicative ℤ))
    (hB : ∀ x ∈ A, w.valuation K x ≤ B) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ x ∈ A, w.valuation K ((a : K) * x) ≤ 1 := by
  obtain ⟨n, hn⟩ := exists_le_exp_nat B
  have hne : w.asIdeal ^ n ≠ ⊥ := pow_ne_zero n w.ne_bot
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨r, hr0, fun x hx => ?_⟩
  have h1 : w.intValuation r ≤ WithZero.exp (-(n : ℤ)) := (w.intValuation_le_pow_iff_mem r n).2 hr
  rw [map_mul]
  have h2 : w.valuation K (r : K) = w.intValuation r := w.valuation_of_algebraMap r
  rw [h2]
  calc w.intValuation r * w.valuation K x ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp (n : ℤ) :=
        mul_le_mul' h1 ((hB x hx).trans hn)
    _ = 1 := by rw [← WithZero.exp_add]; simp
end GlobalTheory.BddFinite
