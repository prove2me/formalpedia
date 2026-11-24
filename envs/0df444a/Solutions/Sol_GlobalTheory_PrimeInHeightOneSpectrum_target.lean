-- Prove2me | solution 1 for GlobalTheory.PrimeInHeightOneSpectrum.target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:24.003183+00:00
-- url     : https://prove2.me/submissions/1a781783-881a-4097-ba84-209e6af3cf93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimeMemHeightOneSpectrum
import Theorems.Thm_GlobalTheory_PrimeInHeightOneSpectrum_exists_prime_mem_heightOneSpectrum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PrimeInHeightOneSpectrum
namespace GlobalTheory.PrimeInHeightOneSpectrum
theorem _root_.solution : ∀ {K : Type} [inst : Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
    ∃ (p : ℕ), Nat.Prime p ∧ (↑p : NumberField.RingOfIntegers K) ∈
      IsDedekindDomain.HeightOneSpectrum.asIdeal v :=
  fun v => exists_prime_mem_heightOneSpectrum v
end GlobalTheory.PrimeInHeightOneSpectrum
