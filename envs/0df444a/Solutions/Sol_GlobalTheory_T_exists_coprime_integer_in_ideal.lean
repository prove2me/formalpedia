-- Prove2me | solution 1 for GlobalTheory.T.exists_coprime_integer_in_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:06:38.129509+00:00
-- url     : https://prove2.me/submissions/4cf2a113-928b-4d67-aeba-e26b48837a35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoprimeIntegerInIdeal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoprimeIntegerInIdealStatement
import Theorems.Thm_GlobalTheory_NormCoprime_exists_coprime_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (c : Ideal (𝓞 K)) (l : ℕ), l.Prime → c ≠ ⊥ →
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ c → (l : 𝓞 K) ∉ v.asIdeal) → ∃ m : ℕ, m.Coprime l ∧ (m : 𝓞 K) ∈ c := by
  first | exact @GlobalTheory.NormCoprime.exists_coprime_mem | exact GlobalTheory.NormCoprime.exists_coprime_mem | (intros; apply GlobalTheory.NormCoprime.exists_coprime_mem <;> assumption)
end _root_.GlobalTheory.T
