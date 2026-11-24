-- Prove2me | solution 1 for GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:42:09.211856+00:00
-- url     : https://prove2.me/submissions/d4f6dbe3-138b-4b03-a68a-9b59e4b52821

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsConductorAdicCompletion
import Theorems.Thm_GlobalTheory_ConductorAdicCompletion_exists_conductor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConductorAdicCompletion
namespace GlobalTheory.ConductorAdicCompletion
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      (ψ : AddChar (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v) ℂ),
      Continuous (⇑ψ : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v → ℂ) →
      (∀ t, ‖ψ t‖ = (1 : ℝ)) → (∃ t, ψ t ≠ (1 : ℂ)) →
      ∃ n : ℤ, ∀ t : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v,
        (∀ s ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v,
          ψ (t * s) = (1 : ℂ)) ↔
        (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v →
          WithZero (Multiplicative ℤ)) t ≤ WithZero.exp n := by
  intro F _ _ v ψ hc _ hne
  exact exists_conductor ψ hc hne
end GlobalTheory.ConductorAdicCompletion
