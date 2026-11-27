-- Prove2me | solution 1 for GlobalTheory.exists_valuationSubring_complex_prime_mem_nonunits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:26.430877+00:00
-- url     : https://prove2.me/submissions/4ebb9534-2a51-498b-8eaf-08f89867d082

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsValuationSubringComplexPrimeMemNonunits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ p : ℕ, p.Prime → ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits := by
  intro p hp
  let A : Subring ℂ := (Int.castRingHom ℂ).range
  have hI : Ideal.span {(p : A)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top, isUnit_iff_exists_inv]
    rintro ⟨⟨b, n, rfl⟩, hb⟩
    have h1 : ((p : ℂ)) * (n : ℂ) = 1 := by
      have := congrArg (Subtype.val) hb
      simpa using this
    have h2 : (p : ℤ) * n = 1 := by exact_mod_cast h1
    have h3 : (p : ℤ) ∣ 1 := ⟨n, h2.symm⟩
    have h4 : p ∣ 1 := by exact_mod_cast h3
    exact hp.one_lt.ne' (Nat.dvd_one.mp h4)
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  refine ⟨B, hB ⟨(p : A), Ideal.subset_span rfl, by simp⟩⟩
end GlobalTheory
