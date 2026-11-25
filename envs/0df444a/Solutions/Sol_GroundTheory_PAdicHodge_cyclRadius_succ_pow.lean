-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cyclRadius_succ_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:28:10.556841+00:00
-- url     : https://prove2.me/submissions/938eda89-5fe4-4740-953d-aaedf62fe217

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_totient_prime_pow_succ
import Theorems.Thm_GroundTheory_PAdicHodge_cyclRadius_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_cyclRadius_pow_totient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) : cyclRadius p (k + 1) ^ p = cyclRadius p k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hφ : Nat.totient (p ^ (j + 1)) ≠ 0 :=
    (Nat.totient_pos.2 (pow_pos (Fact.out : p.Prime).pos _)).ne'
  refine (pow_left_inj₀ (pow_nonneg (cyclRadius_nonneg (p := p) _) _) (cyclRadius_nonneg (p := p) _)
    hφ).1 ?_
  rw [← pow_mul, ← totient_prime_pow_succ (p := p) (k := j + 1) (by omega),
    cyclRadius_pow_totient (p := p) (j + 1), cyclRadius_pow_totient (p := p) j]
end GroundTheory.PAdicHodge
