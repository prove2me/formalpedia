-- Prove2me | solution 1 for GlobalTheory.SympModN.exists_eq_nsmul_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:02:41.606929+00:00
-- url     : https://prove2.me/submissions/eb5e7dd0-861e-433e-bf7e-2e540a12347c

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SRelOneOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymplecticSimilitudeInvertibleModN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SympModN
namespace GlobalTheory.SympModN
theorem _root_.solution {ι : Type*} (N : ℕ) (hN : N ≠ 0) (a : ι → ℤ) :
    (∃ b, a = N • b) ↔ ∀ j, (N : ℤ) ∣ a j := by
  constructor
  · rintro ⟨b, rfl⟩ j
    simp [nsmul_eq_mul]
  · intro hd
    refine ⟨fun j => a j / N, funext fun j => ?_⟩
    simp [nsmul_eq_mul, Int.mul_ediv_cancel' (hd j)]
end GlobalTheory.SympModN
