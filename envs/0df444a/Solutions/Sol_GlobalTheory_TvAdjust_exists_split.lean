-- Prove2me | solution 1 for GlobalTheory.TvAdjust.exists_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:39:08.415993+00:00
-- url     : https://prove2.me/submissions/e51ddd6d-d3fb-4723-990f-2dfa273135f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ImportsTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNsmulMulVecMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTraceZeroAdjustmentOfHermitianLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
open GlobalTheory GlobalTheory.TvAdjust
namespace GlobalTheory.TvAdjust
theorem _root_.solution (b : ℕ) (N : ℕ) (hN : 0 < N) :
    ∃ A B e : ℕ, N = A * B ∧ A ∣ b ^ e ∧ B.Coprime b := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases hg : N.Coprime b
    · exact ⟨1, N, 0, by simp, by simp, hg⟩
    · obtain ⟨M, hM⟩ := Nat.gcd_dvd_left N b
      have hg0 : 0 < N.gcd b := Nat.gcd_pos_of_pos_left _ hN
      have hg1 : 1 < N.gcd b := by
        rcases Nat.lt_or_ge 1 (N.gcd b) with h | h
        · exact h
        · exact absurd (show N.gcd b = 1 by omega) hg
      have hM0 : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; omega)
      have hlt : M < N := by nlinarith
      obtain ⟨A, B, e, h1, h2, h3⟩ := ih M hlt hM0
      refine ⟨N.gcd b * A, B, e + 1, by rw [mul_assoc, ← h1]; exact hM, ?_, h3⟩
      rw [pow_succ']
      exact mul_dvd_mul (Nat.gcd_dvd_right N b) h2
end GlobalTheory.TvAdjust
