-- Prove2me | solution 1 for GlobalTheory.PMonE.norm_pw_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:34:10.393927+00:00
-- url     : https://prove2.me/submissions/936bd4d5-9db5-4edb-83ac-baf0bd0ddbd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormFrobeniusWindowSeriesTermMono
import Theorems.Thm_GlobalTheory_PMonE_iter_frobSymm_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
open GlobalTheory GlobalTheory.PMonE
namespace GlobalTheory.PMonE
theorem _root_.solution {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (k : ℤ) (y y' : F) (hy : ‖y‖ ≤ ‖y'‖) : ‖pw p k y‖ ≤ ‖pw p k y'‖ := by
  unfold pw
  split_ifs with hk
  · rw [norm_pow, norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hy _
  · set m := (-k).toNat
    have hN : p ^ m ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
    have e1 := iter_frobSymm_pow p m y
    have e2 := iter_frobSymm_pow p m y'
    by_contra hc
    push_neg at hc
    have := pow_lt_pow_left₀ hc (norm_nonneg _) hN
    rw [← norm_pow, ← norm_pow, e1, e2] at this
    linarith
end GlobalTheory.PMonE
