-- Prove2me | solution 1 for GlobalTheory.PMonE.coefDet_pw_pow_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:17:32.228838+00:00
-- url     : https://prove2.me/submissions/8be1c5b8-5022-4697-aaf8-58bf34b8efdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MoorePowSubSelfEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalizedRowCoefficientMatricesDetNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
namespace GlobalTheory.PMonE
theorem _root_.solution (k : ℤ) (x : F) : pw p k x ^ p = pw p (k + 1) x := by
  unfold pw
  by_cases hk : 0 ≤ k
  · rw [if_pos hk, if_pos (by omega), ← pow_mul, ← pow_succ]
    congr 2; omega
  · rw [if_neg hk]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (-k).toNat = n + 1 := ⟨(-k).toNat - 1, by omega⟩
    rw [hn, Function.iterate_succ_apply']
    have e : ((frobeniusEquiv F p).symm (((frobeniusEquiv F p).symm)^[n] x)) ^ p =
        ((frobeniusEquiv F p).symm)^[n] x := by
      have := frobenius_apply_frobeniusEquiv_symm F p (((frobeniusEquiv F p).symm)^[n] x)
      rwa [frobenius_def] at this
    rw [e]
    by_cases hk1 : 0 ≤ k + 1
    · rw [if_pos hk1]
      have hn0 : n = 0 := by omega
      have h0 : (k + 1).toNat = 0 := by omega
      rw [hn0, h0]; simp
    · rw [if_neg hk1]; congr 1; omega
end GlobalTheory.PMonE
