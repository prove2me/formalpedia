-- Prove2me | solution 1 for GlobalTheory.EntriesExpBound.exists_entries_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:43:30.362176+00:00
-- url     : https://prove2.me/submissions/f6ee030f-ff52-4436-871c-74596fa51894

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsEntriesLeExp
import Theorems.Thm_GlobalTheory_EntriesExpBound_exists_nat_le_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EntriesExpBound
namespace GlobalTheory.EntriesExpBound
theorem _root_.solution {K : Type} [inst : Field K]
    [inst_1 : Valued K (WithZero (Multiplicative ℤ))] {m : ℕ} (A : Matrix (Fin m) (Fin m) K) :
    ∃ (k : ℕ), ∀ (r s : Fin m),
      (Valued.v : K → WithZero (Multiplicative ℤ)) (A r s) ≤ WithZero.exp (↑k : ℤ) := by
  choose f hf using fun p : Fin m × Fin m =>
    exists_nat_le_exp ((Valued.v : K → WithZero (Multiplicative ℤ)) (A p.1 p.2))
  refine ⟨Finset.univ.sup f, fun r s => (hf (r, s)).trans ?_⟩
  exact WithZero.exp_le_exp.mpr
    (Int.ofNat_le.mpr (Finset.le_sup (f := f) (Finset.mem_univ (r, s))))
end GlobalTheory.EntriesExpBound
