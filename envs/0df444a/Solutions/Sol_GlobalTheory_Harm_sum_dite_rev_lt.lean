-- Prove2me | solution 1 for GlobalTheory.Harm.sum_dite_rev_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:01.776337+00:00
-- url     : https://prove2.me/submissions/228f882a-bfcc-4c41-882c-d088994b56cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EqZeroOfPartialSumsNonneg
import Theorems.Thm_GlobalTheory_Harm_sum_dite_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Harm
open Finset
open Finset
namespace GlobalTheory.Harm
namespace _root_.GlobalTheory.Harm
theorem _root_.solution {m q : ℕ} (hq : q ≤ m) (f : Fin q → ℤ) :
    ∑ k : Fin m, (if h : m - 1 - (k : ℕ) < q then f ⟨m - 1 - k, h⟩ else 0) = ∑ k, f k := by
  rw [← _root_.GlobalTheory.Harm.sum_dite_lt hq f]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun k => ?_)
  have hk : ((Fin.revPerm k : Fin m) : ℕ) = m - 1 - k := by
    simp only [Fin.revPerm_apply, Fin.val_rev]
    omega
  simp only [hk]
end _root_.GlobalTheory.Harm
end GlobalTheory.Harm
