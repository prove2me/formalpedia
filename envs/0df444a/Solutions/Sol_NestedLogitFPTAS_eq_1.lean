-- Prove2me | solution 1 for NestedLogitFPTAS.eq_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:04:58.643353+00:00
-- url     : https://prove2.me/submissions/da2b4fb9-096c-4ef8-b8f9-120fbf158fb0

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model

open NestedLogitFPTAS in
theorem solution {n M : ℕ} (I : Instance n M) (_hI : I.Standing) (S : Finset (Fin n)) :
    I.R S = I.rhoRange 1 M S / (I.w0 + I.omegaRange 1 M S) := by
  have hf : (Finset.univ.filter (fun m : Fin M => 1 ≤ m.val + 1 ∧ m.val + 1 ≤ M)) =
      Finset.univ := by
    ext m; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; omega
  unfold Instance.R Instance.nu Instance.rhoRange Instance.omegaRange
  rw [hf, Finset.sum_div]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_div_assoc]
