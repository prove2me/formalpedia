-- Prove2me | solution 1 for GordanGenProof.mem_gcone_insert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:31.742061+00:00
-- url     : https://prove2.me/submissions/39522622-3a55-4f73-a588-fb752987de8a

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_GordanCones
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GordanIntegerMultiple_ExistsIntMultiple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GordanGenProof
open Finset
namespace GordanGenProof
theorem _root_.solution {n : ℕ} {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → Fin n → ℚ}
    {w : ι} (hw : w ∉ s) (x : Fin n → ℚ) :
    x ∈ gcone (insert w s) f ↔ ∃ t : ℚ, 0 ≤ t ∧ x - t • f w ∈ gcone s f := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c w, hc w (Finset.mem_insert_self w s), c, fun i hi => hc i (Finset.mem_insert_of_mem hi), ?_⟩
    rw [Finset.sum_insert hw]
    abel
  · rintro ⟨t, ht, c, hc, hx⟩
    refine ⟨fun j => if j = w then t else c j, fun i hi => ?_, ?_⟩
    · rcases Finset.mem_insert.1 hi with h | h
      · subst h
        show 0 ≤ (if i = i then t else c i)
        rw [if_pos rfl]
        exact ht
      · show 0 ≤ (if i = w then t else c i)
        rw [if_neg (ne_of_mem_of_not_mem h hw)]
        exact hc i h
    · show x = ∑ j ∈ insert w s, (if j = w then t else c j) • f j
      rw [Finset.sum_insert hw, if_pos rfl]
      have hs : ∑ j ∈ s, (if j = w then t else c j) • f j = ∑ j ∈ s, c j • f j :=
        Finset.sum_congr rfl fun j hj => by rw [if_neg (ne_of_mem_of_not_mem hj hw)]
      rw [hs, ← hx]
      abel
end GordanGenProof
