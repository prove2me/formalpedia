-- Prove2me | solution 1 for KernelRamsey.ramsey_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:00:39.896285+00:00
-- url     : https://prove2.me/submissions/fc560a18-0ab5-4fb7-aa94-9dbbc1ec50a4

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Theorems.Thm_KernelRamsey_noClique_sound
import Theorems.Thm_KernelRamsey_testBit_complementRows
open KernelRamsey

theorem solution {n s t : Nat} (rows : List Nat)
    (hsymm : ∀ i j : Fin n, (row rows i.val).testBit j.val = (row rows j.val).testBit i.val)
    (h1 : noClique rows n s (fullMask n) = true)
    (h2 : noClique (complementRows n rows) n t (fullMask n) = true) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree s ∧ Gᶜ.CliqueFree t := by
  refine ⟨maskGraph n rows hsymm, ?_, ?_⟩
  · intro S hS
    rw [SimpleGraph.isNClique_iff] at hS
    obtain ⟨hcl, hcard⟩ := hS
    refine noClique_sound rows n s _ h1 S hcard (fun v _ => ?_) ?_
    · simp [fullMask, Nat.testBit_two_pow_sub_one, v.isLt]
    · intro i hi j hj hij
      exact (hcl hi hj hij).2
  · intro S hS
    rw [SimpleGraph.isNClique_iff] at hS
    obtain ⟨hcl, hcard⟩ := hS
    refine noClique_sound (complementRows n rows) n t _ h2 S hcard (fun v _ => ?_) ?_
    · simp [fullMask, Nat.testBit_two_pow_sub_one, v.isLt]
    · intro i hi j hj hij
      have hadj := hcl hi hj hij
      rw [testBit_complementRows]
      simp only [SimpleGraph.compl_adj, maskGraph] at hadj
      have : ¬ (row rows i.val).testBit j.val = true := fun hb => hadj.2 ⟨hij, hb⟩
      have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
      simp [this, hv]
