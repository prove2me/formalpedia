-- Prove2me | solution 1 for GraphProblems.Color.exists_coloring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:13:52.854193+00:00
-- url     : https://prove2.me/submissions/10570c10-d603-4433-8221-fb3020c20cf2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Blocks
import Definitions.Def_GraphProblems_Color
import Theorems.Thm_GraphProblems_Color_sat_colorF
import Theorems.Thm_GraphProblems_Color_ext_asg
import Theorems.Thm_GraphProblems_Blocks_ext_val


set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
open GraphProblems.Color
open Blocks
namespace GraphProblems.Color
theorem _root_.solution (hAdj : StAdj) {n k : ℕ} (G : SimpleGraph (Fin n)) (a : Fin (n * k) → Bool) (ha : Sat (ext a) (colorF k n (matrix G))) :
    ∃ col : G.Coloring (Fin k), asg col = a := by
  obtain ⟨h1, h2, h3⟩ := (sat_colorF k n (matrix G) (ext a)).1 ha
  choose c hc hf using fun v : Fin n => h1 v v.2
  have huniq : ∀ (v : Fin n) (c' : ℕ), c' < k → c' ≠ c v → ext a (v * k + c') = false := by
    intro v c' hc' hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · rcases h2 v v.2 c' hc' (c v) (hc v) hlt with h | h
      · exact h
      · rw [hf v] at h
        cases h
    · rcases h2 v v.2 (c v) (hc v) c' hc' hgt with h | h
      · rw [hf v] at h
        cases h
      · exact h
  refine ⟨SimpleGraph.Coloring.mk (fun v => ⟨c v, hc v⟩) ?_, ?_⟩
  · intro u v huv heq
    have h4 : c u = c v := congrArg Fin.val heq
    rcases h3 u u.2 v v.2 ((hAdj n G u v).2 huv) (c u) (hc u) with h | h
    · rw [hf u] at h
      cases h
    · rw [h4, hf v] at h
      cases h
  · funext x
    have hk : 0 < k := Nat.pos_of_ne_zero fun h0 => by
      have h4 := x.2
      have h5 : n * k = 0 := by rw [h0, mul_zero]
      omega
    have hv : x.val / k < n := Nat.div_lt_of_lt_mul (lt_of_lt_of_eq x.2 (mul_comm n k))
    have hx : x.val = (⟨x.val / k, hv⟩ : Fin n).val * k + x.val % k := (Nat.div_add_mod' x.val k).symm
    have h5 := ext_asg (fun v => (⟨c v, hc v⟩ : Fin k)) ⟨x.val / k, hv⟩ (Nat.mod_lt x.val hk)
    rw [← hx, ext_val] at h5
    change asg (fun v => (⟨c v, hc v⟩ : Fin k)) x = a x
    rw [h5, ← ext_val a x]
    by_cases h6 : c ⟨x.val / k, hv⟩ = x.val % k
    · rw [decide_eq_true h6]
      have h7 := hf ⟨x.val / k, hv⟩
      rw [h6, ← hx] at h7
      exact h7.symm
    · rw [decide_eq_false h6]
      have h7 := huniq ⟨x.val / k, hv⟩ (x.val % k) (Nat.mod_lt x.val hk) (Ne.symm h6)
      rw [← hx] at h7
      exact h7.symm
end GraphProblems.Color
