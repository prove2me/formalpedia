-- Prove2me | solution 1 for Groundwork.Host.mainLoop_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:01:10.337211+00:00
-- url     : https://prove2.me/submissions/7b04907c-c3f6-45eb-84a5-319b3a396326

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Machine_Lift
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Machine_Host
import Theorems.Thm_Groundwork_Host_within_io
import Theorems.Thm_Groundwork_Host_chkQ_none
import Theorems.Thm_Groundwork_Host_chkQ_some
import Theorems.Thm_Groundwork_Host_size_le_of_reaches
import Theorems.Thm_Groundwork_Host_look_within
import Theorems.Thm_Groundwork_TM_Frag_Within_seq
import Theorems.Thm_Groundwork_TM_Frag_loop_runs_exit
import Theorems.Thm_Groundwork_TM_Frag_loop_runs_iter


set_option autoImplicit false
section
section
open Groundwork
open TM Turing
open Groundwork.Host
variable {M : Stepped (List Bool) Bool}
variable [Enc M.σ]
variable {Ps Po : Fr} {tS tO : ℕ → ℕ}
  (hS : ∀ (s : M.σ) (M' A B N : List Sym),
    Ps.Within (st (wd s ++ M') A B N) (tS (len s)) (st (wd (M.step s) ++ M') A B N))
  (hO : ∀ (s : M.σ) (M' A B N : List Sym),
    Po.Within (st (wd s ++ M') A B N) (tO (len s)) (st (wd (M.out s) ++ M') A B N))
include hS hO
namespace Groundwork.Host
theorem _root_.solution (mS : Monotone tS) (mO : Monotone tO) {S L : ℕ} (hL : ∀ s : M.σ, size s ≤ S → len s ≤ L) {b : Bool}
    {s : M.σ} {t : ℕ} (h : M.Reaches S b s t) :
    ∃ s' : M.σ, size s' ≤ S ∧ Frag.Within (mainLoop Ps Po) (withIO [] (st (wd (M.out s) ++ (wd s ++ [])) [] [] []))
      (t * (1 + (tS L + (3 * L + 3 + tO L))) + 1) (withIO [b] (st (wd s' ++ []) [] [] [])) := by
  induction h with
  | @halt s t ho hs =>
    refine ⟨s, hs, 1, by omega, ?_⟩
    rw [ho]
    exact Frag.loop_runs_exit (chkQ_some _ _ _ _ _ b)
  | @step s t ho hs hr ih =>
    obtain ⟨s', hs', n, hn, hrun⟩ := ih
    obtain ⟨m, hm, hb⟩ := within_io ((hS s [] [] [] []).seq (look_within hO (M.step s) [] [] [] [])) []
    refine ⟨s', hs', 1 + m + n, ?_, ?_⟩
    · have h1 := mS (hL s hs)
      have h2 := hL _ (size_le_of_reaches hr)
      have h3 := mO h2
      have e : (t + 1) * (1 + (tS L + (3 * L + 3 + tO L))) =
          t * (1 + (tS L + (3 * L + 3 + tO L))) + (1 + (tS L + (3 * L + 3 + tO L))) := Nat.succ_mul _ _
      omega
    · rw [ho]
      exact Frag.loop_runs_iter (chkQ_none _ _ _ _ _) hb hrun
end Groundwork.Host
