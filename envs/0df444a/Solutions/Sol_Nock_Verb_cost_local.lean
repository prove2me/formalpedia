-- Prove2me | solution 1 for Nock.Verb.cost_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:25:54.123665+00:00
-- url     : https://prove2.me/submissions/0f801a00-833a-4e59-8691-ad2af89fc9f3

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_isTerminal_node
public import Theorems.Thm_Nock_Verb_denP_terminal_val
public import Theorems.Thm_Nock_Verb_denP_term_children
public import Theorems.Thm_Nock_Verb_denP_term_split
public import Theorems.Thm_Nock_Verb_denP_star_val
public import Theorems.Thm_Nock_Verb_denP_null_val
public import Theorems.Thm_Nock_Verb_denP_null_none
public import Theorems.Thm_Nock_Verb_pcost_align
public import Theorems.Thm_Nock_Verb_vcost_star_eq
public import Theorems.Thm_Nock_Verb_vcost_slot_eq
public import Theorems.Thm_Nock_Verb_vcost_equal_eq
public import Theorems.Thm_Nock_Verb_vcost_minus_eq
public import Theorems.Thm_Nock_Verb_vcost_edit_eq
public import Theorems.Thm_Nock_Verb_vcost_null_eq
public import Theorems.Thm_Nock_Verb_vcost_star_terminal
public import Theorems.Thm_Nock_Verb_op6_decrease
public import Theorems.Thm_Nock_Verb_denP_succ
public import Theorems.Thm_Nock_Verb_editOk_of_terminal
public import Theorems.Thm_Nock_Verb_evalPaper_op_ge11
public import Theorems.Thm_Nock_Verb_slot_one
public import Theorems.Thm_Nock_Verb_vcost_terminal
public import Theorems.Thm_Nock_evalPaper_succ

section
@[expose] public section
namespace Nock
namespace Verb
open Noun
private theorem paper_composition_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true)
  (n2 : Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hfL : denP (g + 1) L = some L.noun) (hdL : denP (g + 1 + 1)
    L = some L.noun)
  (hgn2 : denP g n2 = some n2.noun) (hr : (node Action.star L (node Action.null (leaf 2) n2)).redex
    = some rr)
  (hvv : evalPaper (g + 1) L.noun ((atom 2).cell n2.noun) = some x) :
  vcost (g + 1 + 1) rr < pcost (g + 1 + 1) L.noun (node Action.null (leaf 2) n2).noun := by
  cases n2 with
  | leaf k => simp [redex] at hr
  | node rn2 b c =>
      have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
      simp only [isTerminal, Bool.and_eq_true] at htn2
      obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
      simp only [redex] at hr; obtain rfl := Option.some.inj hr
      obtain ⟨hg1b, hg1c⟩ :=
        denP_term_children (editOk_of_terminal hn2t) (denP_succ hgn2) htb htc
      have hdb_f1 : denP (g + 1 + 1) b = some b.noun := denP_succ hg1b
      have hdc_f1 : denP (g + 1 + 1) c = some c.noun := denP_succ hg1c
      simp only [noun, evalPaper] at hvv
      cases hb : evalPaper g L.noun b.noun with
      | none => rw [hb] at hvv; simp at hvv
      | some sb =>
        cases hc : evalPaper g L.noun c.noun with
        | none => rw [hb, hc] at hvv; simp at hvv
        | some sc =>
          rw [hb, hc] at hvv
          have hb' : evalPaper (g + 1) L.noun b.noun = some sb := evalPaper_succ hb
          have hc' : evalPaper (g + 1) L.noun c.noun = some sc := evalPaper_succ hc
          have hd_Lb : denP (g + 1 + 1) (Verb.node .star L b) = some sb :=
            denP_star_val hfL hg1b hb'
          have hd_Lc : denP (g + 1 + 1) (Verb.node .star L c) = some sc :=
            denP_star_val hfL hg1c hc'
          have eq_b : pcost (g + 1 + 1) L.noun b.noun = pcost (g + 1) L.noun b.noun :=
            pcost_align hb (by omega) (by omega)
          have eq_c : pcost (g + 1 + 1) L.noun c.noun = pcost (g + 1) L.noun c.noun :=
            pcost_align hc (by omega) (by omega)
          have eq_sbsc : pcost (g + 1 + 1) sb sc = pcost (g + 1) sb sc :=
            pcost_align hvv (by omega) (by omega)
          simp only [vcost_star_eq, hd_Lb, hd_Lc,
            vcost_star_terminal hL htb hdL hdb_f1,
            vcost_star_terminal hL htc hdL hdc_f1]
          simp only [noun, pcost, hb', hc']
          rw [eq_b, eq_c, eq_sbsc]
          omega
private theorem paper_conditional_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true)
  (n2 : Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hdL : denP (g + 1 + 1) L = some L.noun) (hgn2 : denP g n2 =
    some n2.noun)
  (hr : (node Action.star L (node Action.null (leaf 6) n2)).redex = some rr)
  (hvv : evalPaper (g + 1) L.noun ((atom 6).cell n2.noun) = some x) :
  vcost (g + 1 + 1) rr < pcost (g + 1 + 1) L.noun (node Action.null (leaf 6) n2).noun := by
  cases n2 with
  | leaf k => simp [redex] at hr
  | node rn2 b c =>
      have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
      simp only [isTerminal, Bool.and_eq_true] at htn2
      obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
      have hct : isTerminal c = true := htc
      simp only [redex] at hr; obtain rfl := Option.some.inj hr
      obtain ⟨hgb, hgcv⟩ :=
        denP_term_children (editOk_of_terminal hn2t) hgn2 htb htc
      have hdb_f1 : denP (g + 1 + 1) b = some b.noun := denP_succ (denP_succ hgb)
      -- denP F of the terminal `[4 [4 b]]` cell
      have h4a : denP (g + 1) (Verb.node .null (Verb.leaf 4) b)
          = some (Noun.cell (Noun.atom 4) b.noun) :=
        denP_null_val (by simp only [denP]) hgb
      have h4b : denP (g + 1 + 1)
          (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))
          = some (Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 4) b.noun)) :=
        denP_null_val (by simp only [denP]) h4a
      have ht4 : isTerminal
          (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)) = true := by
        simp [isTerminal, Action.isNull, htb]
      have ht23 : isTerminal (Verb.node .null (Verb.leaf 2) (Verb.leaf 3)) = true := by
        simp [isTerminal, Action.isNull]
      -- c must be a cell for op6 to fire
      cases c with
      | leaf ck => exfalso; simp only [noun, evalPaper] at hvv; simp at hvv
      | node rc thn els =>
          have hct2 : isTerminal (Verb.node rc thn els) = true := hct
          rw [isTerminal_node] at hct; simp only [Bool.and_eq_true] at hct
          obtain ⟨⟨hrc, hthn⟩, htels⟩ := hct
          exact op6_decrease hL hct2 hthn htels hgcv hdL h4b ht4 ht23 hvv
private theorem paper_arm_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true) (n2 :
  Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hfL : denP (g + 1) L = some L.noun) (hdL : denP (g + 1 + 1)
    L = some L.noun)
  (hgn2 : denP g n2 = some n2.noun) (hr : (node Action.star L (node Action.null (leaf 9) n2)).redex
    = some rr)
  (hvv : evalPaper (g + 1) L.noun ((atom 9).cell n2.noun) = some x) :
  vcost (g + 1 + 1) rr < pcost (g + 1 + 1) L.noun (node Action.null (leaf 9) n2).noun := by
  cases n2 with
  | leaf k => simp [redex] at hr
  | node rn2 b c =>
      have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
      simp only [isTerminal, Bool.and_eq_true] at htn2
      obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
      have hrn2' : rn2 = Action.null := by cases rn2 <;> simp_all [Action.isNull]
      subst hrn2'
      simp only [redex] at hr; obtain rfl := Option.some.inj hr
      obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := by
        cases g with | zero => simp [denP] at hgn2 | succ n => exact ⟨n, rfl⟩
      obtain ⟨hhb, hhc⟩ := denP_term_split htb htc hgn2
      cases b with
      | node bb bc bd => simp [noun, evalPaper] at hvv
      | leaf ax0 =>
          simp only [noun, evalPaper] at hvv
          cases hcor : evalPaper (g' + 1) L.noun c.noun with
          | none => simp [hcor] at hvv
          | some cor =>
            simp only [hcor] at hvv
            cases harm : Noun.slot ax0 cor with
            | none => simp [harm] at hvv
            | some arm =>
              simp only [harm] at hvv
              have hg2c : denP (g' + 1 + 1) c = some c.noun := denP_succ (denP_succ hhc)
              have hdc_f1 : denP (g' + 1 + 1 + 1) c = some c.noun := denP_succ hg2c
              have hcor2 : evalPaper (g' + 2) L.noun c.noun = some cor :=
                evalPaper_succ hcor
              have hd_core : denP (g' + 1 + 1 + 1) (Verb.node .star L c) = some cor :=
                denP_star_val hfL hg2c hcor2
              have hb0 : denP g' (Verb.leaf 0) = some (Noun.atom 0) := by simp only [denP]
              have hb1 : denP g' (Verb.leaf 1) = some (Noun.atom 1) := by simp only [denP]
              have hf0h : denP (g' + 1) (Verb.node .null (Verb.leaf 0) (Verb.leaf ax0))
                  = some (Noun.cell (Noun.atom 0) (Noun.atom ax0)) := denP_null_val hb0 hhb
              have hf01 : denP (g' + 1) (Verb.node .null (Verb.leaf 0) (Verb.leaf 1))
                  = some (Noun.cell (Noun.atom 0) (Noun.atom 1)) := denP_null_val hb0 hb1
              have hM : denP (g' + 1 + 1)
                    (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 1))
                      (Verb.node .null (Verb.leaf 0) (Verb.leaf ax0)))
                  = some (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 1))
                      (Noun.cell (Noun.atom 0) (Noun.atom ax0))) := denP_null_val hf01 hf0h
              have h2 : denP (g' + 1 + 1) (Verb.leaf 2) = some (Noun.atom 2) := by
                simp only [denP]
              have hform : denP (g' + 1 + 1 + 1)
                    (Verb.node .null (Verb.leaf 2)
                      (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 1))
                        (Verb.node .null (Verb.leaf 0) (Verb.leaf ax0))))
                  = some (Noun.cell (Noun.atom 2)
                      (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 1))
                        (Noun.cell (Noun.atom 0) (Noun.atom ax0)))) := denP_null_val h2 hM
              have hformT : isTerminal
                  (Verb.node .null (Verb.leaf 2)
                    (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 1))
                      (Verb.node .null (Verb.leaf 0) (Verb.leaf ax0)))) = true := by
                simp [isTerminal, Action.isNull]
              have hev01 : evalPaper (g' + 2) cor
                  (Noun.cell (Noun.atom 0) (Noun.atom 1)) = some cor := by
                simp only [evalPaper]; exact slot_one
              have hev0h : evalPaper (g' + 2) cor
                  (Noun.cell (Noun.atom 0) (Noun.atom ax0)) = some arm := by
                simp only [evalPaper]; exact harm
              have eq_c1 : pcost (g' + 1 + 1 + 1) L.noun c.noun
                  = pcost (g' + 2) L.noun c.noun := pcost_align hcor (by omega) (by omega)
              have eq_c2 : pcost (g' + 3) L.noun c.noun
                  = pcost (g' + 2) L.noun c.noun := pcost_align hcor (by omega) (by omega)
              have hRHS : pcost (g' + 1 + 1 + 1) L.noun
                  (Verb.node .null (Verb.leaf 9) (Verb.node .null (Verb.leaf ax0) c)).noun
                  = 20 + pcost (g' + 2) L.noun c.noun + pcost (g' + 2) cor arm := by
                simp only [noun, pcost, hcor2, harm]
              rw [hRHS]
              simp only [vcost_star_eq, hd_core, hform,
                vcost_star_terminal hL htc hdL hdc_f1, vcost_terminal _ hformT]
              simp only [pcost, hev01, hev0h]
              change 1 + 2 + 2 + pcost (g' + 2) cor arm
                  + pcost (g' + 1 + 1 + 1) L.noun c.noun + 0
                < 20 + pcost (g' + 2) L.noun c.noun + pcost (g' + 2) cor arm
              rw [eq_c1]
              omega
private theorem paper_edit_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true) (n2 :
  Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hdL : denP (g + 1 + 1) L = some L.noun) (hgn2 : denP g n2 =
    some n2.noun)
  (hr : (node Action.star L (node Action.null (leaf 10) n2)).redex = some rr)
  (hvv : evalPaper (g + 1) L.noun ((atom 10).cell n2.noun) = some x) :
  vcost (g + 1 + 1) rr < pcost (g + 1 + 1) L.noun (node Action.null (leaf 10) n2).noun := by
  cases n2 with
  | leaf k => simp [redex] at hr
  | node rn2 hd d =>
      cases hd with
      | leaf k => simp [redex] at hr
      | node rhd axv c =>
          have hn2t : isTerminal (Verb.node rn2 (Verb.node rhd axv c) d) = true := htn2
          rw [isTerminal_node] at htn2; simp only [Bool.and_eq_true] at htn2
          obtain ⟨⟨hrn2, hthd⟩, htd⟩ := htn2
          have hhdt : isTerminal (Verb.node rhd axv c) = true := hthd
          rw [isTerminal_node] at hthd; simp only [Bool.and_eq_true] at hthd
          obtain ⟨⟨hrhd, htaxv⟩, htc⟩ := hthd
          simp only [redex] at hr; obtain rfl := Option.some.inj hr
          obtain ⟨hg1hd, hg1d⟩ :=
            denP_term_children (editOk_of_terminal hn2t) (denP_succ hgn2) hhdt htd
          obtain ⟨hg1axv, hg1c⟩ :=
            denP_term_children (editOk_of_terminal hhdt) hg1hd htaxv htc
          have hdc_f1 : denP (g + 1 + 1) c = some c.noun := denP_succ hg1c
          have hdd_f1 : denP (g + 1 + 1) d = some d.noun := denP_succ hg1d
          cases axv with
          | node b0 c0 d0 => simp [noun, evalPaper] at hvv
          | leaf a0 =>
              simp only [noun, evalPaper] at hvv
              cases hnew : evalPaper g L.noun c.noun with
              | none => rw [hnew] at hvv; simp at hvv
              | some new =>
                cases hold : evalPaper g L.noun d.noun with
                | none => rw [hnew, hold] at hvv; simp at hvv
                | some old =>
                    have eq_c : pcost (g + 1 + 1) L.noun c.noun
                        = pcost (g + 1) L.noun c.noun := pcost_align hnew (by omega) (by omega)
                    have eq_d : pcost (g + 1 + 1) L.noun d.noun
                        = pcost (g + 1) L.noun d.noun := pcost_align hold (by omega) (by omega)
                    rw [vcost_edit_eq, vcost_null_eq,
                      vcost_star_terminal hL htc hdL hdc_f1,
                      vcost_star_terminal hL htd hdL hdd_f1]
                    simp only [vcost, noun, pcost]
                    rw [eq_c, eq_d]; omega
private theorem paper_equality_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true) (n2
  : Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hdL : denP (g + 1 + 1) L = some L.noun) (hgn2 : denP g n2 =
    some n2.noun)
  (hr : (node Action.star L (node Action.null (leaf 5) n2)).redex = some rr)
  (hvv : evalPaper (g + 1) L.noun ((atom 5).cell n2.noun) = some x) :
  vcost (g + 1 + 1) rr < pcost (g + 1 + 1) L.noun (node Action.null (leaf 5) n2).noun := by
  cases n2 with
  | leaf k => simp [redex] at hr
  | node rn2 b c =>
      have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
      simp only [isTerminal, Bool.and_eq_true] at htn2
      obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
      simp only [redex] at hr; obtain rfl := Option.some.inj hr
      obtain ⟨hg1b, hg1c⟩ :=
        denP_term_children (editOk_of_terminal hn2t) (denP_succ hgn2) htb htc
      have hdb_f1 : denP (g + 1 + 1) b = some b.noun := denP_succ hg1b
      have hdc_f1 : denP (g + 1 + 1) c = some c.noun := denP_succ hg1c
      simp only [noun, evalPaper] at hvv
      cases hb : evalPaper g L.noun b.noun with
      | none => rw [hb] at hvv; simp at hvv
      | some sb =>
        cases hc : evalPaper g L.noun c.noun with
        | none => rw [hb, hc] at hvv; simp at hvv
        | some sc =>
          have eq_b : pcost (g + 1 + 1) L.noun b.noun = pcost (g + 1) L.noun b.noun :=
            pcost_align hb (by omega) (by omega)
          have eq_c : pcost (g + 1 + 1) L.noun c.noun = pcost (g + 1) L.noun c.noun :=
            pcost_align hc (by omega) (by omega)
          rw [vcost_equal_eq, vcost_star_terminal hL htb hdL hdb_f1,
            vcost_star_terminal hL htc hdL hdc_f1]
          simp only [noun, pcost]
          rw [eq_b, eq_c]; omega
private theorem paper_push_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true) (n2 :
  Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hfL : denP (g + 1) L = some L.noun) (hdL : denP (g + 1 + 1)
    L = some L.noun)
  (hgn2 : denP g n2 = some n2.noun) (hr : (node Action.star L (node Action.null (leaf 8) n2)).redex
    = some rr)
  (hvv : evalPaper (g + 1) L.noun ((atom 8).cell n2.noun) = some x) :
  vcost (g + 1 + 1) rr < pcost (g + 1 + 1) L.noun (node Action.null (leaf 8) n2).noun := by
  cases n2 with
  | leaf k => simp [redex] at hr
  | node rn2 b c =>
      have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
      simp only [isTerminal, Bool.and_eq_true] at htn2
      obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
      simp only [redex] at hr; obtain rfl := Option.some.inj hr
      obtain ⟨hgb, hgc⟩ :=
        denP_term_children (editOk_of_terminal hn2t) hgn2 htb htc
      have hg1b : denP (g + 1) b = some b.noun := denP_succ hgb
      have hdb_f1 : denP (g + 1 + 1) b = some b.noun := denP_succ hg1b
      have hg1c : denP (g + 1) c = some c.noun := denP_succ hgc
      have hdc_f1 : denP (g + 1 + 1) c = some c.noun := denP_succ hg1c
      simp only [noun, evalPaper] at hvv
      cases hb : evalPaper g L.noun b.noun with
      | none => rw [hb] at hvv; simp at hvv
      | some sb =>
          rw [hb] at hvv
          have hb' : evalPaper (g + 1) L.noun b.noun = some sb := evalPaper_succ hb
          have eq_Lb : pcost (g + 1 + 1) L.noun b.noun = pcost (g + 1) L.noun b.noun
            :=
            pcost_align hb (by omega) (by omega)
          have eq_sbLc : pcost (g + 1 + 1) (Noun.cell sb L.noun) c.noun
              = pcost (g + 1) (Noun.cell sb L.noun) c.noun := pcost_align hvv (by
                omega) (by omega)
          have hRHS : pcost (g + 1 + 1) L.noun
              (Verb.node .null (Verb.leaf 8) (Verb.node rn2 b c)).noun
              = 1 + pcost (g + 1) L.noun b.noun
                  + pcost (g + 1) (Noun.cell sb L.noun) c.noun := by
            simp only [noun, pcost, hb']
          rw [hRHS]
          have hvcnull : vcost (g + 1 + 1) (Verb.node .null (Verb.node .star L b) L)
              = pcost (g + 1 + 1) L.noun b.noun := by
            rw [vcost_null_eq, vcost_star_terminal hL htb hdL hdb_f1, vcost_terminal L
              hL,
              Nat.add_zero]
          cases hgL : denP g L with
          | none =>
              have hnone : denP (g + 1) (Verb.node .star L b) = none := by
                simp only [denP, hgL]
              have hsubjn : denP (g + 1 + 1) (Verb.node .null (Verb.node .star L b) L)
                = none :=
                denP_null_none hnone
              rw [vcost_star_eq]
              simp only [hsubjn, hvcnull, vcost_terminal c htc]
              rw [eq_Lb]
              omega
          | some vL =>
              have hvL : vL = L.noun := denP_terminal_val hL hgL
              subst hvL
              have hd_Lb_g : denP (g + 1) (Verb.node .star L b) = some sb :=
                denP_star_val hgL hgb hb
              have hd_subj : denP (g + 1 + 1) (Verb.node .null (Verb.node .star L b)
                L)
                  = some (Noun.cell sb L.noun) := denP_null_val hd_Lb_g hfL
              rw [vcost_star_eq]
              simp only [hd_subj, hdc_f1, hvcnull, vcost_terminal c htc]
              rw [eq_Lb, eq_sbLc]
              omega
end Verb
end Nock
end
end

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {F : Nat} {L R rr : Verb} {x : Noun}
    (hL : isTerminal L = true) (hR : isTerminal R = true)
    (hv : denP F (Verb.node .star L R) = some x)
    (hr : reduce (Verb.node .star L R) = some rr) :
    vcost F rr < vcost F (Verb.node .star L R) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := by
    cases F with
    | zero => simp [denP] at hv
    | succ n => exact ⟨n, rfl⟩
  have hvv := hv
  simp only [denP] at hvv
  cases hfL : denP f L with
  | none => rw [hfL] at hvv; simp at hvv
  | some sL =>
    cases hfR : denP f R with
    | none => rw [hfL, hfR] at hvv; simp at hvv
    | some sR =>
      rw [hfL, hfR] at hvv
      have hsL : sL = L.noun := denP_terminal_val hL hfL
      have hsR : sR = R.noun := denP_terminal_val hR hfR
      subst hsL; subst hsR
      have hdL : denP (f + 1) L = some L.noun := denP_succ hfL
      have hvcL : vcost (f + 1) L = 0 := vcost_terminal L hL (f + 1)
      have hvcR : vcost (f + 1) R = 0 := vcost_terminal R hR (f + 1)
      have hstar : vcost (f + 1) (Verb.node .star L R) = pcost (f + 1) L.noun R.noun := by
        simp only [vcost, hdL, denP_succ hfR, hvcL, hvcR, Nat.add_zero]
      rw [hstar]
      cases R with
      | leaf k => simp [reduce, redex] at hr
      | node ra i n2 =>
          have hRt : isTerminal (Verb.node ra i n2) = true := hR
          simp only [isTerminal, Bool.and_eq_true] at hR
          obtain ⟨⟨hra, hti⟩, htn2⟩ := hR
          have hra0 : ra = Action.null := by cases ra <;> simp_all [Action.isNull]
          subst hra0
          obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := by
            cases f with
            | zero => simp [denP] at hfR
            | succ n => exact ⟨n, rfl⟩
          obtain ⟨hgi, hgn2⟩ := denP_term_split hti htn2 hfR
          rw [reduce] at hr
          have hdi_f1 : denP (g + 1 + 1) i = some i.noun := denP_succ (denP_succ hgi)
          have hdn2_f1 : denP (g + 1 + 1) n2 = some n2.noun := denP_succ (denP_succ hgn2)
          have hvci : vcost (g + 1 + 1) i = 0 := vcost_terminal i hti _
          have hvcn2 : vcost (g + 1 + 1) n2 = 0 := vcost_terminal n2 htn2 _
          cases i with
          | node bi ic id =>
              simp only [redex] at hr
              obtain rfl := Option.some.inj hr
              simp only [noun, evalPaper] at hvv
              cases he1 : evalPaper g L.noun (Noun.cell ic.noun id.noun) with
              | none => rw [he1] at hvv; simp at hvv
              | some l' =>
                  cases he2 : evalPaper g L.noun n2.noun with
                  | none => rw [he1, he2] at hvv; simp at hvv
                  | some r' =>
                      have e_i : pcost (g + 1 + 1) L.noun (Noun.cell ic.noun id.noun)
                          = pcost (g + 1) L.noun (Noun.cell ic.noun id.noun) :=
                        pcost_align he1 (by omega) (by omega)
                      have e_n2 : pcost (g + 1 + 1) L.noun n2.noun = pcost (g + 1) L.noun n2.noun :=
                        pcost_align he2 (by omega) (by omega)
                      rw [vcost_null_eq,
                        vcost_star_terminal hL hti hdL hdi_f1,
                        vcost_star_terminal hL htn2 hdL hdn2_f1]
                      simp only [noun, pcost]
                      rw [e_i, e_n2]
                      omega
          | leaf op =>
              have hop : op < 11 := by
                rcases Nat.lt_or_ge op 11 with h | h
                · exact h
                · exfalso
                  simp only [noun] at hvv
                  rw [evalPaper_op_ge11 (g + 1) L.noun n2.noun op h] at hvv
                  simp at hvv
              simp only [noun] at hvv
              interval_cases op
              · -- OP0
                simp only [redex] at hr; obtain rfl := Option.some.inj hr
                rw [vcost_slot_eq, vcost_terminal n2 htn2, vcost_terminal L hL]
                simp only [noun, pcost]; omega
              · -- OP1
                simp only [redex] at hr; obtain rfl := Option.some.inj hr
                rw [vcost_terminal n2 htn2]
                simp only [noun, pcost]; omega
              · -- OP2
                exact paper_composition_cost_decrease hL n2 htn2 g hfL hdL hgn2 hr hvv
              · -- OP3
                simp only [redex] at hr; obtain rfl := Option.some.inj hr
                simp only [evalPaper, Option.map_eq_some_iff] at hvv
                obtain ⟨y, hy, _⟩ := hvv
                have e_n2 : pcost (g + 1 + 1) L.noun n2.noun = pcost (g + 1) L.noun n2.noun :=
                  pcost_align hy (by omega) (by omega)
                rw [vcost_minus_eq, vcost_star_terminal hL htn2 hdL hdn2_f1]
                simp only [vcost, noun, pcost]
                rw [e_n2]; omega
              · -- OP4
                simp only [redex] at hr; obtain rfl := Option.some.inj hr
                simp only [evalPaper, Option.bind_eq_some_iff] at hvv
                obtain ⟨y, hy, _⟩ := hvv
                have e_n2 : pcost (g + 1 + 1) L.noun n2.noun = pcost (g + 1) L.noun n2.noun :=
                  pcost_align hy (by omega) (by omega)
                rw [vcost_minus_eq, vcost_star_terminal hL htn2 hdL hdn2_f1]
                simp only [vcost, noun, pcost]
                rw [e_n2]; omega
              · -- OP5
                exact paper_equality_cost_decrease hL n2 htn2 g hdL hgn2 hr hvv
              · -- OP6
                exact paper_conditional_cost_decrease hL n2 htn2 g hdL hgn2 hr hvv
              · -- OP7
                cases n2 with
                | leaf k => simp [redex] at hr
                | node rn2 b c =>
                    have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
                    simp only [isTerminal, Bool.and_eq_true] at htn2
                    obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
                    simp only [redex] at hr; obtain rfl := Option.some.inj hr
                    obtain ⟨hg1b, hg1c⟩ :=
                      denP_term_children (editOk_of_terminal hn2t) (denP_succ hgn2) htb htc
                    have hdb_f1 : denP (g + 1 + 1) b = some b.noun := denP_succ hg1b
                    have hdc_f1 : denP (g + 1 + 1) c = some c.noun := denP_succ hg1c
                    simp only [noun, evalPaper] at hvv
                    cases hb : evalPaper g L.noun b.noun with
                    | none => rw [hb] at hvv; simp at hvv
                    | some sb =>
                        rw [hb] at hvv
                        have hb' : evalPaper (g + 1) L.noun b.noun = some sb := evalPaper_succ hb
                        have hd_Lb : denP (g + 1 + 1) (Verb.node .star L b) = some sb :=
                          denP_star_val hfL hg1b hb'
                        have eq_b : pcost (g + 1 + 1) L.noun b.noun = pcost (g + 1) L.noun b.noun :=
                          pcost_align hb (by omega) (by omega)
                        have eq_sbc : pcost (g + 1 + 1) sb c.noun = pcost (g + 1) sb c.noun :=
                          pcost_align hvv (by omega) (by omega)
                        simp only [vcost_star_eq, hd_Lb, hdc_f1,
                          vcost_star_terminal hL htb hdL hdb_f1, vcost_terminal c htc]
                        simp only [noun, pcost, hb']
                        rw [eq_b, eq_sbc]; omega
              · -- OP8
                exact paper_push_cost_decrease hL n2 htn2 g hfL hdL hgn2 hr hvv
              · -- OP9
                exact paper_arm_cost_decrease hL n2 htn2 g hfL hdL hgn2 hr hvv
              · -- OP10
                exact paper_edit_cost_decrease hL n2 htn2 g hdL hgn2 hr hvv
end Nock.Verb
