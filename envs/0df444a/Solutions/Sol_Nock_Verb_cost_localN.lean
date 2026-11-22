-- Prove2me | solution 1 for Nock.Verb.cost_localN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:27:37.436324+00:00
-- url     : https://prove2.me/submissions/1aa395ca-3942-4742-b8d6-683e097514af

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_op11_arith
public import Theorems.Thm_Nock_Verb_evalN_op_ge12_none
public import Theorems.Thm_Nock_Verb_den_terminal_val
public import Theorems.Thm_Nock_Verb_den_term_children
public import Theorems.Thm_Nock_Verb_den_term_split
public import Theorems.Thm_Nock_Verb_den_star_val
public import Theorems.Thm_Nock_Verb_den_null_val
public import Theorems.Thm_Nock_Verb_den_null_none
public import Theorems.Thm_Nock_Verb_ncost_align
public import Theorems.Thm_Nock_Verb_vcostN_star_eq
public import Theorems.Thm_Nock_Verb_vcostN_slot_eq
public import Theorems.Thm_Nock_Verb_vcostN_equal_eq
public import Theorems.Thm_Nock_Verb_vcostN_minus_eq
public import Theorems.Thm_Nock_Verb_vcostN_edit_eq
public import Theorems.Thm_Nock_Verb_vcostN_null_eq
public import Theorems.Thm_Nock_Verb_vcostN_terminal
public import Theorems.Thm_Nock_Verb_vcostN_star_terminal
public import Theorems.Thm_Nock_Verb_op6_decreaseN
public import Theorems.Thm_Nock_Verb_den_succ
public import Theorems.Thm_Nock_Verb_editOk_of_terminal
public import Theorems.Thm_Nock_Verb_isTerminal_node
public import Theorems.Thm_Nock_Verb_slot_one
public import Theorems.Thm_Nock_Verb_slot_three
public import Theorems.Thm_Nock_evalN_succ

section
@[expose] public section
namespace Nock
namespace Verb
open Noun
private theorem hint_composition_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true)
  (n2 : Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hfL : den (g + 1) L = some L.noun) (hdL : den (g + 1 + 1) L
    = some L.noun)
  (hgn2 : den g n2 = some n2.noun) (hr : (node Action.star L (node Action.null (leaf 2)
    n2)).redexHint = some rr)
  (hvv : evalN (g + 1) L.noun ((atom 2).cell n2.noun) = some x) :
  vcostN (g + 1 + 1) rr < ncost (g + 1 + 1) L.noun (node Action.null (leaf 2) n2).noun := by
  cases n2 with
  | leaf k => simp [redexHint, hintExpand, reduce, redex] at hr
  | node rn2 b c =>
      have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
      simp only [isTerminal, Bool.and_eq_true] at htn2
      obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
      simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl := Option.some.inj hr
      obtain ⟨hg1b, hg1c⟩ :=
        den_term_children (editOk_of_terminal hn2t) (den_succ hgn2) htb htc
      have hdb_f1 : den (g + 1 + 1) b = some b.noun := den_succ hg1b
      have hdc_f1 : den (g + 1 + 1) c = some c.noun := den_succ hg1c
      simp only [noun, evalN] at hvv
      cases hb : evalN g L.noun b.noun with
      | none => rw [hb] at hvv; simp at hvv
      | some sb =>
        cases hc : evalN g L.noun c.noun with
        | none => rw [hb, hc] at hvv; simp at hvv
        | some sc =>
          rw [hb, hc] at hvv
          have hb' : evalN (g + 1) L.noun b.noun = some sb := evalN_succ hb
          have hc' : evalN (g + 1) L.noun c.noun = some sc := evalN_succ hc
          have hd_Lb : den (g + 1 + 1) (Verb.node .star L b) = some sb :=
            den_star_val hfL hg1b hb'
          have hd_Lc : den (g + 1 + 1) (Verb.node .star L c) = some sc :=
            den_star_val hfL hg1c hc'
          have eq_b : ncost (g + 1 + 1) L.noun b.noun = ncost (g + 1) L.noun b.noun :=
            ncost_align hb (by omega) (by omega)
          have eq_c : ncost (g + 1 + 1) L.noun c.noun = ncost (g + 1) L.noun c.noun :=
            ncost_align hc (by omega) (by omega)
          have eq_sbsc : ncost (g + 1 + 1) sb sc = ncost (g + 1) sb sc :=
            ncost_align hvv (by omega) (by omega)
          simp only [vcostN_star_eq, hd_Lb, hd_Lc,
            vcostN_star_terminal hL htb hdL hdb_f1,
            vcostN_star_terminal hL htc hdL hdc_f1]
          simp only [noun, ncost, hb', hc']
          rw [eq_b, eq_c, eq_sbsc]
          omega
private theorem hint_conditional_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true)
  (n2 : Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hdL : den (g + 1 + 1) L = some L.noun) (hgn2 : den g n2 =
    some n2.noun)
  (hr : (node Action.star L (node Action.null (leaf 6) n2)).redexHint = some rr)
  (hvv : evalN (g + 1) L.noun ((atom 6).cell n2.noun) = some x) :
  vcostN (g + 1 + 1) rr < ncost (g + 1 + 1) L.noun (node Action.null (leaf 6) n2).noun := by
  cases n2 with
  | leaf k => simp [redexHint, hintExpand, reduce, redex] at hr
  | node rn2 b c =>
      have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
      simp only [isTerminal, Bool.and_eq_true] at htn2
      obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
      have hct : isTerminal c = true := htc
      simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl := Option.some.inj hr
      obtain ⟨hgb, hgcv⟩ :=
        den_term_children (editOk_of_terminal hn2t) hgn2 htb htc
      have hdb_f1 : den (g + 1 + 1) b = some b.noun := den_succ (den_succ hgb)
      have h4a : den (g + 1) (Verb.node .null (Verb.leaf 4) b)
          = some (Noun.cell (Noun.atom 4) b.noun) :=
        den_null_val (by simp only [den]) hgb
      have h4b : den (g + 1 + 1)
          (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))
          = some (Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 4) b.noun)) :=
        den_null_val (by simp only [den]) h4a
      have ht4 : isTerminal
          (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)) = true := by
        simp [isTerminal, Action.isNull, htb]
      have ht23 : isTerminal (Verb.node .null (Verb.leaf 2) (Verb.leaf 3)) = true := by
        simp [isTerminal, Action.isNull]
      cases c with
      | leaf ck => exfalso; simp only [noun, evalN] at hvv; simp at hvv
      | node rc thn els =>
          have hct2 : isTerminal (Verb.node rc thn els) = true := hct
          rw [isTerminal_node] at hct; simp only [Bool.and_eq_true] at hct
          obtain ⟨⟨hrc, hthn⟩, htels⟩ := hct
          exact op6_decreaseN hL hct2 hthn htels hgcv hdL h4b ht4 ht23 hvv
private theorem hint_arm_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true) (n2 :
  Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hfL : den (g + 1) L = some L.noun) (hdL : den (g + 1 + 1) L
    = some L.noun)
  (hgn2 : den g n2 = some n2.noun) (hr : (node Action.star L (node Action.null (leaf 9)
    n2)).redexHint = some rr)
  (hvv : evalN (g + 1) L.noun ((atom 9).cell n2.noun) = some x) :
  vcostN (g + 1 + 1) rr < ncost (g + 1 + 1) L.noun (node Action.null (leaf 9) n2).noun := by
  cases n2 with
  | leaf k => simp [redexHint, hintExpand, reduce, redex] at hr
  | node rn2 b c =>
      have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
      simp only [isTerminal, Bool.and_eq_true] at htn2
      obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
      have hrn2' : rn2 = Action.null := by cases rn2 <;> simp_all [Action.isNull]
      subst hrn2'
      simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl := Option.some.inj hr
      obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := by
        cases g with | zero => simp [den] at hgn2 | succ n => exact ⟨n, rfl⟩
      obtain ⟨hhb, hhc⟩ := den_term_split htb htc hgn2
      cases b with
      | node bb bc bd => simp [noun, evalN] at hvv
      | leaf ax0 =>
          simp only [noun, evalN] at hvv
          cases hcor : evalN (g' + 1) L.noun c.noun with
          | none => simp [hcor] at hvv
          | some cor =>
            simp only [hcor] at hvv
            cases harm : Noun.slot ax0 cor with
            | none => simp [harm] at hvv
            | some arm =>
              simp only [harm] at hvv
              have hg2c : den (g' + 1 + 1) c = some c.noun := den_succ (den_succ hhc)
              have hdc_f1 : den (g' + 1 + 1 + 1) c = some c.noun := den_succ hg2c
              have hcor2 : evalN (g' + 2) L.noun c.noun = some cor :=
                evalN_succ hcor
              have hd_core : den (g' + 1 + 1 + 1) (Verb.node .star L c) = some cor :=
                den_star_val hfL hg2c hcor2
              have hb0 : den g' (Verb.leaf 0) = some (Noun.atom 0) := by simp only [den]
              have hb1 : den g' (Verb.leaf 1) = some (Noun.atom 1) := by simp only [den]
              have hf0h : den (g' + 1) (Verb.node .null (Verb.leaf 0) (Verb.leaf ax0))
                  = some (Noun.cell (Noun.atom 0) (Noun.atom ax0)) := den_null_val hb0 hhb
              have hf01 : den (g' + 1) (Verb.node .null (Verb.leaf 0) (Verb.leaf 1))
                  = some (Noun.cell (Noun.atom 0) (Noun.atom 1)) := den_null_val hb0 hb1
              have hM : den (g' + 1 + 1)
                    (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 1))
                      (Verb.node .null (Verb.leaf 0) (Verb.leaf ax0)))
                  = some (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 1))
                      (Noun.cell (Noun.atom 0) (Noun.atom ax0))) := den_null_val hf01 hf0h
              have h2 : den (g' + 1 + 1) (Verb.leaf 2) = some (Noun.atom 2) := by
                simp only [den]
              have hform : den (g' + 1 + 1 + 1)
                    (Verb.node .null (Verb.leaf 2)
                      (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 1))
                        (Verb.node .null (Verb.leaf 0) (Verb.leaf ax0))))
                  = some (Noun.cell (Noun.atom 2)
                      (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 1))
                        (Noun.cell (Noun.atom 0) (Noun.atom ax0)))) := den_null_val h2 hM
              have hformT : isTerminal
                  (Verb.node .null (Verb.leaf 2)
                    (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 1))
                      (Verb.node .null (Verb.leaf 0) (Verb.leaf ax0)))) = true := by
                simp [isTerminal, Action.isNull]
              have hev01 : evalN (g' + 2) cor
                  (Noun.cell (Noun.atom 0) (Noun.atom 1)) = some cor := by
                simp only [evalN]; exact slot_one
              have hev0h : evalN (g' + 2) cor
                  (Noun.cell (Noun.atom 0) (Noun.atom ax0)) = some arm := by
                simp only [evalN]; exact harm
              have eq_c1 : ncost (g' + 1 + 1 + 1) L.noun c.noun
                  = ncost (g' + 2) L.noun c.noun := ncost_align hcor (by omega) (by omega)
              have hRHS : ncost (g' + 1 + 1 + 1) L.noun
                  (Verb.node .null (Verb.leaf 9) (Verb.node .null (Verb.leaf ax0) c)).noun
                  = 20 + ncost (g' + 2) L.noun c.noun + ncost (g' + 2) cor arm := by
                simp only [noun, ncost, hcor2, harm]
              rw [hRHS]
              simp only [vcostN_star_eq, hd_core, hform,
                vcostN_star_terminal hL htc hdL hdc_f1, vcostN_terminal _ hformT]
              simp only [ncost, hev01, hev0h]
              change 1 + 2 + 2 + ncost (g' + 2) cor arm
                  + ncost (g' + 1 + 1 + 1) L.noun c.noun + 0
                < 20 + ncost (g' + 2) L.noun c.noun + ncost (g' + 2) cor arm
              rw [eq_c1]
              omega
private theorem hint_edit_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true) (n2 :
  Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hdL : den (g + 1 + 1) L = some L.noun) (hgn2 : den g n2 =
    some n2.noun)
  (hr : (node Action.star L (node Action.null (leaf 10) n2)).redexHint = some rr)
  (hvv : evalN (g + 1) L.noun ((atom 10).cell n2.noun) = some x) :
  vcostN (g + 1 + 1) rr < ncost (g + 1 + 1) L.noun (node Action.null (leaf 10) n2).noun := by
  cases n2 with
  | leaf k => simp [redexHint, hintExpand, reduce, redex] at hr
  | node rn2 hd d =>
      cases hd with
      | leaf k => simp [redexHint, hintExpand, reduce, redex] at hr
      | node rhd axv c =>
          have hn2t : isTerminal (Verb.node rn2 (Verb.node rhd axv c) d) = true := htn2
          rw [isTerminal_node] at htn2; simp only [Bool.and_eq_true] at htn2
          obtain ⟨⟨hrn2, hthd⟩, htd⟩ := htn2
          have hhdt : isTerminal (Verb.node rhd axv c) = true := hthd
          rw [isTerminal_node] at hthd; simp only [Bool.and_eq_true] at hthd
          obtain ⟨⟨hrhd, htaxv⟩, htc⟩ := hthd
          simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl := Option.some.inj hr
          obtain ⟨hg1hd, hg1d⟩ :=
            den_term_children (editOk_of_terminal hn2t) (den_succ hgn2) hhdt htd
          obtain ⟨hg1axv, hg1c⟩ :=
            den_term_children (editOk_of_terminal hhdt) hg1hd htaxv htc
          have hdc_f1 : den (g + 1 + 1) c = some c.noun := den_succ hg1c
          have hdd_f1 : den (g + 1 + 1) d = some d.noun := den_succ hg1d
          cases axv with
          | node b0 c0 d0 => simp [noun, evalN] at hvv
          | leaf a0 =>
              simp only [noun, evalN] at hvv
              cases hnew : evalN g L.noun c.noun with
              | none => rw [hnew] at hvv; simp at hvv
              | some new =>
                cases hold : evalN g L.noun d.noun with
                | none => rw [hnew, hold] at hvv; simp at hvv
                | some old =>
                    have eq_c : ncost (g + 1 + 1) L.noun c.noun
                        = ncost (g + 1) L.noun c.noun := ncost_align hnew (by omega) (by omega)
                    have eq_d : ncost (g + 1 + 1) L.noun d.noun
                        = ncost (g + 1) L.noun d.noun := ncost_align hold (by omega) (by omega)
                    rw [vcostN_edit_eq, vcostN_null_eq,
                      vcostN_star_terminal hL htc hdL hdc_f1,
                      vcostN_star_terminal hL htd hdL hdd_f1]
                    simp only [vcostN, noun, ncost]
                    rw [eq_c, eq_d]; omega
private theorem hint_opcode_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true) (n2 :
  Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hdL : den (g + 1 + 1) L = some L.noun) (hgn2 : den g n2 =
    some n2.noun)
  (hr : (node Action.star L (node Action.null (leaf 11) n2)).redexHint = some rr)
  (hvv : evalN (g + 1) L.noun ((atom 11).cell n2.noun) = some x) :
  vcostN (g + 1 + 1) rr < ncost (g + 1 + 1) L.noun (node Action.null (leaf 11) n2).noun := by
  cases n2 with
  | leaf k =>
      simp [noun, evalN] at hvv
  | node rn2 h2 b2 =>
      have hn2t : isTerminal (Verb.node rn2 h2 b2) = true := htn2
      simp only [isTerminal, Bool.and_eq_true] at htn2
      obtain ⟨⟨hrn2, hth2⟩, htb2⟩ := htn2
      have hgb2 : den g b2 = some b2.noun :=
        (den_term_children (editOk_of_terminal hn2t) hgn2 hth2 htb2).2
      cases h2 with
      | leaf t3 =>
          -- static hint: rr = *[L body]
          have hrr : redexHint (Verb.node .star L
              (Verb.node .null (Verb.leaf 11) (Verb.node rn2 (Verb.leaf t3) b2)))
              = some (Verb.node .star L b2) := by
            simp [redexHint, hintExpand, hL, hn2t, Action.isNull]
          rw [hrr] at hr
          obtain rfl := Option.some.inj hr
          simp only [noun, evalN] at hvv
          have hd2b2 : den (g + 1 + 1) b2 = some b2.noun := den_succ (den_succ hgb2)
          have hLHS : vcostN (g + 1 + 1) (Verb.node .star L b2)
              = ncost (g + 1 + 1) L.noun b2.noun :=
            vcostN_star_terminal hL htb2 hdL hd2b2
          have hRHS : ncost (g + 1 + 1) L.noun
              (Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom t3) b2.noun))
              = 50 + ncost (g + 1) L.noun b2.noun := by simp only [ncost]
          have halign : ncost (g + 1 + 1) L.noun b2.noun = ncost (g + 1) L.noun b2.noun :=
            ncost_align hvv (by omega) (by omega)
          rw [hLHS]
          simp only [noun]
          rw [hRHS, halign]
          omega
      | node r3 t3 clue =>
          -- dynamic hint: rr = *[L (8 clue (7 [0 3] body))]
          have hh2t : isTerminal (Verb.node r3 t3 clue) = true := hth2
          simp only [isTerminal, Bool.and_eq_true] at hth2
          obtain ⟨⟨hr3, ht3⟩, htclue⟩ := hth2
          have hrr : redexHint (Verb.node .star L
              (Verb.node .null (Verb.leaf 11) (Verb.node rn2 (Verb.node r3 t3 clue) b2)))
              = some (Verb.node .star L
                  (Verb.node .null (Verb.leaf 8)
                    (Verb.node .null clue
                      (Verb.node .null (Verb.leaf 7)
                        (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 3)) b2))))) := by
            simp [redexHint, hintExpand, hL, hn2t, Action.isNull]
          rw [hrr] at hr
          obtain rfl := Option.some.inj hr
          simp only [noun, evalN] at hvv
          cases hclue : evalN g L.noun clue.noun with
          | none => rw [hclue] at hvv; simp at hvv
          | some cv =>
              rw [hclue] at hvv
              obtain ⟨g0, rfl⟩ : ∃ g0, g = g0 + 1 := by
                cases g with
                | zero => simp [evalN] at hclue
                | succ n => exact ⟨n, rfl⟩
              have hclue1 : evalN (g0 + 2) L.noun clue.noun = some cv := evalN_succ hclue
              have hslot3 : evalN (g0 + 1) (Noun.cell cv L.noun)
                  (Noun.cell (Noun.atom 0) (Noun.atom 3)) = some L.noun := by
                simp [evalN, slot_three]
              have hMt : isTerminal
                  (Verb.node .null (Verb.leaf 8)
                    (Verb.node .null clue
                      (Verb.node .null (Verb.leaf 7)
                        (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 3)) b2)))) = true
                          := by
                simp [isTerminal, Action.isNull, htclue, htb2]
              have hLHSle : vcostN (g0 + 1 + 1 + 1)
                  (Verb.node .star L
                    (Verb.node .null (Verb.leaf 8)
                      (Verb.node .null clue
                        (Verb.node .null (Verb.leaf 7)
                          (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 3)) b2)))))
                  ≤ ncost (g0 + 1 + 1 + 1) L.noun
                      (Verb.node .null (Verb.leaf 8)
                        (Verb.node .null clue
                          (Verb.node .null (Verb.leaf 7)
                            (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 3))
                              b2)))).noun := by
                rw [vcostN_star_eq, vcostN_terminal L hL, vcostN_terminal _ hMt,
                  Nat.add_zero, Nat.add_zero]
                cases hdL3 : den (g0 + 1 + 1 + 1) L with
                | none => simp
                | some sa =>
                    cases hdM : den (g0 + 1 + 1 + 1)
                        (Verb.node .null (Verb.leaf 8)
                          (Verb.node .null clue
                            (Verb.node .null (Verb.leaf 7)
                              (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 3)) b2))))
                                with
                    | none => simp
                    | some Mv =>
                        have e1 : sa = L.noun := den_terminal_val hL hdL3
                        have e2 : Mv = (Verb.node .null (Verb.leaf 8)
                            (Verb.node .null clue
                              (Verb.node .null (Verb.leaf 7)
                                (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 3))
                                  b2)))).noun :=
                          den_terminal_val hMt hdM
                        subst e1; subst e2; simp
              have hLHSval' : ncost (g0 + 1 + 1 + 1) L.noun
                  (Verb.node .null (Verb.leaf 8)
                    (Verb.node .null clue
                      (Verb.node .null (Verb.leaf 7)
                        (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 3)) b2)))).noun
                  = 4 + ncost (g0 + 2) L.noun clue.noun + ncost (g0 + 1) L.noun b2.noun := by
                simp only [noun, ncost, hclue1, hslot3]
                generalize ncost (g0 + 2) L.noun clue.noun = A
                generalize ncost (g0 + 1) L.noun b2.noun = B
                exact op11_arith A B
              have hRHS' : ncost (g0 + 1 + 1 + 1) L.noun
                  (Verb.node .null (Verb.leaf 11) (Verb.node rn2 (Verb.node r3 t3 clue) b2)).noun
                  = 50 + ncost (g0 + 2) L.noun clue.noun + ncost (g0 + 2) L.noun b2.noun := by
                simp only [noun, ncost, hclue1]
              have halign : ncost (g0 + 1) L.noun b2.noun = ncost (g0 + 2) L.noun b2.noun :=
                ncost_align hvv (by omega) (by omega)
              rw [hRHS']
              have key := hLHSval' ▸ hLHSle
              omega
private theorem hint_equality_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true) (n2
  : Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hdL : den (g + 1 + 1) L = some L.noun) (hgn2 : den g n2 =
    some n2.noun)
  (hr : (node Action.star L (node Action.null (leaf 5) n2)).redexHint = some rr)
  (hvv : evalN (g + 1) L.noun ((atom 5).cell n2.noun) = some x) :
  vcostN (g + 1 + 1) rr < ncost (g + 1 + 1) L.noun (node Action.null (leaf 5) n2).noun := by
  cases n2 with
  | leaf k => simp [redexHint, hintExpand, reduce, redex] at hr
  | node rn2 b c =>
      have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
      simp only [isTerminal, Bool.and_eq_true] at htn2
      obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
      simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl :=
        Option.some.inj hr
      obtain ⟨hg1b, hg1c⟩ :=
        den_term_children (editOk_of_terminal hn2t) (den_succ hgn2) htb htc
      have hdb_f1 : den (g + 1 + 1) b = some b.noun := den_succ hg1b
      have hdc_f1 : den (g + 1 + 1) c = some c.noun := den_succ hg1c
      simp only [noun, evalN] at hvv
      cases hb : evalN g L.noun b.noun with
      | none => rw [hb] at hvv; simp at hvv
      | some sb =>
        cases hc : evalN g L.noun c.noun with
        | none => rw [hb, hc] at hvv; simp at hvv
        | some sc =>
          have eq_b : ncost (g + 1 + 1) L.noun b.noun = ncost (g + 1) L.noun b.noun :=
            ncost_align hb (by omega) (by omega)
          have eq_c : ncost (g + 1 + 1) L.noun c.noun = ncost (g + 1) L.noun c.noun :=
            ncost_align hc (by omega) (by omega)
          rw [vcostN_equal_eq, vcostN_star_terminal hL htb hdL hdb_f1,
            vcostN_star_terminal hL htc hdL hdc_f1]
          simp only [noun, ncost]
          rw [eq_b, eq_c]; omega
private theorem hint_push_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true) (n2 :
  Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hfL : den (g + 1) L = some L.noun) (hdL : den (g + 1 + 1) L
    = some L.noun)
  (hgn2 : den g n2 = some n2.noun) (hr : (node Action.star L (node Action.null (leaf 8)
    n2)).redexHint = some rr)
  (hvv : evalN (g + 1) L.noun ((atom 8).cell n2.noun) = some x) :
  vcostN (g + 1 + 1) rr < ncost (g + 1 + 1) L.noun (node Action.null (leaf 8) n2).noun := by
  cases n2 with
  | leaf k => simp [redexHint, hintExpand, reduce, redex] at hr
  | node rn2 b c =>
      have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
      simp only [isTerminal, Bool.and_eq_true] at htn2
      obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
      simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl :=
        Option.some.inj hr
      obtain ⟨hgb, hgc⟩ :=
        den_term_children (editOk_of_terminal hn2t) hgn2 htb htc
      have hg1b : den (g + 1) b = some b.noun := den_succ hgb
      have hdb_f1 : den (g + 1 + 1) b = some b.noun := den_succ hg1b
      have hg1c : den (g + 1) c = some c.noun := den_succ hgc
      have hdc_f1 : den (g + 1 + 1) c = some c.noun := den_succ hg1c
      simp only [noun, evalN] at hvv
      cases hb : evalN g L.noun b.noun with
      | none => rw [hb] at hvv; simp at hvv
      | some sb =>
          rw [hb] at hvv
          have hb' : evalN (g + 1) L.noun b.noun = some sb := evalN_succ hb
          have eq_Lb : ncost (g + 1 + 1) L.noun b.noun = ncost (g + 1) L.noun b.noun
            :=
            ncost_align hb (by omega) (by omega)
          have eq_sbLc : ncost (g + 1 + 1) (Noun.cell sb L.noun) c.noun
              = ncost (g + 1) (Noun.cell sb L.noun) c.noun := ncost_align hvv (by
                omega) (by omega)
          have hRHS : ncost (g + 1 + 1) L.noun
              (Verb.node .null (Verb.leaf 8) (Verb.node rn2 b c)).noun
              = 1 + ncost (g + 1) L.noun b.noun
                  + ncost (g + 1) (Noun.cell sb L.noun) c.noun := by
            simp only [noun, ncost, hb']
          rw [hRHS]
          have hvcnull : vcostN (g + 1 + 1) (Verb.node .null (Verb.node .star L b) L)
              = ncost (g + 1 + 1) L.noun b.noun := by
            rw [vcostN_null_eq, vcostN_star_terminal hL htb hdL hdb_f1,
              vcostN_terminal L hL,
              Nat.add_zero]
          cases hgL : den g L with
          | none =>
              have hnone : den (g + 1) (Verb.node .star L b) = none := by
                simp only [den, hgL]
              have hsubjn : den (g + 1 + 1) (Verb.node .null (Verb.node .star L b) L)
                = none :=
                den_null_none hnone
              rw [vcostN_star_eq]
              simp only [hsubjn, hvcnull, vcostN_terminal c htc]
              rw [eq_Lb]
              omega
          | some vL =>
              have hvL : vL = L.noun := den_terminal_val hL hgL
              subst hvL
              have hd_Lb_g : den (g + 1) (Verb.node .star L b) = some sb :=
                den_star_val hgL hgb hb
              have hd_subj : den (g + 1 + 1) (Verb.node .null (Verb.node .star L b) L)
                  = some (Noun.cell sb L.noun) := den_null_val hd_Lb_g hfL
              rw [vcostN_star_eq]
              simp only [hd_subj, hdc_f1, hvcnull, vcostN_terminal c htc]
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
    (hv : den F (Verb.node .star L R) = some x)
    (hr : redexHint (Verb.node .star L R) = some rr) :
    vcostN F rr < vcostN F (Verb.node .star L R) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := by
    cases F with
    | zero => simp [den] at hv
    | succ n => exact ⟨n, rfl⟩
  have hvv := hv
  simp only [den] at hvv
  cases hfL : den f L with
  | none => rw [hfL] at hvv; simp at hvv
  | some sL =>
    cases hfR : den f R with
    | none => rw [hfL, hfR] at hvv; simp at hvv
    | some sR =>
      rw [hfL, hfR] at hvv
      have hsL : sL = L.noun := den_terminal_val hL hfL
      have hsR : sR = R.noun := den_terminal_val hR hfR
      subst hsL; subst hsR
      have hdL : den (f + 1) L = some L.noun := den_succ hfL
      have hvcL : vcostN (f + 1) L = 0 := vcostN_terminal L hL (f + 1)
      have hvcR : vcostN (f + 1) R = 0 := vcostN_terminal R hR (f + 1)
      have hstar : vcostN (f + 1) (Verb.node .star L R) = ncost (f + 1) L.noun R.noun := by
        simp only [vcostN, hdL, den_succ hfR, hvcL, hvcR, Nat.add_zero]
      rw [hstar]
      cases R with
      | leaf k => simp [redexHint, hintExpand, reduce, redex] at hr
      | node ra i n2 =>
          have hRt : isTerminal (Verb.node ra i n2) = true := hR
          simp only [isTerminal, Bool.and_eq_true] at hR
          obtain ⟨⟨hra, hti⟩, htn2⟩ := hR
          have hra0 : ra = Action.null := by cases ra <;> simp_all [Action.isNull]
          subst hra0
          obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := by
            cases f with
            | zero => simp [den] at hfR
            | succ n => exact ⟨n, rfl⟩
          obtain ⟨hgi, hgn2⟩ := den_term_split hti htn2 hfR
          have hdi_f1 : den (g + 1 + 1) i = some i.noun := den_succ (den_succ hgi)
          have hdn2_f1 : den (g + 1 + 1) n2 = some n2.noun := den_succ (den_succ hgn2)
          have hvci : vcostN (g + 1 + 1) i = 0 := vcostN_terminal i hti _
          have hvcn2 : vcostN (g + 1 + 1) n2 = 0 := vcostN_terminal n2 htn2 _
          cases i with
          | node bi ic id =>
              simp only [redexHint, hintExpand, reduce, redex] at hr
              obtain rfl := Option.some.inj hr
              simp only [noun, evalN] at hvv
              cases he1 : evalN g L.noun (Noun.cell ic.noun id.noun) with
              | none => rw [he1] at hvv; simp at hvv
              | some l' =>
                  cases he2 : evalN g L.noun n2.noun with
                  | none => rw [he1, he2] at hvv; simp at hvv
                  | some r' =>
                      have e_i : ncost (g + 1 + 1) L.noun (Noun.cell ic.noun id.noun)
                          = ncost (g + 1) L.noun (Noun.cell ic.noun id.noun) :=
                        ncost_align he1 (by omega) (by omega)
                      have e_n2 : ncost (g + 1 + 1) L.noun n2.noun = ncost (g + 1) L.noun n2.noun :=
                        ncost_align he2 (by omega) (by omega)
                      rw [vcostN_null_eq,
                        vcostN_star_terminal hL hti hdL hdi_f1,
                        vcostN_star_terminal hL htn2 hdL hdn2_f1]
                      simp only [noun, ncost]
                      rw [e_i, e_n2]
                      omega
          | leaf op =>
              have hop : op < 12 := by
                rcases Nat.lt_or_ge op 12 with h | h
                · exact h
                · exfalso
                  simp only [noun] at hvv
                  rw [evalN_op_ge12_none (g + 1) L.noun n2.noun op h] at hvv
                  simp at hvv
              simp only [noun] at hvv
              interval_cases op
              · -- OP0
                simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl :=
                  Option.some.inj hr
                rw [vcostN_slot_eq, vcostN_terminal n2 htn2, vcostN_terminal L hL]
                simp only [noun, ncost]; omega
              · -- OP1
                simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl :=
                  Option.some.inj hr
                rw [vcostN_terminal n2 htn2]
                simp only [noun, ncost]; omega
              · -- OP2
                exact hint_composition_cost_decrease hL n2 htn2 g hfL hdL hgn2 hr hvv
              · -- OP3
                simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl :=
                  Option.some.inj hr
                simp only [evalN, Option.map_eq_some_iff] at hvv
                obtain ⟨y, hy, _⟩ := hvv
                have e_n2 : ncost (g + 1 + 1) L.noun n2.noun = ncost (g + 1) L.noun n2.noun :=
                  ncost_align hy (by omega) (by omega)
                rw [vcostN_minus_eq, vcostN_star_terminal hL htn2 hdL hdn2_f1]
                simp only [vcostN, noun, ncost]
                rw [e_n2]; omega
              · -- OP4
                simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl :=
                  Option.some.inj hr
                simp only [evalN, Option.bind_eq_some_iff] at hvv
                obtain ⟨y, hy, _⟩ := hvv
                have e_n2 : ncost (g + 1 + 1) L.noun n2.noun = ncost (g + 1) L.noun n2.noun :=
                  ncost_align hy (by omega) (by omega)
                rw [vcostN_minus_eq, vcostN_star_terminal hL htn2 hdL hdn2_f1]
                simp only [vcostN, noun, ncost]
                rw [e_n2]; omega
              · -- OP5
                exact hint_equality_cost_decrease hL n2 htn2 g hdL hgn2 hr hvv
              · -- OP6
                exact hint_conditional_cost_decrease hL n2 htn2 g hdL hgn2 hr hvv
              · -- OP7
                cases n2 with
                | leaf k => simp [redexHint, hintExpand, reduce, redex] at hr
                | node rn2 b c =>
                    have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
                    simp only [isTerminal, Bool.and_eq_true] at htn2
                    obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
                    simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl :=
                      Option.some.inj hr
                    obtain ⟨hg1b, hg1c⟩ :=
                      den_term_children (editOk_of_terminal hn2t) (den_succ hgn2) htb htc
                    have hdb_f1 : den (g + 1 + 1) b = some b.noun := den_succ hg1b
                    have hdc_f1 : den (g + 1 + 1) c = some c.noun := den_succ hg1c
                    simp only [noun, evalN] at hvv
                    cases hb : evalN g L.noun b.noun with
                    | none => rw [hb] at hvv; simp at hvv
                    | some sb =>
                        rw [hb] at hvv
                        have hb' : evalN (g + 1) L.noun b.noun = some sb := evalN_succ hb
                        have hd_Lb : den (g + 1 + 1) (Verb.node .star L b) = some sb :=
                          den_star_val hfL hg1b hb'
                        have eq_b : ncost (g + 1 + 1) L.noun b.noun = ncost (g + 1) L.noun b.noun :=
                          ncost_align hb (by omega) (by omega)
                        have eq_sbc : ncost (g + 1 + 1) sb c.noun = ncost (g + 1) sb c.noun :=
                          ncost_align hvv (by omega) (by omega)
                        simp only [vcostN_star_eq, hd_Lb, hdc_f1,
                          vcostN_star_terminal hL htb hdL hdb_f1, vcostN_terminal c htc]
                        simp only [noun, ncost, hb']
                        rw [eq_b, eq_sbc]; omega
              · -- OP8
                exact hint_push_cost_decrease hL n2 htn2 g hfL hdL hgn2 hr hvv
              · -- OP9
                exact hint_arm_cost_decrease hL n2 htn2 g hfL hdL hgn2 hr hvv
              · -- OP10
                exact hint_edit_cost_decrease hL n2 htn2 g hdL hgn2 hr hvv
              · -- OP11 (hint expansion)
                exact hint_opcode_cost_decrease hL n2 htn2 g hdL hgn2 hr hvv
end Nock.Verb
