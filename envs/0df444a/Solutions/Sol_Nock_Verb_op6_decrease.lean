-- Prove2me | solution 1 for Nock.Verb.op6_decrease
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:45.296451+00:00
-- url     : https://prove2.me/submissions/480c3b8e-19ec-4731-884c-f641bb1ba2df

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_denP_null_val
public import Theorems.Thm_Nock_Verb_pcost_align
public import Theorems.Thm_Nock_Verb_vcost_star_eq
public import Theorems.Thm_Nock_Verb_vcost_null_eq
public import Theorems.Thm_Nock_Verb_EvP_det
public import Theorems.Thm_Nock_Verb_denP_null_leaf0
public import Theorems.Thm_Nock_Verb_DenP_leaf
public import Theorems.Thm_Nock_Verb_DenP_null
public import Theorems.Thm_Nock_Verb_DenP_star
public import Theorems.Thm_Nock_Verb_DenP_terminal_iff
public import Theorems.Thm_Nock_Verb_EvP_op0
public import Theorems.Thm_Nock_Verb_EvP_op4
public import Theorems.Thm_Nock_Verb_denP_succ
public import Theorems.Thm_Nock_Verb_lus_atom
public import Theorems.Thm_Nock_Verb_slot_three
public import Theorems.Thm_Nock_Verb_slot_two
public import Theorems.Thm_Nock_Verb_vcost_terminal
public import Theorems.Thm_Nock_evalPaper_succ


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {g : Nat} {L b thn els : Verb} {x : Noun} {rn2 rc : Action}
    (hL : isTerminal L = true) (htc : isTerminal (Verb.node rc thn els) = true)
    (hthn : isTerminal thn = true) (htels : isTerminal els = true)
    (hgc : denP g (Verb.node rc thn els) = some (Verb.node rc thn els).noun)
    (hdL : denP (g + 1 + 1) L = some L.noun)
    (h4b : denP (g + 1 + 1) (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))
        = some (Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 4) b.noun)))
    (ht4 : isTerminal (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)) = true)
    (ht23 : isTerminal (Verb.node .null (Verb.leaf 2) (Verb.leaf 3)) = true)
    (hvv : evalPaper (g + 1) L.noun
        (Noun.cell (Noun.atom 6) (Verb.node rn2 b (Verb.node rc thn els)).noun) = some x) :
    vcost (g + 1 + 1)
        (Verb.node .star L
          (Verb.node .star (Verb.node rc thn els)
            (Verb.node .null (Verb.leaf 0)
              (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                (Verb.node .null (Verb.leaf 0)
                  (Verb.node .star L
                    (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))))))
      < pcost (g + 1 + 1) L.noun
          (Verb.node .null (Verb.leaf 6) (Verb.node rn2 b (Verb.node rc thn els))).noun := by
  have hleaf0 : isTerminal (Verb.leaf 0) = true := rfl
  have h23 : denP (g + 1 + 1) (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
      = some (Noun.cell (Noun.atom 2) (Noun.atom 3)) :=
    denP_null_val (by simp only [denP]) (by simp only [denP])
  have hdc : denP (g + 1 + 1) (Verb.node rc thn els) = some (Verb.node rc thn els).noun :=
    denP_succ (denP_succ hgc)
  -- op₆ evaluation of the guard `b`
  simp only [noun, evalPaper] at hvv
  cases hsb : evalPaper g L.noun b.noun with
  | none => rw [hsb] at hvv; simp at hvv
  | some sbv =>
    rw [hsb] at hvv
    have hEvb : EvP L.noun b.noun sbv := ⟨g, hsb⟩
    have hsb1 : evalPaper (g + 1) L.noun b.noun = some sbv := evalPaper_succ hsb
    have eqLb : pcost g L.noun b.noun = pcost (g + 1) L.noun b.noun :=
      pcost_align hsb (Nat.le_refl g) (by omega)
    -- `[4 [4 b]]` cost is `4 + pcost g L b` (definitional, op4∘op4)
    have hSFinner : pcost (g + 1 + 1) L.noun (Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 4)
      b.noun))
        = 4 + pcost g L.noun b.noun := by simp only [pcost]; omega
    -- The generic argument: whatever branch, the reduct cost < RHS.
    -- key: SF(c,b0) ≤ 2, SF([2,3],d0) ≤ 2, SF(L,a0) is 0 or the branch pcost.
    -- We prove it by decomposing `vcost` and bounding.
    have hbound : ∀ (branchNoun : Verb),
        (sbv = Noun.atom 0 ∧ branchNoun = thn ∨ sbv = Noun.atom 1 ∧ branchNoun = els) →
        evalPaper g L.noun branchNoun.noun = some x →
        vcost (g + 1 + 1)
          (Verb.node .star L
            (Verb.node .star (Verb.node rc thn els)
              (Verb.node .null (Verb.leaf 0)
                (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                  (Verb.node .null (Verb.leaf 0)
                    (Verb.node .star L
                      (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))))))
        < pcost (g + 1 + 1) L.noun
            (Verb.node .null (Verb.leaf 6) (Verb.node rn2 b (Verb.node rc thn els))).noun := by
      intro branchNoun hbr hbev
      -- align the branch cost
      have eqBr : pcost (g + 1 + 1) L.noun branchNoun.noun = pcost (g + 1) L.noun branchNoun.noun :=
        pcost_align hbev (by omega) (by omega)
      -- RHS = 100 + pcost(g+1) L b + pcost(g+1) L branch
      have hRHS : pcost (g + 1 + 1) L.noun
          (Verb.node .null (Verb.leaf 6) (Verb.node rn2 b (Verb.node rc thn els))).noun
          = 100 + pcost (g + 1) L.noun b.noun + pcost (g + 1) L.noun branchNoun.noun := by
        rcases hbr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp only [noun, pcost, hsb1]
      rw [hRHS]
      -- decompose vcost of the reduct
      simp only [vcost_star_eq, vcost_null_eq, vcost_terminal L hL,
        vcost_terminal (Verb.node rc thn els) htc,
        vcost_terminal (Verb.node .null (Verb.leaf 2) (Verb.leaf 3)) ht23,
        vcost_terminal (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)) ht4,
        vcost_terminal (Verb.leaf 0) hleaf0, hdL, h4b, Nat.add_zero, Nat.zero_add]
      -- SF([2,3],d0) ≤ 2
      have hc0le : (match denP (g + 1 + 1) (Verb.node .null (Verb.leaf 2) (Verb.leaf 3)),
            denP (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
              (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))
                with
          | some sa, some fo => pcost (g + 1 + 1) sa fo | _, _ => 0) ≤ 2 := by
        rw [h23]
        cases hd0 : denP (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
            (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))
              with
        | none => simp
        | some dv => obtain ⟨w, rfl⟩ := denP_null_leaf0 hd0; simp only [pcost]; omega
      -- SF(c,b0) ≤ 2
      have ha0le : (match denP (g + 1 + 1) (Verb.node rc thn els),
            denP (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
              (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                (Verb.node .null (Verb.leaf 0)
                  (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4)
                    b)))))) with
          | some sa, some fo => pcost (g + 1 + 1) sa fo | _, _ => 0) ≤ 2 := by
        rw [hdc]
        cases hb0 : denP (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
            (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
              (Verb.node .null (Verb.leaf 0)
                (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4)
                  b)))))) with
        | none => simp
        | some bv => obtain ⟨w, rfl⟩ := denP_null_leaf0 hb0; simp only [pcost]; omega
      -- SF(L,a0) ≤ pcost(g+1) L branch
      have hrrle : (match some L.noun,
            denP (g + 1 + 1) (Verb.node .star (Verb.node rc thn els)
              (Verb.node .null (Verb.leaf 0)
                (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                  (Verb.node .null (Verb.leaf 0)
                    (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4)
                      b))))))) with
          | some sa, some fo => pcost (g + 1 + 1) sa fo | _, _ => 0)
          ≤ pcost (g + 1) L.noun branchNoun.noun := by
        cases haa : denP (g + 1 + 1) (Verb.node .star (Verb.node rc thn els)
            (Verb.node .null (Verb.leaf 0)
              (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                (Verb.node .null (Verb.leaf 0)
                  (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4)
                    b))))))) with
        | none => simp
        | some aa =>
            simp only
            -- trace: aa = branchNoun.noun
            have hDa0 : DenP (Verb.node .star (Verb.node rc thn els)
                (Verb.node .null (Verb.leaf 0)
                  (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                    (Verb.node .null (Verb.leaf 0)
                      (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf
                        4) b))))))) aa :=
              ⟨g + 1 + 1, haa⟩
            rw [DenP_star] at hDa0
            obtain ⟨cv, b0v, hDc0, hDb0, hEva0⟩ := hDa0
            have : cv = (Verb.node rc thn els).noun := (DenP_terminal_iff htc).1 hDc0
            subst this
            rw [DenP_null] at hDb0
            obtain ⟨z, c0v, rfl, hDz, hDc0'⟩ := hDb0
            have : z = Noun.atom 0 := DenP_leaf.1 hDz
            subst this
            rw [EvP_op0] at hEva0
            obtain ⟨ax, rfl, hslotA⟩ := hEva0
            rw [DenP_star] at hDc0'
            obtain ⟨p23, d0v, hD23, hDd0, hEvc0⟩ := hDc0'
            have hp23 : p23 = Noun.cell (Noun.atom 2) (Noun.atom 3) := by
              have := (DenP_terminal_iff ht23).1 hD23; simpa only [noun] using this
            subst hp23
            rw [DenP_null] at hDd0
            obtain ⟨z2, iv, rfl, hDz2, hDinner⟩ := hDd0
            have : z2 = Noun.atom 0 := DenP_leaf.1 hDz2
            subst this
            rw [EvP_op0] at hEvc0
            obtain ⟨ax2, rfl, hslotB⟩ := hEvc0
            rw [DenP_star] at hDinner
            obtain ⟨Lv, fv, hDL', hD4, hEvinner⟩ := hDinner
            have : Lv = L.noun := (DenP_terminal_iff hL).1 hDL'
            subst this
            have hfv : fv = Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 4) b.noun) := by
              have := (DenP_terminal_iff ht4).1 hD4; simpa only [noun] using this
            subst hfv
            rw [EvP_op4] at hEvinner
            obtain ⟨y, hEvy, hlusy⟩ := hEvinner
            rw [EvP_op4] at hEvy
            obtain ⟨y2, hEvy2, hlusy2⟩ := hEvy
            have hy2 : y2 = sbv := EvP_det hEvy2 hEvb
            subst hy2
            -- Compute each branch.
            rcases hbr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · -- sbv = 0 : y = 1, ax2 = 2, ax = 2, aa = slot 2 c.noun = thn.noun
              have hy : y = Noun.atom 1 := by
                rw [lus_atom] at hlusy2; exact (Option.some.inj hlusy2).symm
              subst hy
              have hax2 : ax2 = 2 := by
                rw [lus_atom] at hlusy; exact (Noun.atom.inj (Option.some.inj hlusy)).symm
              subst hax2
              rw [slot_two] at hslotB
              have hax : ax = 2 := (Noun.atom.inj (Option.some.inj hslotB)).symm
              subst hax
              rw [noun, slot_two] at hslotA
              obtain rfl := Option.some.inj hslotA
              exact eqBr.le
            · -- sbv = 1 : y = 2, ax2 = 3, ax = 3, aa = slot 3 c.noun = els.noun
              have hy : y = Noun.atom 2 := by
                rw [lus_atom] at hlusy2; exact (Option.some.inj hlusy2).symm
              subst hy
              have hax2 : ax2 = 3 := by
                rw [lus_atom] at hlusy; exact (Noun.atom.inj (Option.some.inj hlusy)).symm
              subst hax2
              rw [slot_three] at hslotB
              have hax : ax = 3 := (Noun.atom.inj (Option.some.inj hslotB)).symm
              subst hax
              rw [noun, slot_three] at hslotA
              obtain rfl := Option.some.inj hslotA
              exact eqBr.le
      -- combine
      rw [hSFinner]
      cases evaluatedZero : denP (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
                      (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf
                        4) b))))
        <;> cases evaluatedOne : denP (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
                      (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                        (Verb.node .null (Verb.leaf 0)
                          (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null
                            (Verb.leaf 4) b))))))
        <;> cases evaluatedTwo : denP (g + 1 + 1) (Verb.node .star (Verb.node rc thn els)
                      (Verb.node .null (Verb.leaf 0)
                        (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                          (Verb.node .null (Verb.leaf 0)
                            (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null
                              (Verb.leaf 4) b)))))))
        <;> simp only [hdc, h23, evaluatedZero, evaluatedOne, evaluatedTwo]
          at hc0le ha0le hrrle ⊢
        <;> omega
    -- dispatch on the guard value
    cases sbv with
    | cell k1 k2 => simp at hvv
    | atom av =>
        match av, hvv with
        | 0, hvv => exact hbound thn (Or.inl ⟨rfl, rfl⟩) hvv
        | 1, hvv => exact hbound els (Or.inr ⟨rfl, rfl⟩) hvv
        | (k + 2), hvv => simp at hvv
end Nock.Verb
