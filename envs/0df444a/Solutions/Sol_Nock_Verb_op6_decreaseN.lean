-- Prove2me | solution 1 for Nock.Verb.op6_decreaseN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:26:51.500406+00:00
-- url     : https://prove2.me/submissions/6391e16c-42f9-4fb8-9be7-b3570a2ebd3d

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_EvN_det
public import Theorems.Thm_Nock_Verb_den_null_val
public import Theorems.Thm_Nock_Verb_den_null_leaf0
public import Theorems.Thm_Nock_Verb_ncost_align
public import Theorems.Thm_Nock_Verb_vcostN_star_eq
public import Theorems.Thm_Nock_Verb_vcostN_null_eq
public import Theorems.Thm_Nock_Verb_vcostN_terminal
public import Theorems.Thm_Nock_Verb_Den_leaf
public import Theorems.Thm_Nock_Verb_Den_null
public import Theorems.Thm_Nock_Verb_Den_star
public import Theorems.Thm_Nock_Verb_Den_terminal_iff
public import Theorems.Thm_Nock_Verb_EvN_op0
public import Theorems.Thm_Nock_Verb_EvN_op4
public import Theorems.Thm_Nock_Verb_den_succ
public import Theorems.Thm_Nock_Verb_lus_atom
public import Theorems.Thm_Nock_Verb_slot_three
public import Theorems.Thm_Nock_Verb_slot_two
public import Theorems.Thm_Nock_evalN_succ


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
    (hgc : den g (Verb.node rc thn els) = some (Verb.node rc thn els).noun)
    (hdL : den (g + 1 + 1) L = some L.noun)
    (h4b : den (g + 1 + 1) (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))
        = some (Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 4) b.noun)))
    (ht4 : isTerminal (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)) = true)
    (ht23 : isTerminal (Verb.node .null (Verb.leaf 2) (Verb.leaf 3)) = true)
    (hvv : evalN (g + 1) L.noun
        (Noun.cell (Noun.atom 6) (Verb.node rn2 b (Verb.node rc thn els)).noun) = some x) :
    vcostN (g + 1 + 1)
        (Verb.node .star L
          (Verb.node .star (Verb.node rc thn els)
            (Verb.node .null (Verb.leaf 0)
              (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                (Verb.node .null (Verb.leaf 0)
                  (Verb.node .star L
                    (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))))))
      < ncost (g + 1 + 1) L.noun
          (Verb.node .null (Verb.leaf 6) (Verb.node rn2 b (Verb.node rc thn els))).noun := by
  have hleaf0 : isTerminal (Verb.leaf 0) = true := rfl
  have h23 : den (g + 1 + 1) (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
      = some (Noun.cell (Noun.atom 2) (Noun.atom 3)) :=
    den_null_val (by simp only [den]) (by simp only [den])
  have hdc : den (g + 1 + 1) (Verb.node rc thn els) = some (Verb.node rc thn els).noun :=
    den_succ (den_succ hgc)
  simp only [noun, evalN] at hvv
  cases hsb : evalN g L.noun b.noun with
  | none => rw [hsb] at hvv; simp at hvv
  | some sbv =>
    rw [hsb] at hvv
    have hEvb : Ev L.noun b.noun sbv := ⟨g, hsb⟩
    have hsb1 : evalN (g + 1) L.noun b.noun = some sbv := evalN_succ hsb
    have eqLb : ncost g L.noun b.noun = ncost (g + 1) L.noun b.noun :=
      ncost_align hsb (Nat.le_refl g) (by omega)
    have hSFinner : ncost (g + 1 + 1) L.noun (Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 4)
      b.noun))
        = 4 + ncost g L.noun b.noun := by simp only [ncost]; omega
    have hbound : ∀ (branchNoun : Verb),
        (sbv = Noun.atom 0 ∧ branchNoun = thn ∨ sbv = Noun.atom 1 ∧ branchNoun = els) →
        evalN g L.noun branchNoun.noun = some x →
        vcostN (g + 1 + 1)
          (Verb.node .star L
            (Verb.node .star (Verb.node rc thn els)
              (Verb.node .null (Verb.leaf 0)
                (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                  (Verb.node .null (Verb.leaf 0)
                    (Verb.node .star L
                      (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))))))
        < ncost (g + 1 + 1) L.noun
            (Verb.node .null (Verb.leaf 6) (Verb.node rn2 b (Verb.node rc thn els))).noun := by
      intro branchNoun hbr hbev
      have eqBr : ncost (g + 1 + 1) L.noun branchNoun.noun = ncost (g + 1) L.noun branchNoun.noun :=
        ncost_align hbev (by omega) (by omega)
      have hRHS : ncost (g + 1 + 1) L.noun
          (Verb.node .null (Verb.leaf 6) (Verb.node rn2 b (Verb.node rc thn els))).noun
          = 100 + ncost (g + 1) L.noun b.noun + ncost (g + 1) L.noun branchNoun.noun := by
        rcases hbr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp only [noun, ncost, hsb1]
      rw [hRHS]
      simp only [vcostN_star_eq, vcostN_null_eq, vcostN_terminal L hL,
        vcostN_terminal (Verb.node rc thn els) htc,
        vcostN_terminal (Verb.node .null (Verb.leaf 2) (Verb.leaf 3)) ht23,
        vcostN_terminal (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)) ht4,
        vcostN_terminal (Verb.leaf 0) hleaf0, hdL, h4b, Nat.add_zero, Nat.zero_add]
      have hc0le : (match den (g + 1 + 1) (Verb.node .null (Verb.leaf 2) (Verb.leaf 3)),
            den (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
              (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))
                with
          | some sa, some fo => ncost (g + 1 + 1) sa fo | _, _ => 0) ≤ 2 := by
        rw [h23]
        cases hd0 : den (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
            (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))
              with
        | none => simp
        | some dv => obtain ⟨w, rfl⟩ := den_null_leaf0 hd0; simp only [ncost]; omega
      have ha0le : (match den (g + 1 + 1) (Verb.node rc thn els),
            den (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
              (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                (Verb.node .null (Verb.leaf 0)
                  (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4)
                    b)))))) with
          | some sa, some fo => ncost (g + 1 + 1) sa fo | _, _ => 0) ≤ 2 := by
        rw [hdc]
        cases hb0 : den (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
            (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
              (Verb.node .null (Verb.leaf 0)
                (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4)
                  b)))))) with
        | none => simp
        | some bv => obtain ⟨w, rfl⟩ := den_null_leaf0 hb0; simp only [ncost]; omega
      have hrrle : (match some L.noun,
            den (g + 1 + 1) (Verb.node .star (Verb.node rc thn els)
              (Verb.node .null (Verb.leaf 0)
                (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                  (Verb.node .null (Verb.leaf 0)
                    (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4)
                      b))))))) with
          | some sa, some fo => ncost (g + 1 + 1) sa fo | _, _ => 0)
          ≤ ncost (g + 1) L.noun branchNoun.noun := by
        cases haa : den (g + 1 + 1) (Verb.node .star (Verb.node rc thn els)
            (Verb.node .null (Verb.leaf 0)
              (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                (Verb.node .null (Verb.leaf 0)
                  (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4)
                    b))))))) with
        | none => simp
        | some aa =>
            simp only
            have hDa0 : Den (Verb.node .star (Verb.node rc thn els)
                (Verb.node .null (Verb.leaf 0)
                  (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                    (Verb.node .null (Verb.leaf 0)
                      (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf
                        4) b))))))) aa :=
              ⟨g + 1 + 1, haa⟩
            rw [Den_star] at hDa0
            obtain ⟨cv, b0v, hDc0, hDb0, hEva0⟩ := hDa0
            have : cv = (Verb.node rc thn els).noun := (Den_terminal_iff htc).1 hDc0
            subst this
            rw [Den_null] at hDb0
            obtain ⟨z, c0v, rfl, hDz, hDc0'⟩ := hDb0
            have : z = Noun.atom 0 := Den_leaf.1 hDz
            subst this
            rw [EvN_op0] at hEva0
            obtain ⟨ax, rfl, hslotA⟩ := hEva0
            rw [Den_star] at hDc0'
            obtain ⟨p23, d0v, hD23, hDd0, hEvc0⟩ := hDc0'
            have hp23 : p23 = Noun.cell (Noun.atom 2) (Noun.atom 3) := by
              have := (Den_terminal_iff ht23).1 hD23; simpa only [noun] using this
            subst hp23
            rw [Den_null] at hDd0
            obtain ⟨z2, iv, rfl, hDz2, hDinner⟩ := hDd0
            have : z2 = Noun.atom 0 := Den_leaf.1 hDz2
            subst this
            rw [EvN_op0] at hEvc0
            obtain ⟨ax2, rfl, hslotB⟩ := hEvc0
            rw [Den_star] at hDinner
            obtain ⟨Lv, fv, hDL', hD4, hEvinner⟩ := hDinner
            have : Lv = L.noun := (Den_terminal_iff hL).1 hDL'
            subst this
            have hfv : fv = Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 4) b.noun) := by
              have := (Den_terminal_iff ht4).1 hD4; simpa only [noun] using this
            subst hfv
            rw [EvN_op4] at hEvinner
            obtain ⟨y, hEvy, hlusy⟩ := hEvinner
            rw [EvN_op4] at hEvy
            obtain ⟨y2, hEvy2, hlusy2⟩ := hEvy
            have hy2 : y2 = sbv := EvN_det hEvy2 hEvb
            subst hy2
            rcases hbr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · have hy : y = Noun.atom 1 := by
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
            · have hy : y = Noun.atom 2 := by
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
      rw [hSFinner]
      cases evaluatedZero : den (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
                      (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf
                        4) b))))
        <;> cases evaluatedOne : den (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
                      (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                        (Verb.node .null (Verb.leaf 0)
                          (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null
                            (Verb.leaf 4) b))))))
        <;> cases evaluatedTwo : den (g + 1 + 1) (Verb.node .star (Verb.node rc thn els)
                      (Verb.node .null (Verb.leaf 0)
                        (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                          (Verb.node .null (Verb.leaf 0)
                            (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null
                              (Verb.leaf 4) b)))))))
        <;> simp only [hdc, h23, evaluatedZero, evaluatedOne, evaluatedTwo]
          at hc0le ha0le hrrle ⊢
        <;> omega
    cases sbv with
    | cell k1 k2 => simp at hvv
    | atom av =>
        match av, hvv with
        | 0, hvv => exact hbound thn (Or.inl ⟨rfl, rfl⟩) hvv
        | 1, hvv => exact hbound els (Or.inr ⟨rfl, rfl⟩) hvv
        | (k + 2), hvv => simp at hvv
end Nock.Verb
