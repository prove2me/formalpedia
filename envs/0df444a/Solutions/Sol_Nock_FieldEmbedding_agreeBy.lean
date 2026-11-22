-- Prove2me | solution 1 for Nock.FieldEmbedding.agreeBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:25.966143+00:00
-- url     : https://prove2.me/submissions/a0cca531-ddac-49e7-9385-7ebfbd1a35aa

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_LeanPool_PureNock_ModularEval
public import Theorems.Thm_Nock_FieldEmbedding_BoundedBy_atom
public import Theorems.Thm_Nock_FieldEmbedding_BoundedBy_cell
public import Theorems.Thm_Nock_FieldEmbedding_slot_boundedBy
public import Theorems.Thm_Nock_FieldEmbedding_edit_boundedBy
public import Theorems.Thm_Nock_FieldEmbedding_wut_boundedBy
public import Theorems.Thm_Nock_FieldEmbedding_tis_boundedBy
attribute [local simp] Nock.FieldEmbedding.BoundedBy_atom
attribute [local simp] Nock.FieldEmbedding.BoundedBy_cell
section
@[expose] public section
namespace Nock.FieldEmbedding
open Nock Nock.Noun
private theorem guarded_hint_agreement (q fuel : ℕ)
  (ih :
    ∀ (s f r : Noun),
      BoundedBy q s →
        BoundedBy q f →
          evalGBy q fuel s f = some r → evalN fuel s f = some r ∧ evalFBy q fuel s f = some r ∧
            BoundedBy q r)
  (s r : Noun) (hs : BoundedBy q s) (tail : Noun) (hft : BoundedBy q tail)
  (hG : evalGBy q (fuel + 1) s ((atom 11).cell tail) = some r) :
  evalN (fuel + 1) s ((atom 11).cell tail) = some r ∧
    evalFBy q (fuel + 1) s ((atom 11).cell tail) = some r ∧ BoundedBy q r := by
  match tail with
  | .cell (.cell hd clue) body =>
      obtain ⟨⟨-, hfclue⟩, hfbody⟩ := hft
      simp only [evalGBy] at hG
      cases hcl : evalGBy q fuel s clue with
      | none => rw [hcl] at hG; simp at hG
      | some vc =>
        rw [hcl] at hG
        obtain ⟨hNcl, hFcl, _⟩ := ih s clue vc hs hfclue hcl
        obtain ⟨hNb, hFb, hBr⟩ := ih s body r hs hfbody hG
        exact ⟨by simp only [evalN, hNcl, hNb],
               by simp only [evalFBy, hFcl, hFb], hBr⟩
  | .cell (.atom hint) body =>
      obtain ⟨-, hfbody⟩ := hft
      simp only [evalGBy] at hG
      obtain ⟨hNb, hFb, hBr⟩ := ih s body r hs hfbody hG
      exact ⟨by simp only [evalN, hNb],
             by simp only [evalFBy, hFb], hBr⟩
  | .atom _ => simp [evalGBy] at hG
private theorem guarded_conditional_agreement (q fuel : ℕ)
  (ih :
    ∀ (s f r : Noun),
      BoundedBy q s →
        BoundedBy q f →
          evalGBy q fuel s f = some r → evalN fuel s f = some r ∧ evalFBy q fuel s f = some r ∧
            BoundedBy q r)
  (s r : Noun) (hs : BoundedBy q s) (tail : Noun) (hft : BoundedBy q tail)
  (hG : evalGBy q (fuel + 1) s ((atom 6).cell tail) = some r) :
  evalN (fuel + 1) s ((atom 6).cell tail) = some r ∧
    evalFBy q (fuel + 1) s ((atom 6).cell tail) = some r ∧ BoundedBy q r := by
  match tail with
  | .cell b (.cell c d) =>
      obtain ⟨hfb, hfc, hfd⟩ := hft
      simp only [evalGBy] at hG
      cases hb : evalGBy q fuel s b with
      | none => rw [hb] at hG; simp at hG
      | some vb =>
        obtain ⟨hNb, hFb, _⟩ := ih s b vb hs hfb hb
        rw [hb] at hG
        match vb, hNb, hFb, hG with
        | .atom 0, hNb, hFb, hG =>
            obtain ⟨hNc, hFc, hBr⟩ := ih s c r hs hfc hG
            exact ⟨by simp only [evalN, hNb, hNc],
                   by simp only [evalFBy, hFb, hFc], hBr⟩
        | .atom 1, hNb, hFb, hG =>
            obtain ⟨hNd, hFd, hBr⟩ := ih s d r hs hfd hG
            exact ⟨by simp only [evalN, hNb, hNd],
                   by simp only [evalFBy, hFb, hFd], hBr⟩
        | .atom (n+2), _, _, hG => simp at hG
        | .cell _ _, _, _, hG => simp at hG
  | .cell b (.atom _) => simp [evalGBy] at hG
  | .atom _ => simp [evalGBy] at hG
end Nock.FieldEmbedding
end
end

set_option autoImplicit true
@[expose] public section
public section
open Nock Nock.FieldEmbedding
open Nock Nock.Noun
namespace Nock.FieldEmbedding
theorem _root_.solution (q : ℕ) (hq : 1 < q) :
    ∀ (fuel : Nat) (s f r : Noun), BoundedBy q s → BoundedBy q f →
      evalGBy q fuel s f = some r →
        evalN fuel s f = some r ∧ evalFBy q fuel s f = some r ∧ BoundedBy q r := by
  intro fuel
  induction fuel with
  | zero => intro s f r _ _ hG; simp [evalGBy] at hG
  | succ fuel ih =>
    intro s f r hs hf hG
    match f with
    | .atom a => simp [evalGBy] at hG
    | .cell (.cell b c) d =>
        obtain ⟨hfbc, hfd⟩ := hf
        simp only [evalGBy] at hG
        cases hbc : evalGBy q fuel s (.cell b c) with
        | none => rw [hbc] at hG; simp at hG
        | some l =>
          cases hd : evalGBy q fuel s d with
          | none => rw [hbc, hd] at hG; simp at hG
          | some r' =>
            rw [hbc, hd] at hG
            simp only [Option.some.injEq] at hG
            obtain ⟨hNbc, hFbc, hBl⟩ := ih s (.cell b c) l hs hfbc hbc
            obtain ⟨hNd, hFd, hBr⟩ := ih s d r' hs hfd hd
            subst hG
            refine ⟨?_, ?_, ⟨hBl, hBr⟩⟩
            · simp only [evalN, hNbc, hNd]
            · simp only [evalFBy, hFbc, hFd]
    | .cell (.atom op) tail =>
        obtain ⟨-, hft⟩ := hf
        match op with
        | 0 =>
            simp only [evalGBy] at hG
            match tail with
            | .atom ax =>
                refine ⟨?_, ?_, slot_boundedBy q ax s hs hG⟩
                · simpa only [evalN] using hG
                · simpa only [evalFBy] using hG
            | .cell _ _ => simp at hG
        | 1 =>
            simp only [evalGBy] at hG
            obtain rfl := Option.some.inj hG
            exact ⟨by simp only [evalN], by simp only [evalFBy], hft⟩
        | 2 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGBy] at hG
                cases hb : evalGBy q fuel s b with
                | none => rw [hb] at hG; simp at hG
                | some sb =>
                  cases hc : evalGBy q fuel s c with
                  | none => rw [hb, hc] at hG; simp at hG
                  | some sc =>
                    rw [hb, hc] at hG
                    obtain ⟨hNb, hFb, hBb⟩ := ih s b sb hs hfb hb
                    obtain ⟨hNc, hFc, hBc⟩ := ih s c sc hs hfc hc
                    obtain ⟨hN2, hF2, hBr⟩ := ih sb sc r hBb hBc hG
                    exact ⟨by simp only [evalN, hNb, hNc, hN2],
                           by simp only [evalFBy, hFb, hFc, hF2], hBr⟩
            | .atom _ => simp [evalGBy] at hG
        | 3 =>
            simp only [evalGBy] at hG
            cases ht : evalGBy q fuel s tail with
            | none => rw [ht] at hG; simp at hG
            | some v =>
              rw [ht] at hG
              simp only [Option.map_some, Option.some.injEq] at hG
              obtain ⟨hN, hF, _⟩ := ih s tail v hs hft ht
              subst hG
              exact ⟨by simp only [evalN, hN, Option.map_some],
                     by simp only [evalFBy, hF, Option.map_some], wut_boundedBy hq v⟩
        | 4 =>
            simp only [evalGBy] at hG
            cases ht : evalGBy q fuel s tail with
            | none => rw [ht] at hG; simp at hG
            | some v =>
              rw [ht] at hG
              obtain ⟨hN, hF, hBv⟩ := ih s tail v hs hft ht
              cases v with
              | cell _ _ => simp [lusGBy] at hG
              | atom n =>
                simp only [Option.bind_some, lusGBy] at hG
                split at hG
                · rename_i hlt
                  obtain rfl := Option.some.inj hG
                  refine ⟨?_, ?_, ?_⟩
                  · simp only [evalN, hN, Option.bind_some, Noun.lus]
                  · simp only [evalFBy, hF, Option.bind_some, lusFBy, Nat.mod_eq_of_lt hlt]
                  · exact hlt
                · simp at hG
        | 5 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGBy] at hG
                cases hb : evalGBy q fuel s b with
                | none => rw [hb] at hG; simp at hG
                | some sb =>
                  cases hc : evalGBy q fuel s c with
                  | none => rw [hb, hc] at hG; simp at hG
                  | some sc =>
                    rw [hb, hc] at hG
                    simp only [Option.some.injEq] at hG
                    obtain ⟨hNb, hFb, _⟩ := ih s b sb hs hfb hb
                    obtain ⟨hNc, hFc, _⟩ := ih s c sc hs hfc hc
                    subst hG
                    exact ⟨by simp only [evalN, hNb, hNc],
                           by simp only [evalFBy, hFb, hFc], tis_boundedBy hq sb sc⟩
            | .atom _ => simp [evalGBy] at hG
        | 6 =>
            exact guarded_conditional_agreement q fuel ih s r hs tail hft hG
        | 7 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGBy] at hG
                cases hb : evalGBy q fuel s b with
                | none => rw [hb] at hG; simp at hG
                | some sb =>
                  rw [hb] at hG
                  obtain ⟨hNb, hFb, hBb⟩ := ih s b sb hs hfb hb
                  obtain ⟨hN7, hF7, hBr⟩ := ih sb c r hBb hfc hG
                  exact ⟨by simp only [evalN, hNb, hN7],
                         by simp only [evalFBy, hFb, hF7], hBr⟩
            | .atom _ => simp [evalGBy] at hG
        | 8 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGBy] at hG
                cases hb : evalGBy q fuel s b with
                | none => rw [hb] at hG; simp at hG
                | some sb =>
                  rw [hb] at hG
                  obtain ⟨hNb, hFb, hBb⟩ := ih s b sb hs hfb hb
                  obtain ⟨hN8, hF8, hBr⟩ := ih (.cell sb s) c r ⟨hBb, hs⟩ hfc hG
                  exact ⟨by simp only [evalN, hNb, hN8],
                         by simp only [evalFBy, hFb, hF8], hBr⟩
            | .atom _ => simp [evalGBy] at hG
        | 9 =>
            match tail with
            | .cell (.atom ax) c =>
                obtain ⟨-, hfc⟩ := hft
                simp only [evalGBy] at hG
                cases hc : evalGBy q fuel s c with
                | none => rw [hc] at hG; simp at hG
                | some core =>
                  rw [hc] at hG
                  dsimp only at hG
                  obtain ⟨hNc, hFc, hBcore⟩ := ih s c core hs hfc hc
                  cases harm : slot ax core with
                  | none => rw [harm] at hG; simp at hG
                  | some arm =>
                    rw [harm] at hG
                    dsimp only at hG
                    have hBarm : BoundedBy q arm := slot_boundedBy q ax core hBcore harm
                    obtain ⟨hN9, hF9, hBr⟩ := ih core arm r hBcore hBarm hG
                    exact ⟨by simp only [evalN, hNc, harm, hN9],
                           by simp only [evalFBy, hFc, harm, hF9], hBr⟩
            | .cell (.cell _ _) _ => simp [evalGBy] at hG
            | .atom _ => simp [evalGBy] at hG
        | 10 =>
            match tail with
            | .cell (.cell (.atom ax) c) d =>
                obtain ⟨⟨-, hfc⟩, hfd⟩ := hft
                simp only [evalGBy] at hG
                cases hc : evalGBy q fuel s c with
                | none => rw [hc] at hG; simp at hG
                | some new =>
                  cases hd : evalGBy q fuel s d with
                  | none => rw [hc, hd] at hG; simp at hG
                  | some old =>
                    rw [hc, hd] at hG
                    obtain ⟨hNc, hFc, hBnew⟩ := ih s c new hs hfc hc
                    obtain ⟨hNd, hFd, hBold⟩ := ih s d old hs hfd hd
                    refine ⟨?_, ?_, edit_boundedBy q ax new old hBnew hBold hG⟩
                    · simp only [evalN, hNc, hNd]; exact hG
                    · simp only [evalFBy, hFc, hFd]; exact hG
            | .cell (.cell (.cell _ _) _) _ => simp [evalGBy] at hG
            | .cell (.atom _) _ => simp [evalGBy] at hG
            | .atom _ => simp [evalGBy] at hG
        | 11 =>
            exact guarded_hint_agreement q fuel ih s r hs tail hft hG
        | (n+12) => simp [evalGBy] at hG
end Nock.FieldEmbedding
