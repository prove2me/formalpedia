-- Prove2me | solution 1 for Nock.FieldEmbedding.evalFBy_boundedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:28:14.759953+00:00
-- url     : https://prove2.me/submissions/f148ae8e-5ece-4211-9b8f-05102d7bdea8

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_LeanPool_PureNock_ModularEval
public import Theorems.Thm_Nock_FieldEmbedding_BoundedBy_atom
public import Theorems.Thm_Nock_FieldEmbedding_BoundedBy_cell
public import Theorems.Thm_Nock_FieldEmbedding_slot_boundedBy
public import Theorems.Thm_Nock_FieldEmbedding_edit_boundedBy
public import Theorems.Thm_Nock_FieldEmbedding_lusFBy_bounded
public import Theorems.Thm_Nock_FieldEmbedding_wut_boundedBy
public import Theorems.Thm_Nock_FieldEmbedding_tis_boundedBy
attribute [local simp] Nock.FieldEmbedding.BoundedBy_atom
attribute [local simp] Nock.FieldEmbedding.BoundedBy_cell

set_option autoImplicit true
@[expose] public section
public section
open Nock Nock.FieldEmbedding
open Nock Nock.Noun
namespace Nock.FieldEmbedding
theorem _root_.solution {q : ℕ} (hq : 1 < q) :
    ∀ (fuel : Nat) (s f r : Noun), BoundedBy q s → BoundedBy q f →
      evalFBy q fuel s f = some r → BoundedBy q r := by
  intro fuel
  induction fuel with
  | zero => intro s f r _ _ h; simp [evalFBy] at h
  | succ fuel ih =>
    intro s f r hs hf h
    match f with
    | .atom a => simp [evalFBy] at h
    | .cell (.cell b c) d =>
        obtain ⟨hfbc, hfd⟩ := hf
        simp only [evalFBy] at h
        cases hbc : evalFBy q fuel s (.cell b c) with
        | none => rw [hbc] at h; simp at h
        | some l =>
          cases hd : evalFBy q fuel s d with
          | none => rw [hbc, hd] at h; simp at h
          | some r' =>
            rw [hbc, hd] at h; simp only [Option.some.injEq] at h; subst h
            exact ⟨ih s (.cell b c) l hs hfbc hbc, ih s d r' hs hfd hd⟩
    | .cell (.atom op) tail =>
        obtain ⟨-, hft⟩ := hf
        match op with
        | 0 =>
            simp only [evalFBy] at h
            match tail with
            | .atom ax => exact slot_boundedBy q ax s hs h
            | .cell _ _ => simp at h
        | 1 => simp only [evalFBy] at h; obtain rfl := Option.some.inj h; exact hft
        | 2 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalFBy] at h
                cases hb : evalFBy q fuel s b with
                | none => rw [hb] at h; simp at h
                | some sb =>
                  cases hc : evalFBy q fuel s c with
                  | none => rw [hb, hc] at h; simp at h
                  | some sc =>
                    rw [hb, hc] at h
                    exact ih sb sc r (ih s b sb hs hfb hb) (ih s c sc hs hfc hc) h
            | .atom _ => simp [evalFBy] at h
        | 3 =>
            simp only [evalFBy] at h
            cases ht : evalFBy q fuel s tail with
            | none => rw [ht] at h; simp at h
            | some v =>
              rw [ht] at h; simp only [Option.map_some, Option.some.injEq] at h
              subst h; exact wut_boundedBy hq v
        | 4 =>
            simp only [evalFBy] at h
            cases ht : evalFBy q fuel s tail with
            | none => rw [ht] at h; simp at h
            | some v => rw [ht] at h; exact lusFBy_bounded (by omega) h
        | 5 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalFBy] at h
                cases hb : evalFBy q fuel s b with
                | none => rw [hb] at h; simp at h
                | some sb =>
                  cases hc : evalFBy q fuel s c with
                  | none => rw [hb, hc] at h; simp at h
                  | some sc =>
                    rw [hb, hc] at h; simp only [Option.some.injEq] at h; subst h
                    exact tis_boundedBy hq sb sc
            | .atom _ => simp [evalFBy] at h
        | 6 =>
            match tail with
            | .cell b (.cell c d) =>
                obtain ⟨hfb, hfc, hfd⟩ := hft
                simp only [evalFBy] at h
                cases hb : evalFBy q fuel s b with
                | none => rw [hb] at h; simp at h
                | some vb =>
                  rw [hb] at h
                  match vb, h with
                  | .atom 0, h => exact ih s c r hs hfc h
                  | .atom 1, h => exact ih s d r hs hfd h
                  | .atom (n+2), h => simp at h
                  | .cell _ _, h => simp at h
            | .cell b (.atom _) => simp [evalFBy] at h
            | .atom _ => simp [evalFBy] at h
        | 7 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalFBy] at h
                cases hb : evalFBy q fuel s b with
                | none => rw [hb] at h; simp at h
                | some sb =>
                  rw [hb] at h
                  exact ih sb c r (ih s b sb hs hfb hb) hfc h
            | .atom _ => simp [evalFBy] at h
        | 8 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalFBy] at h
                cases hb : evalFBy q fuel s b with
                | none => rw [hb] at h; simp at h
                | some sb =>
                  rw [hb] at h
                  exact ih (.cell sb s) c r ⟨ih s b sb hs hfb hb, hs⟩ hfc h
            | .atom _ => simp [evalFBy] at h
        | 9 =>
            match tail with
            | .cell (.atom ax) c =>
                obtain ⟨-, hfc⟩ := hft
                simp only [evalFBy] at h
                cases hc : evalFBy q fuel s c with
                | none => rw [hc] at h; simp at h
                | some core =>
                  rw [hc] at h; dsimp only at h
                  cases harm : slot ax core with
                  | none => rw [harm] at h; simp at h
                  | some arm =>
                    rw [harm] at h; dsimp only at h
                    have hBcore := ih s c core hs hfc hc
                    exact ih core arm r hBcore (slot_boundedBy q ax core hBcore harm) h
            | .cell (.cell _ _) _ => simp [evalFBy] at h
            | .atom _ => simp [evalFBy] at h
        | 10 =>
            match tail with
            | .cell (.cell (.atom ax) c) d =>
                obtain ⟨⟨-, hfc⟩, hfd⟩ := hft
                simp only [evalFBy] at h
                cases hc : evalFBy q fuel s c with
                | none => rw [hc] at h; simp at h
                | some new =>
                  cases hd : evalFBy q fuel s d with
                  | none => rw [hc, hd] at h; simp at h
                  | some old =>
                    rw [hc, hd] at h
                    exact edit_boundedBy q ax new old (ih s c new hs hfc hc)
                      (ih s d old hs hfd hd) h
            | .cell (.cell (.cell _ _) _) _ => simp [evalFBy] at h
            | .cell (.atom _) _ => simp [evalFBy] at h
            | .atom _ => simp [evalFBy] at h
        | 11 =>
            match tail with
            | .cell (.cell hd clue) body =>
                obtain ⟨⟨-, -⟩, hfbody⟩ := hft
                simp only [evalFBy] at h
                cases hcl : evalFBy q fuel s clue with
                | none => rw [hcl] at h; simp at h
                | some vc => rw [hcl] at h; exact ih s body r hs hfbody h
            | .cell (.atom hint) body =>
                obtain ⟨-, hfbody⟩ := hft
                simp only [evalFBy] at h
                exact ih s body r hs hfbody h
            | .atom _ => simp [evalFBy] at h
        | (n+12) => simp [evalFBy] at h
end Nock.FieldEmbedding
