-- Prove2me | solution 1 for MondererShapley.Improvement.improvesTo_trans
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:11:21.892468+00:00
-- url     : https://prove2.me/submissions/8b77bec7-73ea-4a8f-a2e0-80c65d0b09bc

import Mathlib
import Definitions.Def_MondererShapley_Improvement_ImprovesTo
import Definitions.Def_MondererShapley_Improvement_HasFIP
open MondererShapley.Improvement
open MondererShapley.ClosedPath
open Relation
private def gain {ι : Type*} [DecidableEq ι] {Y : ι → Type*}
    (u : ι → (∀ i, Y i) → ℝ) (a b : ∀ i, Y i) : Prop :=
  ∃ i, IsStep a b i ∧ u i a < u i b
private theorem path_reaches {ι : Type*} [DecidableEq ι] {Y : ι → Type*}
    (u : ι → (∀ i, Y i) → ℝ) (γ : FinPath Y) (h : γ.IsImprovement u) :
    ReflTransGen (gain u) (γ.pt 0) (γ.pt (Fin.last γ.len)) := by
  have pref : ∀ n (hn : n ≤ γ.len),
      ReflTransGen (gain u) (γ.pt 0) (γ.pt ⟨n, by omega⟩) := by
    intro n
    induction n with
    | zero => intro hn; exact .refl
    | succ n ih =>
      intro hn
      exact (ih (by omega)).tail ⟨γ.dev ⟨n, by omega⟩,
        γ.step ⟨n, by omega⟩, h ⟨n, by omega⟩⟩
  exact pref γ.len le_rfl
private theorem reaches_path {ι : Type*} [DecidableEq ι] {Y : ι → Type*}
    (u : ι → (∀ i, Y i) → ℝ) {a b : ∀ i, Y i}
    (h : ReflTransGen (gain u) a b) :
    ∃ γ : FinPath Y, γ.IsImprovement u ∧ γ.pt 0 = a ∧ γ.pt (Fin.last γ.len) = b := by
  induction h with
  | refl =>
    exact ⟨⟨0, fun _ => a, Fin.elim0, fun k => Fin.elim0 k⟩,
      (fun k => Fin.elim0 k), rfl, rfl⟩
  | @tail b c hab hbc ih =>
    obtain ⟨γ, hg, ha, hb⟩ := ih
    obtain ⟨i, hs, hi⟩ := hbc
    let δ : FinPath Y := {
      len := γ.len + 1
      pt := Fin.lastCases c γ.pt
      dev := Fin.lastCases i γ.dev
      step := by
        intro k
        refine Fin.lastCases ?_ (fun l => ?_) k
        · simpa [hb] using hs
        · simpa only [Fin.succ_castSucc, Fin.lastCases_castSucc] using γ.step l }
    refine ⟨δ, ?_, ?_, ?_⟩
    · intro k
      refine Fin.lastCases ?_ (fun l => ?_) k
      · simpa [δ, hb] using hi
      · simpa only [δ, Fin.lastCases_castSucc, Fin.succ_castSucc] using hg l
    · change Fin.lastCases c γ.pt (Fin.castSucc (0 : Fin (γ.len + 1))) = a
      simpa only [Fin.lastCases_castSucc] using ha
    · simp [δ]
theorem solution {ι : Type*} [DecidableEq ι] {Y : ι → Type*} [Fintype ι]
    (u : ι → (∀ i, Y i) → ℝ) (hFIP : HasFIP u) (x y z : ∀ i, Y i)
    (hxy : ImprovesTo u x y) (hyz : ImprovesTo u y z) : ImprovesTo u x z := by
  classical
  have hw : WellFounded (Function.swap (gain u)) := by
    apply wellFounded_iff_isEmpty_descending_chain.mpr
    refine ⟨?_⟩
    rintro ⟨f, hf⟩
    apply hFIP
    exact ⟨f, fun n => (hf n).choose, fun n => (hf n).choose_spec⟩
  obtain ⟨hne1, γ, hg, ha, hb⟩ := hxy
  obtain ⟨hne2, η, hh, hc, hd⟩ := hyz
  have r1 : ReflTransGen (gain u) y x := by simpa [ha, hb] using path_reaches u γ hg
  have r2 : ReflTransGen (gain u) z y := by simpa [hc, hd] using path_reaches u η hh
  have t1 : TransGen (gain u) y x :=
    (reflTransGen_iff_eq_or_transGen.mp r1).resolve_left hne1
  have t2 : TransGen (gain u) z y :=
    (reflTransGen_iff_eq_or_transGen.mp r2).resolve_left hne2
  have hne : x ≠ z := by
    intro he
    have cycle := transGen_swap.mpr (t2.trans t1)
    exact hw.transGen.irrefl.irrefl x (by simpa only [← he] using cycle)
  exact ⟨hne, reaches_path u (r2.trans r1)⟩
#print axioms solution
