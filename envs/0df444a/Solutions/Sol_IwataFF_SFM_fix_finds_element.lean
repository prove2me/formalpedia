-- Prove2me | solution 1 for IwataFF.SFM.fix_finds_element
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:32:20.712403+00:00
-- url     : https://prove2.me/submissions/6f024421-19c7-4557-9d79-b11c628cba99

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic
import Definitions.Def_IwataFF_SFM_Phase
open IwataFF.SFM

noncomputable def g69g_f : Finset Unit → ℝ := fun X => if X = ∅ then 0 else -1

noncomputable def g69g_st : PhaseState Unit :=
  { idx := (initPhase [()] (2 : ℝ)).idx, phi := clip (initPhase [()] (2 : ℝ)).phi ((2 : ℝ) / 2),
    delta := (2 : ℝ) / 2, begun := true }

theorem g69g_fin_cases (X : Finset Unit) : X = ∅ ∨ X = {()} := by
  rcases X.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact Or.inl h
  · right; ext y; simp only [Finset.mem_singleton]
    constructor
    · intro _; trivial
    · intro _; cases x; cases y; exact hx

theorem g69g_sub : SubmodularOn ({()} : Finset Unit) g69g_f := by
  intro X _ Y _
  rcases g69g_fin_cases X with rfl | rfl <;> rcases g69g_fin_cases Y with rfl | rfl <;>
    simp [g69g_f]

theorem g69g_greedy : greedy g69g_f [()] () = -1 := by
  simp [greedy, g69g_f]

theorem g69g_end : PhaseEnd g69g_f ({()} : Finset Unit) g69g_st := by
  right; left
  unfold Tset
  apply Finset.filter_false_of_mem
  intro v _
  have hx : xOf g69g_f g69g_st v = -1 := by
    cases v; simp [xOf, g69g_st, initPhase, g69g_greedy]
  have hb : bdry ({()} : Finset Unit) g69g_st v = 0 := by
    simp [bdry, g69g_st, initPhase, clip]
  rw [hx, hb]; simp [g69g_st]

theorem solution : ¬ (∀ {α : Type} [DecidableEq α] (V : Finset α) (hV : V.Nonempty)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (L : List α) (hL : IsOrdering V L) (η κ : ℝ) (hη : 0 < η)
    (hxη : ∀ v ∈ V, greedy f L v ≤ η) (hκ : 0 < κ)
    (Y : Finset α) (hY : Y ⊆ V) (hfY : f Y ≤ -κ)
    (st : PhaseState α) (hrun : Relation.ReflTransGen (ScStep f V) (initPhase L η) st)
    (hbeg : st.begun = true) (hend : PhaseEnd f V st)
    (hK : st.delta = η / 2 ^ ⌈Real.logb 2 ((V.card : ℝ) ^ 3 * η / κ)⌉₊),
    st.delta < κ / (V.card : ℝ) ^ 3 ∧
      ∃ w ∈ Y, xOf f st w < -((V.card : ℝ) ^ 2) * st.delta ∧
        ∀ X : Finset α, IsMinimizer V f X → w ∈ X) := by
  intro H
  have hrun : Relation.ReflTransGen (ScStep g69g_f ({()} : Finset Unit))
      (initPhase [()] (2 : ℝ)) g69g_st :=
    Relation.ReflTransGen.single (Or.inl ⟨Or.inl rfl, rfl⟩)
  have hK : g69g_st.delta = (2 : ℝ) / 2 ^ ⌈Real.logb 2
      ((({()} : Finset Unit).card : ℝ) ^ 3 * 2 / 1)⌉₊ := by
    have : ((({()} : Finset Unit).card : ℝ) ^ 3 * 2 / 1) = 2 := by simp
    rw [this, Real.logb_self_eq_one (by norm_num)]
    simp [g69g_st]
  have h := (H ({()} : Finset Unit) ⟨(), Finset.mem_singleton_self _⟩ g69g_f g69g_sub
    (by simp [g69g_f]) [()] ⟨List.nodup_singleton _, by intro a; cases a; simp⟩ 2 1
    (by norm_num) (by intro v _; cases v; rw [g69g_greedy]; norm_num) (by norm_num)
    {()} (subset_refl _) (by simp [g69g_f]) g69g_st hrun rfl g69g_end hK).1
  simp [g69g_st] at h
