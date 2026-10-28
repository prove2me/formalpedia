-- Prove2me | solution 1 for MPECRelax.ScholtesConv.eventually_index_inclusions
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:23:09.803836+00:00
-- url     : https://prove2.me/submissions/434f91ba-ef7f-4dfe-bcff-b993b3f564f0

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC
import Definitions.Def_MPECRelax_ScholtesConv_Scholtes

open Filter Topology

open MPECRelax.ScholtesConv in
theorem solution {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1)
    (t : ℕ → ℝ) (ht_pos : ∀ k, 0 < t k) (ht_anti : Antitone t)
    (ht_lim : Tendsto t atTop (𝓝 0))
    (x : ℕ → E n) (hx : ∀ k, (P.RS (t k)).Feasible (x k))
    (xs : E n) (hxs : Tendsto x atTop (𝓝 xs)) :
    ∀ᶠ k in atTop, P.Ig (x k) ⊆ P.Ig xs ∧ P.IG (x k) ⊆ P.I00 xs ∪ P.I0p xs ∧
      P.IH (x k) ⊆ P.I00 xs ∪ P.Ip0 xs := by
  have hgc : ∀ i, Tendsto (fun k => P.g i (x k)) atTop (𝓝 (P.g i xs)) :=
    fun i => ((hP.2.1 i).continuous.tendsto xs).comp hxs
  have hGc : ∀ i, Tendsto (fun k => P.G i (x k)) atTop (𝓝 (P.G i xs)) :=
    fun i => ((hP.2.2.2.1 i).continuous.tendsto xs).comp hxs
  have hHc : ∀ i, Tendsto (fun k => P.H i (x k)) atTop (𝓝 (P.H i xs)) :=
    fun i => ((hP.2.2.2.2 i).continuous.tendsto xs).comp hxs
  have hGnn : ∀ i, 0 ≤ P.G i xs := fun i => ge_of_tendsto (hGc i)
    (Eventually.of_forall fun k => by
      have := (hx k).1 (Sum.inr (Sum.inl i))
      simp only [MPEC.RS, Sum.elim_inr, Sum.elim_inl] at this
      linarith)
  have hHnn : ∀ i, 0 ≤ P.H i xs := fun i => ge_of_tendsto (hHc i)
    (Eventually.of_forall fun k => by
      have := (hx k).1 (Sum.inr (Sum.inr (Sum.inl i)))
      simp only [MPEC.RS, Sum.elim_inr, Sum.elim_inl] at this
      linarith)
  have hev : ∀ (φ : ℕ → ℝ) (a : ℝ), Tendsto φ atTop (𝓝 a) → ∀ᶠ k in atTop, a ≠ 0 → φ k ≠ 0 := by
    intro φ a h
    by_cases ha : a = 0
    · exact Eventually.of_forall fun _ h' => absurd ha h'
    · exact (h.eventually_ne ha).mono fun _ hk _ => hk
  have e1 : ∀ᶠ k in atTop, ∀ i, P.g i xs ≠ 0 → P.g i (x k) ≠ 0 :=
    eventually_all.mpr fun i => hev _ _ (hgc i)
  have e2 : ∀ᶠ k in atTop, ∀ i, P.G i xs ≠ 0 → P.G i (x k) ≠ 0 :=
    eventually_all.mpr fun i => hev _ _ (hGc i)
  have e3 : ∀ᶠ k in atTop, ∀ i, P.H i xs ≠ 0 → P.H i (x k) ≠ 0 :=
    eventually_all.mpr fun i => hev _ _ (hHc i)
  filter_upwards [e1, e2, e3] with k h1 h2 h3
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · by_contra hne
    exact h1 i hne hi
  · have hG0 : P.G i xs = 0 := by
      by_contra hne
      exact h2 i hne hi
    rcases (hHnn i).eq_or_lt with h | h
    · exact Or.inl ⟨hG0, h.symm⟩
    · exact Or.inr ⟨hG0, h⟩
  · have hH0 : P.H i xs = 0 := by
      by_contra hne
      exact h3 i hne hi
    rcases (hGnn i).eq_or_lt with h | h
    · exact Or.inl ⟨h.symm, hH0⟩
    · exact Or.inr ⟨h, hH0⟩
