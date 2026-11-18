-- Prove2me | solution 1 for ManolescuPiccirillo.rasmussenS_unknot
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T15:15:56.721203+00:00
-- url     : https://prove2.me/submissions/15c330e5-c861-4758-948d-e68ed09ee9d5

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD
import Definitions.Def_ManolescuPiccirillo_Kirby
import Definitions.Def_ManolescuPiccirillo_Movie
import Definitions.Def_ManolescuPiccirillo_Lee1
import Definitions.Def_ManolescuPiccirillo_Lee2

namespace MPUnknotAux
open ManolescuPiccirillo

abbrev U : PD := ⟨[]⟩

lemma labels_U : U.labels = ∅ := by
  simp [PD.labels, PD.entries]

lemma numTrue_U (s : U.State) : U.numTrue s = 0 := by
  have key : ∀ t : Fin 0 → Bool, ((List.ofFn t).filter (fun b => b)).length = 0 := by
    intro t; simp
  exact key s

lemma minReps_U (s : U.State) : U.minReps s = ∅ := by
  classical
  apply Finset.subset_empty.mp
  intro x hx
  unfold PD.minReps at hx
  have h := Finset.mem_of_mem_filter x hx
  rw [labels_U] at h
  simp at h

lemma qDeg_U (g : U.LeeGen) : U.qDeg g = 0 := by
  have h1 := numTrue_U g.val.1
  have h2 : U.nPlus = 0 := by simp [PD.nPlus]
  have h3 : U.nMinus = 0 := by simp [PD.nMinus]
  have hE : IsEmpty ↥(U.minReps g.val.1) := by
    refine ⟨fun x => ?_⟩
    have h0 : x.val ∈ (∅ : Finset ℕ) := by rw [← minReps_U g.val.1]; exact x.property
    simp at h0
  unfold PD.qDeg
  rw [h1, h2, h3, Fintype.sum_empty]
  simp

lemma qFilt_top (q : ℤ) (hq : q ≤ 0) : U.qFilt q = ⊤ := by
  ext f
  simp only [Submodule.mem_top, iff_true]
  intro b hb
  rw [qDeg_U] at hb
  exact absurd hb (not_lt.mpr hq)

lemma qFilt_bot (q : ℤ) (hq : 0 < q) : U.qFilt q = ⊥ := by
  ext f
  simp only [Submodule.mem_bot]
  constructor
  · intro hf
    funext b
    exact hf b (by rw [qDeg_U]; exact hq)
  · rintro rfl
    exact (U.qFilt q).zero_mem

lemma HFilt_top (q : ℤ) (hq : q ≤ 0) : U.HFilt q = ⊤ := by
  unfold PD.HFilt
  rw [qFilt_top q hq, Submodule.comap_top, Submodule.map_top, Submodule.range_mkQ]

lemma HFilt_bot (q : ℤ) (hq : 0 < q) : U.HFilt q = ⊥ := by
  unfold PD.HFilt
  rw [qFilt_bot q hq, Submodule.comap_bot, Submodule.ker_subtype, Submodule.map_bot]

lemma classDeg_U (h : U.H0) (hh : h ≠ 0) : U.classDeg h = 0 := by
  unfold PD.classDeg
  have : {q : ℤ | h ∈ U.HFilt q} = Set.Iic 0 := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    constructor
    · intro hm
      by_contra hlt
      rw [HFilt_bot q (lt_of_not_ge hlt), Submodule.mem_bot] at hm
      exact hh hm
    · intro hq
      rw [HFilt_top q hq]; exact Submodule.mem_top
  rw [this, csSup_Iic]

lemma image_sub (S : Set U.H0) (hS : ∀ h ∈ S, h ≠ 0) : U.classDeg '' S ⊆ {0} := by
  rintro _ ⟨h, hmem, rfl⟩
  exact classDeg_U h (hS h hmem)

end MPUnknotAux

open ManolescuPiccirillo in
theorem solution : (⟨[]⟩ : PD).rasmussenS = 0 := by
  have hsub := MPUnknotAux.image_sub {h : (⟨[]⟩ : PD).H0 | h ≠ 0} (fun h hh => hh)
  have hcases := Set.subset_singleton_iff_eq.mp hsub
  have hmax : (⟨[]⟩ : PD).sMax = 0 := by
    unfold PD.sMax
    rcases hcases with h | h <;> rw [h]
    · exact Int.csSup_empty
    · exact csSup_singleton 0
  have hmin : (⟨[]⟩ : PD).sMin = 0 := by
    unfold PD.sMin
    rcases hcases with h | h <;> rw [h]
    · exact Int.csInf_empty
    · exact csInf_singleton 0
  unfold PD.rasmussenS
  rw [hmax, hmin]; rfl
