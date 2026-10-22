-- Prove2me | solution 1 for IoTFusion.KnownQuality.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T13:27:46.289987+00:00
-- url     : https://prove2.me/submissions/c0c62ad8-2122-4ba6-bf6a-da8ee2bf7ca9

import Mathlib
import Definitions.Def_IoTFusion_KnownQuality_Model
import Theorems.Thm_IoTFusion_KnownQuality_remark_1
import Theorems.Thm_IoTFusion_KnownQuality_lemma_2

open IoTFusion.KnownQuality Filter

theorem solution {n : ℕ} (P : IoTFusion.KnownQuality.Instance n) (hn : 2 ≤ n) (hq : ∀ i, 0 < P.q i)
    (hv : ∀ i j, 0 < P.v i j) (hw : ∀ i j, 0 < P.w i j)
    (hasym : Function.Injective P.q) (s : ℕ → ℝ) :
    ∀ i : Fin n, (longRunContacts P i s).ncard = 1 := by
  intro i
  -- every target is a genuine other sensor
  have hne : ∀ c : Fin n → ℝ, lowArgmin i c ≠ i := by
    intro c
    obtain ⟨j0, hj0⟩ : ∃ j0 : Fin n, j0 ≠ i := by
      by_cases h : i.val = 0
      · exact ⟨⟨1, by omega⟩, fun h' => by simp [Fin.ext_iff] at h'; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h' => by simp [Fin.ext_iff] at h'; omega⟩
    have hS : (Finset.univ.filter (fun j : Fin n => j ≠ i)).Nonempty := ⟨j0, by simp [hj0]⟩
    obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image _ c hS
    have hM : (minimizersExcept i c).Nonempty := by
      refine ⟨m, ?_⟩
      unfold minimizersExcept
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
      exact ⟨hm, fun k hk => hmin k (by simp [hk])⟩
    unfold lowArgmin
    rw [dif_pos hM]
    have hmem := Finset.min'_mem _ hM
    unfold minimizersExcept at hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem.1
  have htne : ∀ k, target P i s k ≠ i := fun k => hne _
  -- existence: some sensor is targeted infinitely often
  have hex : ∃ j, ∃ᶠ k in atTop, target P i s k = j := by
    by_contra h
    have h' : ∀ j, ∀ᶠ k in atTop, target P i s k ≠ j := by
      intro j; by_contra hc; exact h ⟨j, not_eventually.mp hc |>.mono fun k hk => not_not.mp hk⟩
    have := (eventually_all.mpr h').exists
    obtain ⟨k, hk⟩ := this
    exact hk (target P i s k) rfl
  obtain ⟨j, hj⟩ := hex
  have hji : j ≠ i := by
    intro h; subst h
    obtain ⟨k, hk⟩ := hj.exists
    exact htne k hk
  have hjT : j ∈ longRunContacts P i s := (remark_1 P hq hv hw s i j hji).mpr hj
  -- uniqueness: two contacts of different quality are impossible
  have key : ∀ j1 j2 : Fin n, j1 ∈ longRunContacts P i s → j2 ∈ longRunContacts P i s →
      P.q j2 < P.q j1 → False := by
    intro j1 j2 h1 h2 hlt
    have hb := hq j2
    set ε := (P.q j1 / P.q j2 - 1) / 2 with hε
    have hratio : 1 < P.q j1 / P.q j2 := by rw [lt_div_iff₀ hb]; linarith
    have hεpos : 0 < ε := by rw [hε]; linarith
    obtain ⟨ψbar, hψbar⟩ := lemma_2 P hq hv hw ε hεpos
    have hev : ∀ᶠ k in atTop, ψbar < fam P i s k j1 (s k) :=
      h1.2.eventually (eventually_gt_atTop ψbar)
    have hfr : ∃ᶠ k in atTop, target P i s k = j2 :=
      (remark_1 P hq hv hw s i j2 h2.1).mp h2
    obtain ⟨k, hk1, hk2⟩ := (hfr.and_eventually hev).exists
    exact hψbar s i j1 j2 k h1.1 h2.1 hk2 (by rw [hε]; linarith) hk1
  rw [Set.ncard_eq_one]
  refine ⟨j, Set.eq_singleton_iff_unique_mem.mpr ⟨hjT, fun j' hj' => ?_⟩⟩
  by_contra hne'
  have hqne : P.q j' ≠ P.q j := fun h => hne' (hasym h)
  rcases lt_or_gt_of_ne hqne with h | h
  · exact key j j' hjT hj' h
  · exact key j' j hj' hjT h
