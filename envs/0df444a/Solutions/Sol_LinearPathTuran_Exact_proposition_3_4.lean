-- Prove2me | solution 1 for LinearPathTuran.Exact.proposition_3_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:55:00.997898+00:00
-- url     : https://prove2.me/submissions/33450447-b081-4f47-a0ea-3c7d7f83472c

import Mathlib
import Definitions.Def_LinearPathTuran_Exact_DeltaSystem

set_option autoImplicit false
open Finset LinearPathTuran.Exact

theorem lpt_filter_card_one (k s : ℕ) {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (χ : Fin n → Fin k)
    (J : Finset (Finset (Fin k))) (hH : IsHomogeneous s 𝓕 χ J)
    (D : Finset (Fin k)) (hD : ∀ B ∈ J, ¬ D ⊆ B) (F : Finset (Fin n)) (hF : F ∈ 𝓕) :
    #(𝓕.filter (fun F' => F.filter (fun v => χ v ∈ D) ⊆ F')) = 1 := by
  obtain ⟨hpart, hJne, hJim, hJcap, hstar⟩ := hH
  rw [Finset.card_eq_one]
  refine ⟨F, ?_⟩
  ext F'
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hF', hsub⟩
    by_contra hne
    have hmem : F ∩ F' ∈ interStruct 𝓕 F :=
      Finset.mem_image.mpr ⟨F', Finset.mem_erase.mpr ⟨hne, hF'⟩, rfl⟩
    have hpat : pattern χ (F ∩ F') ∈ J := by
      rw [← hJim F hF]; exact Finset.mem_image_of_mem _ hmem
    apply hD _ hpat
    intro i hi
    have h1 := hpart F hF i
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < #(F.filter (fun v => χ v = i)))
    rw [Finset.mem_filter] at hv
    refine Finset.mem_image.mpr ⟨v, Finset.mem_inter.mpr ⟨hv.1, hsub ?_⟩, hv.2⟩
    exact Finset.mem_filter.mpr ⟨hv.1, by rw [hv.2]; exact hi⟩
  · rintro rfl
    exact ⟨hF, fun x hx => (Finset.mem_filter.mp hx).1⟩

theorem solution (k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (χ : Fin n → Fin k) (J : Finset (Finset (Fin k)))
    (hH : IsHomogeneous s 𝓕 χ J) (p : ℕ) (hp : rank J = p) :
    #𝓕 ≤ n.choose p := by
  have hHc := hH
  obtain ⟨hpart, hJne, hJim, hJcap, hstar⟩ := hH
  -- a witness D of size p with no member of J containing it
  have hne : {d | ∃ D : Finset (Fin k), #D = d ∧ ∀ B ∈ J, ¬ D ⊆ B}.Nonempty := by
    refine ⟨k, Finset.univ, by simp, fun B hB hsub => ?_⟩
    exact hJne B hB (Finset.univ_subset_iff.mp hsub)
  have hmem := Nat.sInf_mem hne
  unfold rank at hp
  rw [hp] at hmem
  obtain ⟨D, hDc, hDJ⟩ := hmem
  -- the map F ↦ F[D]
  have hcard : ∀ F ∈ 𝓕, #(F.filter (fun v => χ v ∈ D)) = p := by
    intro F hF
    rw [Finset.card_eq_sum_card_fiberwise (f := χ) (s := F.filter (fun v => χ v ∈ D)) (t := D)
      (fun v hv => (Finset.mem_filter.mp hv).2)]
    rw [← hDc, Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have : (F.filter (fun v => χ v ∈ D)).filter (fun v => χ v = i) = F.filter (fun v => χ v = i) := by
      ext v
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨a, _⟩, c⟩; exact ⟨a, c⟩
      · rintro ⟨a, c⟩; exact ⟨⟨a, by rw [c]; exact hi⟩, c⟩
    rw [this]
    exact hpart F hF i
  have hinj : Set.InjOn (fun F : Finset (Fin n) => F.filter (fun v => χ v ∈ D)) (𝓕 : Set (Finset (Fin n))) := by
    intro F1 h1 F2 h2 heq
    have hc := lpt_filter_card_one k s 𝓕 χ J hHc D hDJ F1 h1
    rw [Finset.card_eq_one] at hc
    obtain ⟨G, hG⟩ := hc
    have a1 : F1 ∈ 𝓕.filter (fun F' => F1.filter (fun v => χ v ∈ D) ⊆ F') := by
      rw [Finset.mem_filter]; exact ⟨h1, fun x hx => (Finset.mem_filter.mp hx).1⟩
    have a2 : F2 ∈ 𝓕.filter (fun F' => F1.filter (fun v => χ v ∈ D) ⊆ F') := by
      rw [Finset.mem_filter]
      refine ⟨h2, ?_⟩
      simp only at heq
      rw [heq]; exact fun x hx => (Finset.mem_filter.mp hx).1
    rw [hG, Finset.mem_singleton] at a1 a2
    rw [a1, a2]
  calc #𝓕 ≤ #(Finset.powersetCard p (Finset.univ : Finset (Fin n))) := by
        apply Finset.card_le_card_of_injOn (fun F : Finset (Fin n) => F.filter (fun v => χ v ∈ D))
        · intro F hF
          rw [Finset.mem_coe, Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ _, hcard F hF⟩
        · exact hinj
    _ = n.choose p := by simp
