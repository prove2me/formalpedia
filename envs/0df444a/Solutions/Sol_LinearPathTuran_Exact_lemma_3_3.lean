-- Prove2me | solution 1 for LinearPathTuran.Exact.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:54:34.134719+00:00
-- url     : https://prove2.me/submissions/f7ff771f-146c-4a77-960c-82b213dab33e

import Mathlib
import Definitions.Def_LinearPathTuran_Exact_DeltaSystem

set_option autoImplicit false
open Finset LinearPathTuran.Exact

theorem solution (k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) {n : ℕ} (𝓕 : Finset (Finset (Fin n)))
    (χ : Fin n → Fin k) (J : Finset (Finset (Fin k))) (hH : IsHomogeneous s 𝓕 χ J)
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
