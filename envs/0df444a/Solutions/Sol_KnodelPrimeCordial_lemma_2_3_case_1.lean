-- Prove2me | solution 1 for KnodelPrimeCordial.lemma_2_3_case_1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-18T02:47:16.002637+00:00
-- url     : https://prove2.me/submissions/8256b0c6-63c5-4dd5-86cd-c38904e14ea2

import Theorems.Thm_KnodelPrimeCordial_labelF_cyc_bijective_mod0
import Theorems.Thm_KnodelPrimeCordial_cyc_label_zero_count_mod0
import Theorems.Thm_KnodelPrimeCordial_cyc_label_one_count_mod0
import Theorems.Thm_KnodelPrimeCordial_cyclic_model
import Theorems.Thm_KnodelPrimeCordial_edge_label_counts_transport__p2m_997a75d7_cde0_465d_99c4_3e69bfa4c2a4_a1

open KnodelPrimeCordial

set_option autoImplicit false

theorem solution (n : ℕ) (hn : 0 < n) (h12 : 12 ∣ n) :
    Set.BijOn (fun i : Fin n ↦ labelF i.val) Set.univ (Set.Icc 1 n) ∧
      (edgesLabelZero (cyc n) (fun i : Fin n ↦ labelF i.val)).card = 3 * n / 4 ∧
      (edgesLabelOne (cyc n) (fun i : Fin n ↦ labelF i.val)).card = 3 * n / 4 ∧
      ∃ g : Fin 2 × Fin (n / 2) → ℕ, (∀ i : Fin n, g (vtx n (by omega) i) = labelF i.val) ∧
        IsPrimeCordialLabeling (knodel 3 n) g := by
  have hbij := labelF_cyc_bijective_mod0 n hn h12
  have hzero := cyc_label_zero_count_mod0 n hn h12
  have hone := cyc_label_one_count_mod0 n hn h12
  refine ⟨hbij, hzero, hone, ?_⟩
  have heven : Even n := even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 12) h12)
  have h8 : 8 ≤ n := le_trans (by decide : 8 ≤ 12) (Nat.le_of_dvd hn h12)
  obtain ⟨hvtx, hadj⟩ := cyclic_model n heven h8
  let e : Fin n ≃ Fin 2 × Fin (n / 2) := Equiv.ofBijective (vtx n (by omega)) hvtx
  let f : Fin n → ℕ := fun i ↦ labelF i.val
  refine ⟨f ∘ e.symm, ?_, ?_⟩
  · intro i
    exact congrArg f (e.symm_apply_apply i)
  · have hcounts :=
      edge_label_counts_transport__p2m_997a75d7_cde0_465d_99c4_3e69bfa4c2a4_a1
        (cyc n) (knodel 3 n) e hadj f
    constructor
    · have he : Set.BijOn e.symm Set.univ Set.univ := e.symm.bijective.bijOn_univ
      have hcomp := hbij.comp he
      have hcard : Fintype.card (Fin 2 × Fin (n / 2)) = n := by
        rw [← Fintype.card_congr e, Fintype.card_fin]
      simpa only [hcard] using hcomp
    · rw [← hcounts.1, ← hcounts.2, hzero, hone]
      norm_num
