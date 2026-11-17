-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:11:27.472927+00:00
-- url     : https://prove2.me/submissions/7e053e1e-8e62-4fa4-a163-c2fdb4514bb4

import Mathlib
import Definitions.Def_KnodelPrimeCordial_PrimeCordial
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_label_bijective__p2m_585db7c0_0954_404f_a5c5_92bed9ed7485_a2
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_label_edge_counts__p2m_585db7c0_0954_404f_a5c5_92bed9ed7485_a2

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    KnodelPrimeCordial.PrimeCordial (KnodelPrimeCordial.knodel 3 n) := by
  let f : Fin 2 × Fin (n / 2) → ℕ := fun v =>
    KnodelPrimeCordial.labelF
      (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n)
  have hb :=
    KnodelPrimeCordial.case_mod_6_label_bijective__p2m_585db7c0_0954_404f_a5c5_92bed9ed7485_a2
      n hn h10 hmod
  have hc :=
    KnodelPrimeCordial.case_mod_6_label_edge_counts__p2m_585db7c0_0954_404f_a5c5_92bed9ed7485_a2
      n hn h10 hmod
  have hcard : Fintype.card (Fin 2 × Fin (n / 2)) = n := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    rcases hn with ⟨k, hk⟩
    omega
  change ∃ g, KnodelPrimeCordial.IsPrimeCordialLabeling (KnodelPrimeCordial.knodel 3 n) g
  refine ⟨f, ?_⟩
  unfold KnodelPrimeCordial.IsPrimeCordialLabeling
  constructor
  · simpa [f, hcard] using hb
  · rcases hc with ⟨hz, ho⟩
    simp only [f, hz, ho]
    have hcounts : (3 * n + 2) / 4 = (3 * n - 2) / 4 + 1 := by
      obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 12 * k + 6 := by
        exact ⟨n / 12, by omega⟩
      rw [hk]
      omega
    have hdiff :
        (↑((3 * n - 2) / 4) : ℤ) - ↑((3 * n + 2) / 4) = -1 := by
      rw [hcounts]
      push_cast
      ring
    rw [hdiff]
    norm_num
