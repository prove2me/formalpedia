-- Prove2me | solution 1 for KnodelPrimeCordial.cyclic_case_mod_10_label_surjective__p2m_6dfc39c6_04b4_4470_a7a0_9be6cdfdbf5c_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:47:31.309476+00:00
-- url     : https://prove2.me/submissions/d449fa92-4e7a-4420-84ee-90eb7cc1301b

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_labelF_prefix_surjective__p2m_8e730630_f726_4c62_b7a1_a47217416d93_a1
import Theorems.Thm_KnodelPrimeCordial_labelF_tail_surjective__p2m_8e730630_f726_4c62_b7a1_a47217416d93_a1

theorem solution
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 10) :
    ∀ y : ℕ, y ∈ Set.Icc 1 n →
      ∃ i : Fin n,
        (if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val) = y := by
  intro y hy
  have hylo : 1 ≤ y := (Set.mem_Icc.mp hy).1
  have hyhi : y ≤ n := (Set.mem_Icc.mp hy).2
  let q := n / 12
  have hn' : n = 12 * q + 10 := by
    dsimp [q]
    calc
      n = n % 12 + 12 * (n / 12) := (Nat.mod_add_div n 12).symm
      _ = 12 * (n / 12) + 10 := by rw [hmod]; omega
  have hnsub : n - 3 = 12 * q + 7 := by rw [hn']; omega
  by_cases hlow : y ≤ 12 * q
  · obtain ⟨i, hi, hlabel⟩ :=
      KnodelPrimeCordial.labelF_prefix_surjective__p2m_8e730630_f726_4c62_b7a1_a47217416d93_a1
        q y ⟨hylo, hlow⟩
    have hin : i < n := by rw [hn']; omega
    let j : Fin n := ⟨i, hin⟩
    refine ⟨j, ?_⟩
    have hne : i ≠ 12 * q + 7 := by omega
    simpa [j, hnsub, hne] using hlabel
  · have hhigh : 12 * q < y := by omega
    obtain ⟨i, hi, hlabel⟩ :=
      KnodelPrimeCordial.labelF_tail_surjective__p2m_8e730630_f726_4c62_b7a1_a47217416d93_a1
        q y hhigh (by rw [hn'] at hyhi; exact hyhi)
    have hin : i < n := by rw [hn']; omega
    let j : Fin n := ⟨i, hin⟩
    refine ⟨j, ?_⟩
    simpa [j, hnsub] using hlabel
