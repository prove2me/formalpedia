-- Prove2me | solution 1 for MatousekLP.SparseRecovery.good_iff_kernel_inter_cone
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T04:35:20.397358+00:00
-- url     : https://prove2.me/submissions/84059979-7ae6-488c-a42b-6111feacad03

import Definitions.Def_MatousekLP_SparseRecovery_BasisPursuit
import Mathlib

open Matrix MatousekLP.SparseRecovery

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : ℕ)
    (z : Fin n → ℝ) (hz : l1Norm z = 1) (hsupp : (supp z).card ≤ r) :
    IsGoodFor (kernel A) z ↔ kernel A ∩ coneAt z = {0} := by
  have hzB : z ∈ crosspolytope n := by simp [crosspolytope, hz]
  constructor
  · intro hgood
    ext v
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hv, t, ht, x, hx, rfl⟩
      rcases ht.lt_or_eq with ht | ht
      · -- x = z + (1/t)·v lies in (ker A + z) ∩ B₁, hence equals z
        have hxmem : x ∈ translate (kernel A) z ∩ crosspolytope n := by
          refine ⟨⟨x - z, ?_, by abel⟩, hx⟩
          have hv' : A *ᵥ (t • (x - z)) = 0 := hv
          rw [mulVec_smul] at hv'
          exact (smul_eq_zero.mp hv').resolve_left ht.ne'
        rw [hgood] at hxmem
        rw [Set.mem_singleton_iff.mp hxmem, sub_self, smul_zero]
      · rw [← ht, zero_smul]
    · rintro rfl
      exact ⟨by simp [kernel], 0, le_rfl, z, hzB, by simp⟩
  · intro hcone
    ext w
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨l, hl, rfl⟩, hw⟩
      have hl0 : l ∈ kernel A ∩ coneAt z :=
        ⟨hl, 1, zero_le_one, l + z, hw, by simp⟩
      rw [hcone] at hl0
      rw [Set.mem_singleton_iff.mp hl0, zero_add]
    · rintro rfl
      exact ⟨⟨0, by simp [kernel], by simp⟩, hzB⟩
