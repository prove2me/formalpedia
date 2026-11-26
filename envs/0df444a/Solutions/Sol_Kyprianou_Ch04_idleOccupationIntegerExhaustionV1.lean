-- Prove2me | solution 1 for Kyprianou.Ch04.idleOccupationIntegerExhaustionV1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:22:39.992547+00:00
-- url     : https://prove2.me/submissions/13af5479-a2c0-4f98-9088-b062c8d4567d

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem _root_.solution
    (g : Real → ENNReal) (hg : Measurable g) :
    (∫⁻ t in Ici (0 : Real), g t ∂volume) =
      ⨆ n : Nat, ∫⁻ t in Icc (0 : Real) (n : Real), g t ∂volume := by
  have hU : Ici (0 : ℝ) = ⋃ n : ℕ, Icc (0 : ℝ) (n : ℝ) := by
    ext t
    simp only [mem_Ici, mem_iUnion, mem_Icc]
    constructor
    · intro ht
      obtain ⟨n, hn⟩ := exists_nat_ge t
      exact ⟨n, ht, hn⟩
    · rintro ⟨n, h, _⟩; exact h
  have hm : Monotone fun n : ℕ => Icc (0 : ℝ) (n : ℝ) := fun a b h =>
    Icc_subset_Icc le_rfl (Nat.cast_le.2 h)
  rw [hU]
  exact setLIntegral_iUnion_of_directed g hm.directed_le

