-- Prove2me | solution 1 for MathieuM23.lemma_3_1_riemann_hurwitz
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T10:20:42.214828+00:00
-- url     : https://prove2.me/submissions/22cf1ab1-026f-4ad6-9a2c-6f50ef491922

import Definitions.Def_MathieuM23_Group

open MathieuM23

set_option maxRecDepth 100000 in
theorem solution :
    g₁.cycleType = Multiset.replicate 8 2 ∧ g₂.cycleType = {23} ∧ g₃.cycleType = {23} ∧
      (2 * 4 - 2 : ℤ) = 23 * (2 * 0 - 2) +
        (((g₁.cycleType.sum : ℤ) - g₁.cycleType.card) +
          ((g₂.cycleType.sum : ℤ) - g₂.cycleType.card) +
          ((g₃.cycleType.sum : ℤ) - g₃.cycleType.card)) := by
  have h1 : g₁.cycleType = Multiset.replicate 8 2 := by decide +kernel
  have h2 : g₂.cycleType = {23} := by decide +kernel
  have h3 : g₃.cycleType = {23} := by decide +kernel
  refine ⟨h1, h2, h3, ?_⟩
  rw [h1, h2, h3]
  simp


#print axioms solution
