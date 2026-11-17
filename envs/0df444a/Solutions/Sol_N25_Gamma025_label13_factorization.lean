-- Prove2me | solution 1 for N25.Gamma025_label13_factorization
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:00.794585+00:00
-- url     : https://prove2.me/submissions/09e105a0-bb67-4e47-b549-eb175a22c9f5

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_level25_subgroup_membership

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

open CongruenceSubgroup

namespace N25

/-- The five powers of a label-thirteen representative exhaust Gamma0 modulo GammaH. -/
theorem _root_.solution (T : Gamma0 25)
    (hT : CohCarrier.gamma0Units 25 T = (ZMod.unitOfCoprime 13 (by decide))⁻¹)
    (B : Gamma0 25) :
    ∃ k : Fin 5, ∃ C : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      C ∈ CohCarrier.GammaH 25 N25.H25 ∧
        (B : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
          C * (T : Matrix.SpecialLinearGroup (Fin 2) ℤ) ^ k.val := by
  have hf : ∀ u : (ZMod 25)ˣ, ∃ k : Fin 5,
      (((u * (ZMod.unitOfCoprime 13 (by decide)) ^ k.val : (ZMod 25)ˣ) : ZMod 25) = 1 ∨
       ((u * (ZMod.unitOfCoprime 13 (by decide)) ^ k.val : (ZMod 25)ˣ) : ZMod 25) = 7 ∨
       ((u * (ZMod.unitOfCoprime 13 (by decide)) ^ k.val : (ZMod 25)ˣ) : ZMod 25) = 18 ∨
       ((u * (ZMod.unitOfCoprime 13 (by decide)) ^ k.val : (ZMod 25)ˣ) : ZMod 25) = 24) := by
    decide +kernel
  obtain ⟨k, hk⟩ := hf (CohCarrier.gamma0Units 25 B)
  let C : Gamma0 25 := B * (T ^ k.val)⁻¹
  have hC : CohCarrier.gamma0Units 25 C ∈ N25.H25 := by
    dsimp only [C]
    rw [map_mul, map_inv, map_pow, hT, inv_pow, inv_inv]
    rw [N25.level25_subgroup_membership]
    exact hk
  refine ⟨k, C, ⟨C, hC, rfl⟩, ?_⟩
  change (B : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
    ((B * (T ^ k.val)⁻¹) * T ^ k.val : Gamma0 25)
  simp

end N25
