-- Prove2me | solution 1 for GlobalTheory.VolPairExists.read_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:36:10.415311+00:00
-- url     : https://prove2.me/submissions/91c371c8-565a-465e-8def-625604eb3577

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LeftInvOfUnitary
import Theorems.Thm_GlobalTheory_VolPairExists_mat_injective
import Theorems.Thm_GlobalTheory_VolPairExists_mat_mul
import Theorems.Thm_GlobalTheory_VolPairExists_mat_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory GlobalTheory.VolPairExists
variable {P Q : ℕ}
variable {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ}
variable {A A' : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ} {L : Matrix (Fin n) (Fin P ⊕ Fin Q) ℂ}
namespace GlobalTheory.VolPairExists
theorem _root_.solution (hl : L * A = 1) (hr : A * L = 1) (u : UpqT P Q) (hu : UpqT.mat u = A' * L)
    {g : Matrix (Fin n) (Fin n) ℂ} (t : UpqT P Q) (ht : UpqT.mat t = A * g * L) (B : Set (UpqT P Q)) :
    (∃ b ∈ B, UpqT.mat b * A' = A' * g) ↔ t ∈ (fun b => b * u⁻¹) ⁻¹' ((fun b => u * b) ⁻¹' B) := by
  have hA' : A' = UpqT.mat u * A := by rw [hu, Matrix.mul_assoc, hl, Matrix.mul_one]
  have hinv : UpqT.mat u⁻¹ * UpqT.mat u = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
  have key : ∀ b : UpqT P Q, UpqT.mat b * A' = A' * g ↔ b = u * (t * u⁻¹) := by
    intro b
    constructor
    · intro h
      have h2 : UpqT.mat (b * u) = UpqT.mat (u * t) := by
        rw [mat_mul, mat_mul, ht]
        calc UpqT.mat b * UpqT.mat u = UpqT.mat b * A' * L := by rw [hu, Matrix.mul_assoc]
          _ = A' * g * L := by rw [h]
          _ = UpqT.mat u * (A * g * L) := by rw [hA']; simp only [Matrix.mul_assoc]
      have h3 := mat_injective h2
      rw [← mul_assoc, ← h3, mul_inv_cancel_right]
    · rintro rfl
      rw [mat_mul, mat_mul, ht, hA']
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (UpqT.mat u⁻¹), hinv, Matrix.one_mul, hl, Matrix.mul_one]
  simp only [Set.mem_preimage]
  constructor
  · rintro ⟨b, hb, h⟩
    rwa [(key b).1 h] at hb
  · intro h
    exact ⟨_, h, (key _).2 rfl⟩
end GlobalTheory.VolPairExists
