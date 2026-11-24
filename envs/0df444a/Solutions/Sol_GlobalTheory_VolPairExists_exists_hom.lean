-- Prove2me | solution 1 for GlobalTheory.VolPairExists.exists_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:21:11.016951+00:00
-- url     : https://prove2.me/submissions/79c3ee33-6fa5-4649-883d-8cceef43f336

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LeftInvOfUnitary
import Theorems.Thm_GlobalTheory_VolPairExists_mat_mkU
import Theorems.Thm_GlobalTheory_VolPairExists_mat_injective
import Theorems.Thm_GlobalTheory_VolPairExists_mat_mul
import Theorems.Thm_GlobalTheory_VolPairExists_continuous_mkU
import Theorems.Thm_GlobalTheory_VolPairExists_conj_unitary

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
theorem _root_.solution {Γ : Type} [Group Γ] [TopologicalSpace Γ] (m : Γ → Matrix (Fin n) (Fin n) ℂ)
    (hm : Continuous m) (hmul : ∀ g h, m (g * h) = m g * m h) (hu : ∀ h, (m h)ᴴ * G * m h = G)
    (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hl : L * A = 1) (hr : A * L = 1) :
    ∃ ψ : Γ →* UpqT P Q, Continuous ψ ∧ ∀ h, UpqT.mat (ψ h) = A * m h * L := by
  let f : Γ → UpqT P Q := fun x => mkU (A * m x * L) (conj_unitary hA hr (hu x))
  have hf : ∀ x, UpqT.mat (f x) = A * m x * L := fun x => mat_mkU _ _
  refine ⟨MonoidHom.mk' f fun x y => mat_injective ?_, ?_, fun x => hf x⟩
  · rw [mat_mul, hf, hf, hf, hmul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc L, hl, Matrix.one_mul]
  · show Continuous f
    exact continuous_mkU (fun x => A * m x * L) ((continuous_const.matrix_mul hm).matrix_mul continuous_const)
      (fun x => conj_unitary hA hr (hu x))
end GlobalTheory.VolPairExists
