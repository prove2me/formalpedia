-- Prove2me | solution 1 for GlobalTheory.VolPairExists.conj_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:18:54.120739+00:00
-- url     : https://prove2.me/submissions/74bd5794-7485-4a92-8496-bd741c291f82

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LeftInvOfUnitary
import Theorems.Thm_GlobalTheory_VolPairExists_conj_frame

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
theorem _root_.solution (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hr : A * L = 1) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : gᴴ * G * g = G) : (A * g * L)ᴴ * Formalism.UG.Jpq P Q * (A * g * L) = Formalism.UG.Jpq P Q := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have h1 : Lᴴ * (gᴴ * Aᴴ) * Formalism.UG.Jpq P Q * (A * g * L) =
      Lᴴ * (gᴴ * (Aᴴ * Formalism.UG.Jpq P Q * A) * g) * L := by
    simp only [Matrix.mul_assoc]
  rw [h1, hA, hg, conj_frame hA hr]
end GlobalTheory.VolPairExists
