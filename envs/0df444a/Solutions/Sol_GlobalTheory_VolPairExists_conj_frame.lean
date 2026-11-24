-- Prove2me | solution 1 for GlobalTheory.VolPairExists.conj_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:01:25.670816+00:00
-- url     : https://prove2.me/submissions/8dc00aa6-8557-45c7-9745-e032423a0d54

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LeftInvOfUnitary

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
theorem _root_.solution (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hr : A * L = 1) : Lᴴ * G * L = Formalism.UG.Jpq P Q := by
  rw [← hA]
  have h1 : Lᴴ * (Aᴴ * Formalism.UG.Jpq P Q * A) * L = (A * L)ᴴ * Formalism.UG.Jpq P Q * (A * L) := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [h1, hr, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
end GlobalTheory.VolPairExists
