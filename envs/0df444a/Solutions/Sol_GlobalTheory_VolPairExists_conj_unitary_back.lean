-- Prove2me | solution 1 for GlobalTheory.VolPairExists.conj_unitary_back
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:35:52.30025+00:00
-- url     : https://prove2.me/submissions/b1c310bd-9d5b-4d78-825e-a990d7069331

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LeftInvOfUnitary
import Theorems.Thm_GlobalTheory_VolPairExists_mat_unitary
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
theorem _root_.solution (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hr : A * L = 1) (b : UpqT P Q) :
    (L * UpqT.mat b * A)ᴴ * G * (L * UpqT.mat b * A) = G := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have h1 : Aᴴ * ((UpqT.mat b)ᴴ * Lᴴ) * G * (L * UpqT.mat b * A) =
      Aᴴ * ((UpqT.mat b)ᴴ * (Lᴴ * G * L) * UpqT.mat b) * A := by
    simp only [Matrix.mul_assoc]
  rw [h1, conj_frame hA hr, mat_unitary, hA]
end GlobalTheory.VolPairExists
