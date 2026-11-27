-- Prove2me | solution 1 for GlobalTheory.VolPairExists.change_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:35:48.945372+00:00
-- url     : https://prove2.me/submissions/a1f6f454-45c6-406c-a705-bb5a08fc2526

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
theorem _root_.solution (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hr : A * L = 1) (hA' : A'ᴴ * Formalism.UG.Jpq P Q * A' = G) :
    (A' * L)ᴴ * Formalism.UG.Jpq P Q * (A' * L) = Formalism.UG.Jpq P Q := by
  rw [Matrix.conjTranspose_mul]
  have h1 : Lᴴ * A'ᴴ * Formalism.UG.Jpq P Q * (A' * L) = Lᴴ * (A'ᴴ * Formalism.UG.Jpq P Q * A') * L := by
    simp only [Matrix.mul_assoc]
  rw [h1, hA', conj_frame hA hr]
end GlobalTheory.VolPairExists
