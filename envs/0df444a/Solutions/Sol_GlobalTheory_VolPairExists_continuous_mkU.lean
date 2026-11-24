-- Prove2me | solution 1 for GlobalTheory.VolPairExists.continuous_mkU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:11:33.377884+00:00
-- url     : https://prove2.me/submissions/4c3a6981-7ee8-4223-a18d-8bac60f4e02a

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
namespace GlobalTheory.VolPairExists
theorem _root_.solution {X : Type} [TopologicalSpace X] (f : X → Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)
    (hf : Continuous f) (h : ∀ x, (f x)ᴴ * Formalism.UG.Jpq P Q * f x = Formalism.UG.Jpq P Q) :
    Continuous fun x => mkU (f x) (h x) := by
  have hinv : Continuous fun x => Formalism.UG.Jpq P Q * (f x)ᴴ * Formalism.UG.Jpq P Q :=
    (continuous_const.matrix_mul hf.matrix_conjTranspose).matrix_mul continuous_const
  unfold mkU
  refine (Units.continuous_iff.2 ⟨?_, ?_⟩).subtype_mk _
  · exact hf
  · exact hinv
end GlobalTheory.VolPairExists
