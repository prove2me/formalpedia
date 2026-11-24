-- Prove2me | solution 1 for GlobalTheory.T.isSelfDual_image_standardLattice_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:16:06.320752+00:00
-- url     : https://prove2.me/submissions/28b99460-5201-43b2-9588-8c6d4c8c2aec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSelfDualImageStandardLatticeUnitary
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSelfDualImageStandardLatticeUnitaryStatement
import Theorems.Thm_GlobalTheory_LatOrb_selfDual_matLat_stdLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K),
    (∀ x, σ (σ x) = x) → (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) K), (g.map σ)ᵀ * g = 1 →
    SelfDual O σ (matLat O g (stdLat O n)) := by
  first | exact @GlobalTheory.LatOrb.selfDual_matLat_stdLat | exact GlobalTheory.LatOrb.selfDual_matLat_stdLat | (intros; apply GlobalTheory.LatOrb.selfDual_matLat_stdLat <;> assumption)
end _root_.GlobalTheory.T
