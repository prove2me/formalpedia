-- Prove2me | solution 1 for GlobalTheory.UnitLemma.OrthBasis.herm_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:59:05.410473+00:00
-- url     : https://prove2.me/submissions/3b9f3379-a3a2-4330-a029-65a4af322632

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermBasisOrthonormal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.OrthBasis
open GlobalTheory.UnitLemma
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.UnitLemma.OrthBasis
theorem _root_.solution (x y z₁ z₂ : B.A) : B.herm x y (z₁ + z₂) = B.herm x y z₁ + B.herm x y z₂ := by
  unfold InvAlg.herm
  rw [map_add, mul_add, map_add]
end GlobalTheory.UnitLemma.OrthBasis
