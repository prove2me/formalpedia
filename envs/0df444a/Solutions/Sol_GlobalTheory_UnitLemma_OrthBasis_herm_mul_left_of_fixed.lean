-- Prove2me | solution 1 for GlobalTheory.UnitLemma.OrthBasis.herm_mul_left_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:59:06.119811+00:00
-- url     : https://prove2.me/submissions/98f80abb-531f-40a2-b2a8-80062938c321

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
theorem _root_.solution (x g y z : B.A) (hg : B.σ g = g) :
    B.herm x (g * y) z = B.herm x y (g * z) := by
  unfold InvAlg.herm
  rw [map_mul B.σ, hg]; congr 1; ring
end GlobalTheory.UnitLemma.OrthBasis
