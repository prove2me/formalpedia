-- Prove2me | solution 1 for GlobalTheory.UnitLemma.OrthBasis.herm_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:59:07.480464+00:00
-- url     : https://prove2.me/submissions/a7596aa3-1c94-4d0b-adf5-5ebdbcdeabeb

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
theorem _root_.solution (x y : B.A) : B.herm x y 0 = 0 := by
  unfold InvAlg.herm
  simp
end GlobalTheory.UnitLemma.OrthBasis
