-- Prove2me | solution 1 for GlobalTheory.Cyc.FontW.Cpl.tensor_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:25:11.508181+00:00
-- url     : https://prove2.me/submissions/f25d3790-8fea-432b-a599-37eef14d0487

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRight
import Theorems.Thm_GlobalTheory_Cyc_FontW_Cpl_equiv
import Theorems.Thm_GlobalTheory_Cyc_FontW_Cpl_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.FontW
namespace GlobalTheory.Cyc.FontW
namespace Cpl
theorem _root_.solution {l : ℕ} {R P M : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [Module.Free R P] [Module.Finite R P] [AddCommGroup M] [Module R M] (h : Cpl l M) :
    Cpl l (TensorProduct R P M) := by
  classical
  let b := Module.Free.chooseBasis R P
  exact Cpl.equiv ((TensorProduct.equivFinsuppOfBasisLeft b).toAddEquiv.trans
    Finsupp.addEquivFunOnFinite) (h.pi _)
end Cpl
end GlobalTheory.Cyc.FontW
