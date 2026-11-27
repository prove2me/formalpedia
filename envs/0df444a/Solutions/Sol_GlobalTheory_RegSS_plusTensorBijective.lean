-- Prove2me | solution 1 for GlobalTheory.RegSS.plusTensorBijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T06:24:48.410243+00:00
-- url     : https://prove2.me/submissions/9e1b2c82-f7e4-4c6f-b74e-7dc6d8dea11d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleSelfAdjointPartTensorBijective
import Theorems.Thm_GlobalTheory_RegSS_productMap_bijective_of_involution
import Theorems.Thm_GlobalTheory_RegSS_exists_adjEquiv
import Theorems.Thm_GlobalTheory_RegSS_quad_exists_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.RegSS GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
namespace GlobalTheory.RegSS
theorem _root_.solution : PlusTensorBijective := by
  intro F E _ _ _ _ n _ _ σ J γ h hA
  obtain ⟨τ, -, hτ, hE, hP⟩ := exists_adjEquiv h hA
  obtain ⟨b, d, h0, h1, hd, hsq⟩ := quad_exists_basis h.quad
  refine productMap_bijective_of_involution _ τ hτ _ hP b d h0 ?_ hd hsq
  rw [IsScalarTower.toAlgHom_apply, hE, h1, map_neg]
end GlobalTheory.RegSS
