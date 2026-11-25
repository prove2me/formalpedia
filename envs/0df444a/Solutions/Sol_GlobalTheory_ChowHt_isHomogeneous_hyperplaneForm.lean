-- Prove2me | solution 1 for GlobalTheory.ChowHt.isHomogeneous_hyperplaneForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:29:54.676014+00:00
-- url     : https://prove2.me/submissions/1b64fb1e-ed4b-4002-a927-6baccc89281d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallAevalLineVanishingIdealIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ProjPointIdealMemProjComponentsOfIsProjPureDim
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsMultiHomogeneousFixFirstBlock_b3ed944b577456bc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ChowHt
variable {k : Type} [Field k] {N : ℕ}
namespace GlobalTheory.ChowHt
theorem _root_.solution (u : Fin N → k) : (hyperplaneForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X k j).C_mul _
end GlobalTheory.ChowHt
