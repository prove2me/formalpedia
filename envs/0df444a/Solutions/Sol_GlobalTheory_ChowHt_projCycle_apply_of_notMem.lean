-- Prove2me | solution 1 for GlobalTheory.ChowHt.projCycle_apply_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:16:37.698303+00:00
-- url     : https://prove2.me/submissions/3d98b708-4666-4b20-af22-bc003004687c

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
theorem _root_.solution {J Q : Ideal (MvPolynomial (Fin N) k)}
    (h : Q ∉ projComponents J) : projCycle J Q = 0 := by
  rw [projCycle, Finsupp.ofSupportFinite_coe]
  exact dif_neg h
end GlobalTheory.ChowHt
