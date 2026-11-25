-- Prove2me | solution 1 for GlobalTheory.ChowHt.mem_support_projCycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:47:33.354218+00:00
-- url     : https://prove2.me/submissions/8c981eaf-377c-40b7-86b7-464299a37ede

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallAevalLineVanishingIdealIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ProjPointIdealMemProjComponentsOfIsProjPureDim
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsMultiHomogeneousFixFirstBlock_b3ed944b577456bc
import Theorems.Thm_GlobalTheory_ChowHt_localLength_ne_zero
import Theorems.Thm_GlobalTheory_ChowHt_cast_projCycle_apply
import Theorems.Thm_GlobalTheory_ChowHt_projCycle_apply_of_notMem

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
theorem _root_.solution {J Q : Ideal (MvPolynomial (Fin N) k)} :
    Q ∈ (projCycle J).support ↔ Q ∈ projComponents J := by
  rw [Finsupp.mem_support_iff]
  refine ⟨fun h => by_contra fun h' => h (projCycle_apply_of_notMem h'), fun h h0 => ?_⟩
  haveI : Q.IsPrime := h.1.1.1
  refine localLength_ne_zero h.1.1.2 ?_
  rw [← cast_projCycle_apply h, h0, Nat.cast_zero]
end GlobalTheory.ChowHt
