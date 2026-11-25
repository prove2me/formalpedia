-- Prove2me | solution 1 for GlobalTheory.ChowHt.cast_projCycle_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:15:50.4299+00:00
-- url     : https://prove2.me/submissions/e6e2147a-75aa-49bf-9da9-e6a9ce6fc035

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallAevalLineVanishingIdealIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ProjPointIdealMemProjComponentsOfIsProjPureDim
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsMultiHomogeneousFixFirstBlock_b3ed944b577456bc
import Theorems.Thm_GlobalTheory_ChowHt_localLength_ne_top
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ChowHt
variable {k : Type} [Field k] {N : ℕ}
namespace GlobalTheory.ChowHt
theorem _root_.solution {J Q : Ideal (MvPolynomial (Fin N) k)} [Q.IsPrime]
    (h : Q ∈ projComponents J) : (projCycle J Q : ℕ∞) = localLength J Q := by
  rw [projCycle, Finsupp.ofSupportFinite_coe]
  simp only [dif_pos h]
  exact ENat.coe_toNat (localLength_ne_top h.1)
end GlobalTheory.ChowHt
