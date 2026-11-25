-- Prove2me | solution 1 for GlobalTheory.TateFree.natCard_pts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:02:30.381656+00:00
-- url     : https://prove2.me/submissions/55f40d7b-f200-486e-867b-8311c7a7f4af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
import Theorems.Thm_GlobalTheory_TateFree_comp_ofId_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.TateFree
variable (O C A : Type) [CommRing O] [Field C] [Algebra O C] [IsIntegrallyClosedIn O C]
  [CommRing A]
variable [IsAlgClosed C] [CharZero C] [HopfAlgebra O A] [Module.Finite O A]
namespace GlobalTheory.TateFree
theorem _root_.solution : Nat.card (A →ₐ[O] O) = finrank C (C ⊗[O] A) := by
  have := etale_of_hopfAlgebra C (C ⊗[O] A)
  rw [Nat.card_congr (Equiv.ofBijective _ (comp_ofId_bijective O C A)),
    Nat.card_congr (AlgHom.liftEquiv O C A C), natCard_algHom_eq_finrank_of_etale]
end GlobalTheory.TateFree
