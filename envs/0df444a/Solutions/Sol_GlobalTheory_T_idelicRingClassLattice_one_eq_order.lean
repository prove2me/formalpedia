-- Prove2me | solution 1 for GlobalTheory.T.idelicRingClassLattice_one_eq_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:54:10.985393+00:00
-- url     : https://prove2.me/submissions/7c3560a0-14e7-41eb-8785-685374b87a53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdelicRingClassLatticeOneEqOrder
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdelicRingClassLatticeOneEqOrderStatement
import Theorems.Thm_GlobalTheory_CMVal_HatCap_lattice_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → lattice c 1 = (orderC c : Set E) := by
  first | exact @GlobalTheory.CMVal.HatCap.lattice_one | exact GlobalTheory.CMVal.HatCap.lattice_one | (intros; apply GlobalTheory.CMVal.HatCap.lattice_one <;> assumption)
end _root_.GlobalTheory.T
