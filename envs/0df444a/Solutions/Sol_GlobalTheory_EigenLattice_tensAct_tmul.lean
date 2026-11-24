-- Prove2me | solution 1 for GlobalTheory.EigenLattice.tensAct_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:25:06.334905+00:00
-- url     : https://prove2.me/submissions/18bdc75c-cbea-4aff-abe5-3b95bf1d5c66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralThird

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.EigenLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H]
namespace GlobalTheory.EigenLattice
theorem _root_.solution (ρ : orderC c →+* Module.End O H) (a : orderC c) (x : O) :
    tensAct ρ (a ⊗ₜ x) = x • ρ a := by
  rfl
end GlobalTheory.EigenLattice
