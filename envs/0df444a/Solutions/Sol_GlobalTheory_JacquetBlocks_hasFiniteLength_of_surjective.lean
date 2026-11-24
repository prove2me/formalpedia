-- Prove2me | solution 1 for GlobalTheory.JacquetBlocks.hasFiniteLength_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:00:11.825647+00:00
-- url     : https://prove2.me/submissions/207ce747-bd8e-42eb-8e40-7342e98c5af4

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLength
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_of_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.JacquetBlocks
variable {F G H V W : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
namespace GlobalTheory.JacquetBlocks
theorem _root_.solution {ρ : Representation F G V} {σ : Representation F G W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) (h : HasFiniteLength ρ) :
    HasFiniteLength σ :=
  IsFiniteLength.of_surjective h
    (f := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f) hf
end GlobalTheory.JacquetBlocks
