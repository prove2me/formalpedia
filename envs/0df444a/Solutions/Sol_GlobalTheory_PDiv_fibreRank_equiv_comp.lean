-- Prove2me | solution 1 for GlobalTheory.PDiv.fibreRank_equiv_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:51:39.611838+00:00
-- url     : https://prove2.me/submissions/68e27271-0a40-482c-8aa1-85bddf92c424

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PointsGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanEqTopOfFinrankFibreEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerCounitAlgHomBaseChangeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Theorems.Thm_GlobalTheory_IsBicharacter_baseChange
import Theorems.Thm_GlobalTheory_IsPerfectBicharacter_baseChange


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
open GlobalTheory GlobalTheory.PDiv
variable {O : Type} [CommRing O]
variable {M N P : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
  [AddCommGroup P] [Module O P]
namespace GlobalTheory.PDiv
theorem _root_.solution (e : N ≃ₗ[O] P) (f : M →ₗ[O] N) (q : PrimeSpectrum O) :
    fibreRank (e.toLinearMap ∘ₗ f) q = fibreRank f q := by
  rw [fibreRank, LinearMap.baseChange_comp, LinearMap.range_comp]
  exact LinearEquiv.finrank_map_eq (e.baseChange O _ N P) _
end GlobalTheory.PDiv
