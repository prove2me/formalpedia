-- Prove2me | solution 1 for GlobalTheory.PDiv.fibreRank_comp_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:47:53.509299+00:00
-- url     : https://prove2.me/submissions/b50e5eb6-8c8b-466d-a457-21814fb675cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PointsGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanEqTopOfFinrankFibreEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerCounitAlgHomBaseChangeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective

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
theorem _root_.solution (g : N →ₗ[O] P) {f : M →ₗ[O] N}
    (hf : Function.Surjective f) (q : PrimeSpectrum O) :
    fibreRank (g ∘ₗ f) q = fibreRank g q := by
  rw [fibreRank, LinearMap.baseChange_comp, LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.2 (LinearMap.lTensor_surjective _ hf)
end GlobalTheory.PDiv
