-- Prove2me | solution 1 for GlobalTheory.PDiv.fibreRank_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:58:32.481107+00:00
-- url     : https://prove2.me/submissions/3b3018cf-1b96-47c4-9184-2c16ec9a0190

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PointsGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanEqTopOfFinrankFibreEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerCounitAlgHomBaseChangeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Theorems.Thm_GlobalTheory_PDiv_fibreRank_comp_of_surjective
import Theorems.Thm_GlobalTheory_PDiv_fibreRank_equiv_comp
import Theorems.Thm_GlobalTheory_DualFibreRank_finrank_dual_and_range_dualMap_baseChange


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
variable [Module.Finite O M] [Module.Projective O M] [Module.Finite O N] [Module.Projective O N]
namespace GlobalTheory.PDiv
theorem _root_.solution (f : M →ₗ[O] N) (q : PrimeSpectrum O) :
    fibreRank (CartierDual.transpose f) q = fibreRank f q := by
  have h : CartierDual.transpose f = (CartierDual.toDual O M).symm.toLinearMap ∘ₗ
      (f.dualMap ∘ₗ (CartierDual.toDual O N).toLinearMap) := rfl
  rw [h, fibreRank_equiv_comp, fibreRank_comp_of_surjective _ (CartierDual.toDual O N).surjective]
  exact (GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange O M N _ f).2
end GlobalTheory.PDiv
