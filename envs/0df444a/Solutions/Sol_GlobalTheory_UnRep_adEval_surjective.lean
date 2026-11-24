-- Prove2me | solution 1 for GlobalTheory.UnRep.adEval_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:45:01.433532+00:00
-- url     : https://prove2.me/submissions/021cb79b-c14c-4dd8-9205-afdc0b0a9d5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep
namespace GlobalTheory.UnRep
theorem _root_.solution (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Function.Surjective (adEval F v) := by
  classical
  intro x
  refine ⟨⟨Pi.single v x, ?_⟩, ?_⟩
  · filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw
    rw [Pi.single_eq_of_ne hw]
    exact zero_mem _
  · exact Pi.single_eq_same v x
end GlobalTheory.UnRep
