-- Prove2me | solution 1 for GlobalTheory.CyclicNormCheck.norm_real_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:41.583128+00:00
-- url     : https://prove2.me/submissions/53d91f25-02da-4201-ad05-405976f924ad

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CyclicNormPrinciple
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AdelicSplittingExamples_LocalConditionsOfGlobal
import Theorems.Thm_GlobalTheory_CyclicNormCheck_norm_of_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
open GlobalTheory GlobalTheory.CyclicNormCheck
namespace GlobalTheory.CyclicNormCheck
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] [Algebra F ℝ]
    [Module.Finite F E] {a : ℝ} (ha : 0 < a) : ∃ y : ℝ ⊗[F] E, Algebra.norm ℝ y = a :=
  norm_of_root (Real.rpow_inv_natCast_pow ha.le (Module.finrank_pos (R := F) (M := E)).ne')
end GlobalTheory.CyclicNormCheck
