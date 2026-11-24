-- Prove2me | solution 1 for GlobalTheory.cm_discr_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:35:24.468748+00:00
-- url     : https://prove2.me/submissions/7be79f1b-64f9-4c03-b2bd-6b9a7edcb608

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SubMemDifferentIdeal
import Theorems.Thm_GlobalTheory_CMDiscrSq_differentIdeal_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open NumberField Module Matrix
open scoped ENNReal
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [StarRing E] [Algebra F E], _root_.Formalism.BasicNotions.CMData F E → |discr E| = discr F ^ 2 ∧
      Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F))) =
        (discr F).natAbs ^ 2 := by
  intro F E _ _ _ _ _ _ h
  have hd := _root_.GlobalTheory.CMDiscrSq.differentIdeal_eq_top h
  have hE := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)
  rw [hd, Ideal.absNorm_top, one_mul, h.deg2] at hE
  refine ⟨?_, ?_⟩
  · rw [Int.abs_eq_natAbs, hE]
    push_cast
    exact sq_abs _
  · have hmul := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)
    rw [hd, Ideal.top_mul] at hmul
    rw [← hmul, absNorm_differentIdeal E (𝓞 E), hE]
end _root_.GlobalTheory
