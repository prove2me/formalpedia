-- Prove2me | solution 1 for GlobalTheory.InertCompletion.continuous_of_valued_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:41:51.613165+00:00
-- url     : https://prove2.me/submissions/6cde2012-07c5-4281-97f1-833ab58b8f5c

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldAdicCompletionTensorOfInert
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsRingEquivTensorInertAdicCompletion
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.InertCompletion
namespace GlobalTheory.InertCompletion
theorem _root_.solution {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (σ : P.adicCompletion E →+* P.adicCompletion E) (h : ∀ x, Valued.v (σ x) = Valued.v x) :
    Continuous σ := by
  refine (AddMonoidHomClass.isometry_of_norm σ fun x => ?_).continuous
  exact le_antisymm (Valued.toNormedField.norm_le_iff.2 (h x).le) (Valued.toNormedField.norm_le_iff.2 (h x).ge)
end GlobalTheory.InertCompletion
