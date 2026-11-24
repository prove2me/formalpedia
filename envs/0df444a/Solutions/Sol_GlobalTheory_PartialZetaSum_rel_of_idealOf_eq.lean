-- Prove2me | solution 1 for GlobalTheory.PartialZetaSum.rel_of_idealOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:19:45.201994+00:00
-- url     : https://prove2.me/submissions/bbfdf869-b86e-4974-bb25-2e683d8d7b97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumAbsNormCpowUnitClassesPartialZeta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.PartialZetaSum
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.PartialZetaSum
theorem _root_.solution (𝔟 : Frac F) {b b' : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)}
    (h : idealOf 𝔟 b = idealOf 𝔟 b') : (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)).r b b' := by
  have h2 : FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 = FractionalIdeal.spanSingleton (𝓞 F)⁰ b'.1 := by
    rw [span_eq, span_eq, h]
  obtain ⟨z, hz⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.1 h2
  exact ⟨z, by rw [← hz, Units.smul_def, Algebra.smul_def]⟩
end GlobalTheory.PartialZetaSum
