-- Prove2me | solution 1 for GlobalTheory.PartialZetaSum.idealOf_eq_of_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:22:52.374421+00:00
-- url     : https://prove2.me/submissions/ba40fcdd-f3c9-4c56-9892-d6f146adc9f8

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
    (h : (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)).r b b') : idealOf 𝔟 b = idealOf 𝔟 b' := by
  obtain ⟨ε, hε⟩ := h
  apply FractionalIdeal.coeIdeal_injective (K := F)
  beta_reduce
  rw [idealOf_coe, idealOf_coe, hε]
  congr 1
  exact FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨ε, by rw [Units.smul_def, Algebra.smul_def]⟩
end GlobalTheory.PartialZetaSum
