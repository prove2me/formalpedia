-- Prove2me | solution 1 for GlobalTheory.PartialZetaSum.idealOf_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:22:51.321801+00:00
-- url     : https://prove2.me/submissions/2f720767-d373-4327-8cf3-021a6b52de50

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
theorem _root_.solution (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    ClassGroup.mk0 ⟨idealOf 𝔟 b, idealOf_mem 𝔟 b⟩ = (ClassGroup.mk F 𝔟)⁻¹ := by
  rw [← ClassGroup.mk_mk0 F, ← map_inv]
  have hb : (b.1 : F) ≠ 0 := b.2.2
  have h : FractionalIdeal.mk0 F ⟨idealOf 𝔟 b, idealOf_mem 𝔟 b⟩ =
      toPrincipalIdeal (𝓞 F) F (Units.mk0 b.1 hb) * 𝔟⁻¹ := by
    apply Units.ext
    rw [FractionalIdeal.coe_mk0, Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0, idealOf_coe]
  have hp : ClassGroup.mk F (toPrincipalIdeal (𝓞 F) F (Units.mk0 b.1 hb)) = 1 := by
    rw [ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
    exact ⟨⟨_, rfl⟩⟩
  rw [h, map_mul, hp, one_mul]
end GlobalTheory.PartialZetaSum
