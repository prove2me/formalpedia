-- Prove2me | solution 1 for GlobalTheory.GaussExt.UnitIdx.finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:11:09.643801+00:00
-- url     : https://prove2.me/submissions/97f7adc9-bdea-4b7e-9263-0b05b8bb4690

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteGaussianExtensionUnitsQuotUnits
import Theorems.Thm_GlobalTheory_GaussExt_UnitIdx_pow_mem_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.GaussExt GlobalTheory.GaussExt.UnitIdx
variable (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
namespace GlobalTheory.GaussExt.UnitIdx
theorem _root_.solution : Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸
    (Units.map (algebraMap (NumberField.RingOfIntegers F)
      (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) := by
  haveI : Group.FG (𝓞 (Ext F))ˣ := Group.fg_iff_monoid_fg.2 inferInstance
  refine CommGroup.finite_of_fg_torsion _ fun q => ?_
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨m, hm, hu⟩ := pow_mem_range F u
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact hu
end GlobalTheory.GaussExt.UnitIdx
