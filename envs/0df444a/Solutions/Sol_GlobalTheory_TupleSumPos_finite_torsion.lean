-- Prove2me | solution 1 for GlobalTheory.TupleSumPos.finite_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:21:42.164023+00:00
-- url     : https://prove2.me/submissions/dcac2319-9e5f-40ec-8095-f6ae7187ba0b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroOnCoset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsGeneratorsLattice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open scoped TensorProduct nonZeroDivisors
open GlobalTheory GlobalTheory.TupleSumPos
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.TupleSumPos
theorem _root_.solution (T : PT E) :
    {v : Vsp T.dim | v ∈ ZSpan.fundamentalDomain T.b ∧ ((5 : ℂ) ^ 2) • v ∈ T.L}.Finite := by
  have hb := (ZSpan.fundamentalDomain_isBounded T.b).smul₀ ((5 : ℂ) ^ 2)
  have hf := ZSpan.setFinite_inter T.b hb
  refine Set.Finite.of_finite_image (f := fun v => ((5 : ℂ) ^ 2) • v) (hf.subset ?_) ?_
  · rintro _ ⟨v, ⟨h1, h2⟩, rfl⟩
    exact ⟨Set.smul_mem_smul_set h1, h2⟩
  · exact (smul_right_injective _ (by norm_num)).injOn
end GlobalTheory.TupleSumPos
