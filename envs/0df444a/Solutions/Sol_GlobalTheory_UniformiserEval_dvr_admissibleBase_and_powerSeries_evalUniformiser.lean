-- Prove2me | solution 1 for GlobalTheory.UniformiserEval.dvr_admissibleBase_and_powerSeries_evalUniformiser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:17:59.033522+00:00
-- url     : https://prove2.me/submissions/3e4b6f96-5064-452d-90ff-da966e6a6e37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsPrincipalIdealRingOfIsLocalization
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_DvrAdmissibleBaseAndPowerSeriesEvalUniformiser
import Theorems.Thm_GlobalTheory_UniformiserEval_translate_X
import Theorems.Thm_GlobalTheory_UniformiserEval_translate_C
import Theorems.Thm_GlobalTheory_UniformiserEval_translate_injective
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_C
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_X
import Theorems.Thm_P2M_GlobalTheory_ChartRing_evFrac__apply_1d354619b41f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ChartRing.evalAdic_C
attribute [local simp] GlobalTheory.ChartRing.evalAdic_X
attribute [local simp] P2M_GlobalTheory_ChartRing_evFrac__apply_1d354619b41f



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UniformiserEval
open GlobalTheory.ChartRing
variable {V : Type} [CommRing V] [IsLocalRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
namespace GlobalTheory.UniformiserEval
theorem _root_.solution : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → IsAdicComplete (IsLocalRing.maximalIdeal V) V → AdmBase V (Ideal.span {ϖ}) ∧ AdmBase (PowerSeries V) (Ideal.span {PowerSeries.X}) ∧ ∃ ev : PowerSeries V →+* V, (∀ x, ev (PowerSeries.C x) = x) ∧ ev PowerSeries.X = ϖ ∧ ∀ (F : Type) [Field F] (i : V →+* F), Function.Injective i → ∃ σ : PowerSeries V →+* PowerSeries F, Function.Injective σ ∧ (∀ x, σ (PowerSeries.C x) = PowerSeries.C (i x)) ∧ σ PowerSeries.X = PowerSeries.C (i ϖ) + PowerSeries.X ∧ ∀ f, PowerSeries.constantCoeff (σ f) = i (ev f) := by
  intro V _ _ _ ϖ hϖ hc
  have hm : ϖ ∈ IsLocalRing.maximalIdeal V := hϖ.not_isUnit
  refine ⟨⟨inferInstance, inferInstance, inferInstance, hϖ.maximalIdeal_eq ▸ hc⟩,
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    (PowerSeries.constantCoeff (R := V)).comp (translate hm : PowerSeries V →+* PowerSeries V),
    fun x => ?_, ?_, fun F _ i hi =>
      ⟨(PowerSeries.map i).comp (translate hm : PowerSeries V →+* PowerSeries V), ?_,
        fun x => ?_, ?_, fun f => ?_⟩⟩
  · simp [translate_C]
  · simp [translate_X]
  · exact (PowerSeries.map_injective i hi).comp (translate_injective hm)
  · simp [translate_C]
  · simp [translate_X]
  · simp only [RingHom.comp_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map]
end GlobalTheory.UniformiserEval
