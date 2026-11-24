-- Prove2me | solution 1 for GlobalTheory.HostModel.unramified_of_isCoprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:09:43.885017+00:00
-- url     : https://prove2.me/submissions/1423c353-1cfa-4f6c-8ab9-b6aa32ad9908

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Theorems.Thm_GlobalTheory_HostModel_formallyUnramified_of_isCoprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.HostModel
theorem _root_.solution (w₁ w₂ : 𝓞 E)
    (h : IsCoprime (w₁ - IsCMField.ringOfIntegersComplexConj E w₁) (w₂ - IsCMField.ringOfIntegersComplexConj E w₂)) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
  { formallyUnramified := formallyUnramified_of_isCoprime (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)
      (fun b => RingOfIntegers.ext (IsCMField.complexConj_apply_apply E (b : E)))
      (fun b hb => (IsCMField.ringOfIntegersComplexConj_eq_self_iff E b).1 hb) w₁ w₂ h
    finiteType := inferInstance }
end GlobalTheory.HostModel
