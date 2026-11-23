-- Prove2me | solution 1 for GlobalTheory.HostModel.trForm_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:38.676463+00:00
-- url     : https://prove2.me/submissions/4e0bb70e-b4ff-4bb1-b7a9-46a7c2799a1e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate

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
open scoped TensorProduct ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.HostModel
theorem _root_.solution (H : Host E) {y : 𝓞 E} (hy : y ≠ 0) : 0 < trForm H y y := by
  have h : (0 : ℝ) < (trForm H y y : ℝ) := by
    rw [trForm_self_eq_sum]
    refine Finset.sum_pos (fun τ _ => pow_pos (norm_pos_iff.2 ?_) 2) Finset.univ_nonempty
    exact (map_ne_zero τ).2 (RingOfIntegers.coe_ne_zero_iff.2 hy)
  exact_mod_cast h
end GlobalTheory.HostModel
