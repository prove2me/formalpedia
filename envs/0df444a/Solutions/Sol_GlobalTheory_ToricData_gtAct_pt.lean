-- Prove2me | solution 1 for GlobalTheory.ToricData.gtAct_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:49:55.897378+00:00
-- url     : https://prove2.me/submissions/12752716-bfa3-4f25-a751-ff6b0f4c5963

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ZeroFLeftExt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ToricData
variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable (q : X → (FractionRing K)ˣ) (F : Type) [Field F] [Algebra (FractionRing K) F]
namespace GlobalTheory.ToricData
theorem _root_.solution (O : Type) [CommRing O] [StarRing O] [Module O X] (h) (a : O) (t t') :
    GtAct (toricOAct q O h) a (pt q F t) (pt q F t') ↔
      ∀ χ : X, t' (Multiplicative.ofAdd χ) = t (Multiplicative.ofAdd (star a • χ)) := by
  refine (and_iff_right (toUnit_unique _ _)).trans ⟨fun H χ => ?_, fun H u _ hu (χ : X) => ?_⟩
  · have hc := H (cg _ _ 1) (cg_isGen _ _ 1)
      (corr_of_isConst ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)) (isConst_oneGen _)) χ
    have e := eq_of_corr
      (isConst_mulGen (pt_isConst q F t (star a • χ)) ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)))
      (pt_isConst q F t' χ) hc
    exact (unitOn_inj.1 ((_root_.mul_one _).symm.trans e)).symm
  · exact corr_of_isConst
      ((isConst_mulGen (pt_isConst q F t (star a • χ))
        ((isConst_pullGen (isConst_one_of_zero2 q u hu) _).of_eq (map_one _))).of_eq
        ((_root_.mul_one _).trans (congrArg unitOn (H χ).symm)))
      (pt_isConst q F t' χ)
end GlobalTheory.ToricData
