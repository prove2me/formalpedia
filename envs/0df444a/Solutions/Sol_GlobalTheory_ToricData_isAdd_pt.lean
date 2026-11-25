-- Prove2me | solution 1 for GlobalTheory.ToricData.isAdd_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:23:59.496897+00:00
-- url     : https://prove2.me/submissions/2be6fe4a-ead4-440f-924d-a89e7ad60f91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ZeroFLeftExt
import Theorems.Thm_GlobalTheory_ToricData_hom_eq_iff
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
theorem _root_.solution (t t' t'') : (pt q F t).IsAdd (pt q F t') (pt q F t'') ↔ t'' = t * t' :=
  (and_iff_right (toUnit_unique _ _)).trans ((forall_congr' fun (χ : X) =>
    (corr_iff_eq
      ((isConst_mulGen (pt_isConst q F t'' χ) (cubAt_isConst q F _ _ _)).of_eq (_root_.mul_one _))
      ((isConst_mulGen (pt_isConst q F t χ) (pt_isConst q F t' χ)).of_eq (unitOn_mul _ _).symm)).trans
      unitOn_inj).trans (hom_eq_iff (t' := t * t')))
end GlobalTheory.ToricData
