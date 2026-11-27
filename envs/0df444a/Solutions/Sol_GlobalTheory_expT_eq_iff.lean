-- Prove2me | solution 1 for GlobalTheory.expT_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:33:27.593132+00:00
-- url     : https://prove2.me/submissions/c993e9cc-2818-4aef-8929-18cf45ba01ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfWeightSum
import Theorems.Thm_GlobalTheory_ExpUniq_sval_diffSec
import Theorems.Thm_GlobalTheory_ExpUniq_eq_of_diffSec
import Theorems.Thm_GlobalTheory_ExpUniq_gs_eq_zero_of_sval
import Theorems.Thm_GlobalTheory_ExpUniq_sec_eq_zero
import Theorems.Thm_GlobalTheory_ExpUniq_expT_diff
import Theorems.Thm_GlobalTheory_ExpUniq_sval_sec_eq_zero
import Theorems.Thm_GlobalTheory_ExpUniq_sval_term_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_isLB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory
open ExpUniq
namespace GlobalTheory
theorem _root_.solution : (AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ k σ σ' f f', U.ExpT (TA V W) k σ f → U.ExpT (TA V W) k σ' f' → (σ = σ' ↔ f = f')) := by
  intro V _ _ _ hV D A G _ _ U W _ _ _ hW k σ σ' f f' h h'
  have := hV.1
  have := hW.1
  have : IsNoetherianRing W := IsNoetherianRing.of_finite V W
  have hI : (IsLocalRing.maximalIdeal V).map (algebraMap V W) ≤ Ideal.jacobson ⊥ :=
    have := hW.2.2.2.2
    IsAdicComplete.le_jacobson_bot _
  have hd := expT_diff h h'
  constructor
  · rintro rfl
    have := D.P.isAb.smooth
    have := D.P.isAb.geomConnected
    refine funext fun α => eq_of_diffSec (sec_eq_zero _ W hI D.P.A _ (DVR.linComb_isLB _ D.P.isLB _ _) _
      fun e Z r a ha z j hj => gs_eq_zero_of_sval D.P.isLB _ r z (fun J hJ => ?_) j hj)
    exact sval_term_eq_zero hd (fun Z r z J hJ => by rw [sval_diffSec _ _ _ hJ, sub_self]) α e r a ha z J hJ
  · rintro rfl
    have := U.semi.smooth
    have := U.semi.geomConnected
    refine eq_of_diffSec (sec_eq_zero _ W hI G _ (DVR.linComb_isLB _ U.P.L.isLB _ _) _
      fun e Z r a ha z j hj => gs_eq_zero_of_sval U.P.L.isLB _ r z (fun J hJ => ?_) j hj)
    exact sval_sec_eq_zero hd (fun α Z r z J hJ => by rw [sval_diffSec _ _ _ hJ, sub_self]) e r a ha z J hJ
end GlobalTheory
