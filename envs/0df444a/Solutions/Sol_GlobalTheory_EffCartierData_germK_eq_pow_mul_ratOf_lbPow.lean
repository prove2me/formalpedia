-- Prove2me | solution 1 for GlobalTheory.EffCartierData.germK_eq_pow_mul_ratOf_lbPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:45:05.494341+00:00
-- url     : https://prove2.me/submissions/5ab32095-1d2d-432d-a808-b49423b7f358

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_Cartier_IsRegularSec_secPow
import Theorems.Thm_GlobalTheory_Cartier_germK_eq_mul_ratOf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier
open GlobalTheory.EffCartierData
variable {X Y Z : Scheme.{0}}
variable (D D' : EffCartierData X)
variable [IsIntegral X]
namespace GlobalTheory.EffCartierData
theorem _root_.solution (n : ℕ) (V : X.Opens) [Nonempty V]
    {t : ∀ j, Γ(X, V ⊓ (lbPow D.lb n).U j)} (ht : t ∈ secOn (lbPow D.lb n) V) (j : PUnit → D.ι)
    [hj : Nonempty (V ⊓ (lbPow D.lb n).U j : X.Opens)] :
    (X.germToFunctionField (V ⊓ (lbPow D.lb n).U j)).hom (t j) =
      (X.germToFunctionField (V ⊓ (lbPow D.lb n).U j)).hom
        (resG X (inf_le_right.trans (lbPow_U D.lb n j).le) (D.f (j ⟨⟩))) ^ n *
        ratOf (D.isLB_lbPow n) (secPow D.canonical n) V t := by
  refine (@germK_eq_mul_ratOf _ _ _ (D.isLB_lbPow n) _ (D.isRegularSec_canonical.secPow n) V _ _
    ht j hj).trans (congrArg (· * _) ?_)
  exact (congrArg _ ((map_pow (resG X _) _ n).trans (congrArg (· ^ n) (resG_resG _ _ _)))).trans
    (map_pow _ _ n)
end GlobalTheory.EffCartierData
