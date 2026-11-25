-- Prove2me | solution 1 for GlobalTheory.EffCartierData.germK_eq_pow_mul_ratOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:42:47.306682+00:00
-- url     : https://prove2.me/submissions/55695881-411c-45d9-9402-c5c6cc675907

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
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
    {t : ∀ i, Γ(X, V ⊓ (D.nsmul n).lb.U i)} (ht : t ∈ secOn (D.nsmul n).lb V) (i : D.ι)
    [hi : Nonempty (V ⊓ D.U i : X.Opens)] :
    (X.germToFunctionField (V ⊓ D.U i)).hom (t i) =
      (X.germToFunctionField (V ⊓ D.U i)).hom (resG X inf_le_right (D.f i)) ^ n *
        ratOf (D.nsmul n).isLB_lb (D.nsmul n).canonical V t := by
  refine (@germK_eq_mul_ratOf _ _ _ (D.nsmul n).isLB_lb _ (D.nsmul n).isRegularSec_canonical V _ _
    ht i hi).trans (congrArg (· * _) ?_)
  exact (congrArg _ (map_pow (resG X _) (D.f i) n)).trans (map_pow _ _ n)
end GlobalTheory.EffCartierData
