-- Prove2me | solution 1 for GlobalTheory.EffCartierData.mem_poleSecs_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:45:44.814334+00:00
-- url     : https://prove2.me/submissions/0fcf75f5-bcd5-4137-8a7f-74dbcf73ca4a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange

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
theorem _root_.solution (n : ℕ) (V : X.Opens) [Nonempty V] (h : X.functionField) :
    h ∈ D.poleSecs n V ↔ ∀ (i : D.ι) [Nonempty (V ⊓ D.U i : X.Opens)], ∃ a : Γ(X, V ⊓ D.U i),
      (X.germToFunctionField _).hom a =
        (X.germToFunctionField (V ⊓ D.U i)).hom (resG X inf_le_right (D.f i)) ^ n * h := by
  refine forall₂_congr fun i _ => exists_congr fun a => iff_of_eq (congrArg (fun r => _ = r * h) ?_)
  exact (congrArg _ (map_pow (resG X _) (D.f i) n)).trans (map_pow _ _ n)
end GlobalTheory.EffCartierData
