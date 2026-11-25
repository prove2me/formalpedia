-- Prove2me | solution 1 for GlobalTheory.Cartier.ratOf_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:31:32.7116+00:00
-- url     : https://prove2.me/submissions/6ed155cf-f75f-4006-a430-b1839f5ad32c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen

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
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
variable [IsIntegral X]
namespace GlobalTheory.Cartier
theorem _root_.solution {L : LB X} (hL : L.IsLB) (s : L.Sec) (V : X.Opens) [Nonempty V] (c : Γ(X, V))
    (t : ∀ i, Γ(X, V ⊓ L.U i)) :
    ratOf hL s V (fun i => resG X inf_le_left c * t i) = c • ratOf hL s V t := by
  have hm : genericPoint X ∈ V ⊓ L.U (genericChart hL) :=
    ⟨genericPoint_mem V, mem_genericChart hL⟩
  change (X.presheaf.germ _ _ hm).hom (resG X inf_le_left c * t _) * _ = _
  rw [map_mul, germ_resG, mul_assoc]
  rfl
end GlobalTheory.Cartier
