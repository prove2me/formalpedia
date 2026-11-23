-- Prove2me | solution 1 for GlobalTheory.Cartier.SecMaps.isGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:50:37.523605+00:00
-- url     : https://prove2.me/submissions/e93c9ed0-afd5-4258-8895-c05b200d46d5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_val_res
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul_right_cancel
import Theorems.Thm_GlobalTheory_Cartier_SecMaps_on

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
namespace GlobalTheory.Cartier
namespace SecMaps
theorem _root_.solution {A B : LB X} {w : LB.Iso A B} {a : A.Sec} {b : B.Sec} (h : SecMaps w a b)
    (ha : IsRegularSec a) : w.IsGen := by
  rintro ⟨p, q⟩ ⟨p', q'⟩
  have hp : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ B.U p := inf_le_left.trans inf_le_left
  have hq : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ A.U q := inf_le_left.trans inf_le_right
  have hp' : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ B.U p' := inf_le_right.trans inf_le_left
  have hq' : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ A.U q' := inf_le_right.trans inf_le_right
  have key : res (le_inf hp hq) (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q))) *
      res (le_inf hq hq') (A.g q q') = res (le_inf hp hp') (B.g p p') *
        res (le_inf hp' hq') (@id (Γ(X, B.U p' ⊓ A.U q')ˣ) (w.s (p', q'))) := by
    refine Units.ext (((ha q').resG hq').mul_right_cancel ?_)
    simp only [Units.val_mul, val_res]
    rw [mul_assoc, mul_assoc, ← sec_compat a q q' hq hq', ← h.on p' q' hp' hq', ← h.on p q hp hq,
      ← sec_compat b p p' hp hp']
  change res (le_inf hp hq) (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q))) =
    res (le_inf hp hp') (B.g p p') * (res (le_inf hq hq') (A.g q q'))⁻¹ *
      res (le_inf hp' hq') (@id (Γ(X, B.U p' ⊓ A.U q')ˣ) (w.s (p', q')))
  rw [mul_right_comm, ← key, mul_inv_cancel_right]
end SecMaps
end GlobalTheory.Cartier
