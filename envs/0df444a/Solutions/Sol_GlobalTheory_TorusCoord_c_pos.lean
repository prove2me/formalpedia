-- Prove2me | solution 1 for GlobalTheory.TorusCoord.c_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:25.024939+00:00
-- url     : https://prove2.me/submissions/8679b9ba-2c82-4c25-9bc0-f3be6d728951

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsTorusCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
open scoped ComplexConjugate
open GlobalTheory
open GlobalTheory.TorusCoord
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.TorusCoord
namespace _root_.GlobalTheory.TorusCoord
theorem _root_.solution (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (τ : X.Ψ) : 0 < X.c τ := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.c
  exact mul_pos two_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr X.ξ0_ne))
end _root_.GlobalTheory.TorusCoord
end GlobalTheory.TorusCoord
