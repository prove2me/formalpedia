-- Prove2me | solution 1 for GlobalTheory.TorusCoord.act_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:37:51.708899+00:00
-- url     : https://prove2.me/submissions/2f22b358-3d2e-48a5-8d5a-5de00120a2fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsTorusCoordinates
import Theorems.Thm_GlobalTheory_TorusCoord_pr_smul

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
namespace GlobalTheory.TorusCoord
theorem _root_.solution (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) (α : 𝓞 E) (y : X.Ψ → Fin r → ℂ) :
    coordMap X e (fun τ => τ.1 (α : E) • y τ) = act α (coordMap X e y) := by
  ext i
  show coord X e _ i = i.1 (α : E) * coord X e y i
  unfold coord
  split_ifs
  · rw [pr_smul X e (fun τ => τ.1 (α : E))]
  · rw [pr_smul X e (fun τ => τ.1 (α : E)), map_mul]
    simp
end GlobalTheory.TorusCoord
