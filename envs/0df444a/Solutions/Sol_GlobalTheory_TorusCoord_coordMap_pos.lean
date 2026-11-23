-- Prove2me | solution 1 for GlobalTheory.TorusCoord.coordMap_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:00:49.947053+00:00
-- url     : https://prove2.me/submissions/b55ad9f2-dfa9-44bd-ace3-1fe1a9a45560

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
namespace GlobalTheory.TorusCoord
theorem _root_.solution (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) (y : X.Ψ → Fin r → ℂ) (τ : X.Ψ)
    (a : Fin (dimOf X τ.1)) :
    coordMap X e y ⟨τ.1, a⟩ = pr X e y τ ⟨a.1, lt_pos X τ.2 a⟩ := by
  show coord X e y ⟨τ.1, a⟩ = _
  unfold coord
  rw [dif_pos τ.2]
end GlobalTheory.TorusCoord
