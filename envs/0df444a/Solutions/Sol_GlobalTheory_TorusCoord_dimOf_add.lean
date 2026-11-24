-- Prove2me | solution 1 for GlobalTheory.TorusCoord.dimOf_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:34:02.227037+00:00
-- url     : https://prove2.me/submissions/36e3fa2b-c172-429f-9d95-a138dadb256e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsTorusCoordinates
import Theorems.Thm_GlobalTheory_TorusCoord_dimOf_mem
import Theorems.Thm_GlobalTheory_TorusCoord_dimOf_not_mem

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
theorem _root_.solution (X : Data E r) (σ : E →+* ℂ) :
    dimOf X σ + dimOf X (ComplexEmbedding.conjugate σ) = r := by
  have := X.p0_le
  by_cases h : σ ∈ X.Ψ
  · rw [dimOf_mem X h, dimOf_not_mem X ((X.cmType σ).mp h)]; omega
  · rw [dimOf_not_mem X h, dimOf_mem X (conj_mem X h)]; omega
end GlobalTheory.TorusCoord
