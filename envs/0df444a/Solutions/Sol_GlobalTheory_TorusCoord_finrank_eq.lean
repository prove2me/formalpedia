-- Prove2me | solution 1 for GlobalTheory.TorusCoord.finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:01:49.316407+00:00
-- url     : https://prove2.me/submissions/f01532a3-0279-44b1-a916-ceda86c4f052

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsTorusCoordinates
import Theorems.Thm_GlobalTheory_TorusCoord_card_idx

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
theorem _root_.solution (X : Data E r) :
    Module.finrank ℝ (X.Ψ → Fin r → ℂ) = Module.finrank ℝ (Vsp (dimOf X)) := by
  rw [(WithLp.linearEquiv 2 ℝ (Idx (dimOf X) → ℂ)).finrank_eq]
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, card_idx, smul_eq_mul, Fintype.card_coe, Fintype.card_fin]
  ring
end GlobalTheory.TorusCoord
