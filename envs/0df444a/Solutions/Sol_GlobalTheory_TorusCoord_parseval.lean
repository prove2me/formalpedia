-- Prove2me | solution 1 for GlobalTheory.TorusCoord.parseval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:34:02.960551+00:00
-- url     : https://prove2.me/submissions/bf4c5937-cf72-4818-a1c0-a47241a51b74

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsTorusCoordinates
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_expand


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
theorem _root_.solution (X : Data E r) (τ : X.Ψ) (e : Fin r → Fin r → ℂ)
    (he : ∀ a b, hermC τ.1 X.Gm (e a) (e b) =
      if a = b then ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm u v = ∑ a : Fin r, ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) *
      (hermC τ.1 X.Gm u (e a) * conj (hermC τ.1 X.Gm v (e a))) := by
  conv_lhs => arg 4; rw [expand X τ e he v]
  rw [hermC_sum_right]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hermC_smul_right, map_mul, Complex.conj_ofReal]
  ring
end GlobalTheory.TorusCoord
