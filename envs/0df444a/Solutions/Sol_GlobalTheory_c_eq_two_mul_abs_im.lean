-- Prove2me | solution 1 for GlobalTheory.c_eq_two_mul_abs_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:22:42.984809+00:00
-- url     : https://prove2.me/submissions/00166bd9-985b-4aa2-94ca-0521db015bb9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceFormIndependence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_SumCMulImHermCEqSignMulTrace
import Theorems.Thm_GlobalTheory_re_map_xi_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open NumberField
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E]
    {r : ℕ}
    (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (τ : X.Ψ) : X.c τ = 2 * |(τ.1 X.ξ0).im| := by
  have hre := _root_.GlobalTheory.re_map_xi_eq_zero X τ.1
  have hz : τ.1 X.ξ0 = ((τ.1 X.ξ0).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.c
  conv_lhs => rw [hz]
  simp [Complex.norm_real]
end _root_.GlobalTheory
end GlobalTheory
