-- Prove2me | solution 1 for GlobalTheory.TwoLines.chi_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:17:18.740513+00:00
-- url     : https://prove2.me/submissions/dcce9fb7-92a2-404c-9c9c-c02657784f71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfHermOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RightMulBorelFirstColumn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix
open GlobalTheory GlobalTheory.TwoLines
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.TwoLines
theorem _root_.solution (X : Data E 2) (la : Wt X.Ψ 2) : X.χ la 1 = 1 := by
  have h1 := X.χ_mul la 1 X.Γ.one_mem 1 X.Γ.one_mem
  obtain ⟨n, hn, h2⟩ := X.χ_fin la
  have h3 := h2 1 X.Γ.one_mem
  have h4 : X.χ la 1 ≠ 0 := by
    intro h; rw [h, zero_pow hn.ne'] at h3; exact zero_ne_one h3
  rw [mul_one] at h1
  exact (mul_eq_left₀ h4).1 h1.symm
end GlobalTheory.TwoLines
