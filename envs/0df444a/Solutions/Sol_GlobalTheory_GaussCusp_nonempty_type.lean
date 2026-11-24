-- Prove2me | solution 1 for GlobalTheory.GaussCusp.nonempty_type
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:09:39.661627+00:00
-- url     : https://prove2.me/submissions/4cbfc9ca-fbee-4561-b0bc-af019fd7e14c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementHypsConsistent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FirstRaisingMemEquivariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries (E4)
open GlobalTheory
open GlobalTheory.GaussCusp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {ζ : E}
namespace GlobalTheory.GaussCusp
theorem _root_.solution (hζ : IsPrimitiveRoot ζ 4) : Nonempty (data hζ).Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ (data hζ).Ψ
  · exact ⟨⟨τ, h⟩⟩
  · by_cases h' : ComplexEmbedding.conjugate τ ∈ (data hζ).Ψ
    · exact ⟨⟨_, h'⟩⟩
    · exact absurd (((data hζ).cmType τ).mpr h') h
end GlobalTheory.GaussCusp
