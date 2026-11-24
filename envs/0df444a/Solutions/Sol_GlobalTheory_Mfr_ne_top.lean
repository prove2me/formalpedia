-- Prove2me | solution 1 for GlobalTheory.Mfr_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:58:16.683393+00:00
-- url     : https://prove2.me/submissions/da737fff-1d49-46aa-84ca-b557dbab3260

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AdmissibleColumnsLeAndHarmonicMapCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    Mfr l ≠ ⊤ := by
  intro h
  have hb : l.Mb = ⊤ := by
    rw [Ideal.eq_top_iff_one] at h ⊢
    obtain ⟨y, hy, hy1⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 h
    have : y = 1 := H.bar.injective (by simpa using hy1)
    exact this ▸ hy
  have hp := l.prod
  rw [hb, Ideal.map_top, Ideal.top_mul] at hp
  have hn := congrArg Ideal.absNorm hp
  rw [Ideal.absNorm_top, Ideal.absNorm_span_natCast] at hn
  have h3 := l.three_le
  have hpos : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
  rcases Nat.pow_eq_one.1 hn.symm with h' | h' <;> omega
end GlobalTheory
