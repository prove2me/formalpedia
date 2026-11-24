-- Prove2me | solution 1 for GlobalTheory.DatumInverseCharacter.root_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:55:33.152543+00:00
-- url     : https://prove2.me/submissions/57e332df-c1c6-4f10-a46e-ef7f39ba9cd6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsQuotEquiv
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_zeta_pow

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
open GlobalTheory GlobalTheory.DatumInverseCharacter
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.DatumInverseCharacter
theorem _root_.solution {l : Level H} (c : Coeff l) {N : ℕ} (hN : N ∣ l.M) :
    ((⟨zeta l.M', c.zeta_mem⟩ : c.F) ^ (l.M' / N)) ^ N = 1 := by
  have hd : N ∣ l.M' := hN.trans (Nat.dvd_lcm_left l.M l.A)
  have hpos : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  rw [← pow_mul, Nat.div_mul_cancel hd]
  apply Subtype.ext
  simpa using zeta_pow hpos
end GlobalTheory.DatumInverseCharacter
