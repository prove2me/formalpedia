-- Prove2me | solution 1 for GlobalTheory.DatumInverseCharacter.dvd_EF_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:46.782954+00:00
-- url     : https://prove2.me/submissions/302f2783-34b7-4a0b-9f7b-66ff6e51bfe4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsQuotEquiv
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_bar_bar

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
theorem _root_.solution (D : Datum H) {N : ℕ} {t : 𝓞 E} (ht : t ∈ Ideal.span {(N : 𝓞 E)}) (u v : D.La) :
    (N : ℤ) ∣ D.EF u (t • v) := by
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp ht
  have h : D.EF u ((s * (N : 𝓞 E)) • v) = D.EF (H.bar s • u) ((N : 𝓞 E) • v) := by
    rw [D.adj, bar_bar, mul_smul]
  rw [h, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
  exact dvd_mul_right _ _
end GlobalTheory.DatumInverseCharacter
