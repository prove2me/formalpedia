-- Prove2me | solution 1 for GlobalTheory.NabLinear.dmon_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:40:01.675812+00:00
-- url     : https://prove2.me/submissions/c749fc8c-8e7b-4992-ab9f-f6da14233121

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThExpBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ConnectionLinearInSection
import Theorems.Thm_GlobalTheory_NabLinear_dof_iter_C_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open GlobalTheory GlobalTheory.NabLinear
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.NabLinear
theorem _root_.solution (F : Fin d → PS k 2 d) {κ : Type} [Fintype κ] (u : κ → Fin d → k) (m : κ →₀ ℕ) (c : k)
    (f : PS k 1 d) :
    Germ.DmonOf F u m (MvPowerSeries.C c * f) = MvPowerSeries.C c * Germ.DmonOf F u m f := by
  unfold Germ.DmonOf
  induction (Finset.univ : Finset κ).toList with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, List.foldr_cons, ih, dof_iter_C_mul]
end GlobalTheory.NabLinear
