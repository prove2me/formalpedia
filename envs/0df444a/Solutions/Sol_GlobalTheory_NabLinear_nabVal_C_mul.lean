-- Prove2me | solution 1 for GlobalTheory.NabLinear.nabVal_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:57:40.235904+00:00
-- url     : https://prove2.me/submissions/67d7c837-f68a-4bbb-a01a-ccde7467dc7a

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
import Theorems.Thm_GlobalTheory_NabLinear_dmon_C_mul

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
theorem _root_.solution [Algebra ℚ k] {R : Type} [CommRing R] [Algebra R k] {O : Type} [CommRing O] [StarRing O]
    (B : Germ.FB R d O) (h : PS k 2 d) (w0 : O) (q : ℕ) (c : k) (f : PS k 1 d) {κ : Type} [Fintype κ]
    (u : κ → Fin d → k) (P : MvPolynomial κ k) :
    B.nabVal k h w0 q (MvPowerSeries.C c * f) u P = c * B.nabVal k h w0 q f u P := by
  unfold Germ.FB.nabVal Germ.DpolyOf
  rw [_root_.mul_assoc, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dmon_C_mul]
  simp only [map_mul, MvPowerSeries.constantCoeff_C]
  ring
end GlobalTheory.NabLinear
