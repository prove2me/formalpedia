-- Prove2me | solution 1 for GlobalTheory.PowGerm.NabJet.coeff_iterate_DofN_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:12:31.610225+00:00
-- url     : https://prove2.me/submissions/36ac3e73-31ca-4f06-a992-029e42490c9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonNCongr
import Theorems.Thm_GlobalTheory_PowGerm_NabJet_coeff_DofN_congr
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PowGerm.NabJet
open MvPowerSeries
variable {k : Type} [CommRing k] {d n : ℕ}
namespace GlobalTheory.PowGerm.NabJet
theorem _root_.solution (F : Fin d → PS k 2 d) (b : Fin n) (v : Fin d → k) (r : ℕ) :
    ∀ (N : ℕ) (f g : PS k n d),
      (∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N + r → coeff mo f = coeff mo g) →
      ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N →
        coeff mo ((DofN F b v)^[r] f) = coeff mo ((DofN F b v)^[r] g) := by
  induction r with
  | zero => intro N f g h mo hmo; exact h mo hmo
  | succ r ih =>
    intro N f g h mo hmo
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih N _ _ (coeff_DofN_congr F b v (N + r) f g h) mo hmo
end GlobalTheory.PowGerm.NabJet
