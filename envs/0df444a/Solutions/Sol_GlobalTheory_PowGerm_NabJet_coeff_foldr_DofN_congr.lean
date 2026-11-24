-- Prove2me | solution 1 for GlobalTheory.PowGerm.NabJet.coeff_foldr_DofN_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:28:28.267408+00:00
-- url     : https://prove2.me/submissions/4b500fc3-9bf0-4cbc-98aa-226344c93d1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonNCongr
import Theorems.Thm_GlobalTheory_PowGerm_NabJet_coeff_iterate_DofN_congr

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
theorem _root_.solution (F : Fin d → PS k 2 d) {Ix : Type} (cp : Ix → Fin n) (u : Ix → Fin d → k) (m : Ix → ℕ)
    (f g : PS k n d) (L : List Ix) :
    ∀ N : ℕ,
      (∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N + (L.map m).sum → coeff mo f = coeff mo g) →
      ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N →
        coeff mo (L.foldr (fun l s => (DofN F (cp l) (u l))^[m l] s) f) =
          coeff mo (L.foldr (fun l s => (DofN F (cp l) (u l))^[m l] s) g) := by
  induction L with
  | nil => intro N h mo hmo; exact h mo hmo
  | cons l L ih =>
    intro N h mo hmo
    rw [List.foldr_cons, List.foldr_cons]
    refine coeff_iterate_DofN_congr F (cp l) (u l) (m l) N _ _ (ih (N + m l) fun mo' h' => h mo' ?_) mo hmo
    rw [List.map_cons, List.sum_cons]
    omega
end GlobalTheory.PowGerm.NabJet
