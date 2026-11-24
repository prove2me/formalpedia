-- Prove2me | solution 1 for GlobalTheory.PowGerm.NabJet.isLinearMap_DmonN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:43:54.698446+00:00
-- url     : https://prove2.me/submissions/f4a24340-5372-4130-8572-ef0cae90c540

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonNCongr
import Theorems.Thm_GlobalTheory_PowGerm_NabJet_isLinearMap_DofN
import Theorems.Thm_GlobalTheory_PowGerm_NabJet_isLinearMap_iterate

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
theorem _root_.solution (F : Fin d → PS k 2 d) {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k)
    (m : Ix →₀ ℕ) : IsLinearMap k (DmonN F cp u m : PS k n d → PS k n d) := by
  unfold DmonN
  induction (Finset.univ : Finset Ix).toList with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | cons l L ih =>
    have hl := isLinearMap_iterate _ (isLinearMap_DofN F (cp l) (u l)) (m l)
    constructor
    · intro f g
      simp only [List.foldr_cons]
      rw [ih.map_add, hl.map_add]
    · intro c f
      simp only [List.foldr_cons]
      rw [ih.map_smul, hl.map_smul]
end GlobalTheory.PowGerm.NabJet
