-- Prove2me | solution 1 for GlobalTheory.PowGerm.UnivConv.aug_ren
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:04:11.108044+00:00
-- url     : https://prove2.me/submissions/6a027c07-0e28-4b49-ba07-73afc39978ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalJetsReindexFin
import Theorems.Thm_GlobalTheory_PowGerm_UnivConv_ren_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PowGerm.UnivConv
variable {V : Type} [CommRing V]
namespace GlobalTheory.PowGerm.UnivConv
theorem _root_.solution {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) :
    (jetAug : Jet V κ m →ₐ[V] V).comp (ren (V := V) β m).toAlgHom = Chart.jetAug V (Fin N) m :=
  Chart.jet_ext fun j => by
    rw [Chart.jetAug_zR]
    show jetAug (ren (V := V) β m (Chart.zR m j)) = 0
    rw [ren_zR]
    show MvPolynomial.aeval (fun _ : κ => (0 : V)) (MvPolynomial.X (β j)) = 0
    simp
end GlobalTheory.PowGerm.UnivConv
