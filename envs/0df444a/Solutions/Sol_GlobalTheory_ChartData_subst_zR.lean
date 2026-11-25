-- Prove2me | solution 1 for GlobalTheory.ChartData.subst_zR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:02:23.865929+00:00
-- url     : https://prove2.me/submissions/9decd693-72ce-4d78-8a52-5ff5b5490dba

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsPtJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsIsChartGOfBasis
import Theorems.Thm_GlobalTheory_ChartData_mk_psTrunc
import Theorems.Thm_GlobalTheory_ChartData_jetMap_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (FGLaw)
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ChartData
open GlobalTheory.ChartJet (Q gen sq_gen)
namespace GlobalTheory.ChartData
theorem _root_.solution {S : Type} [CommRing S] {d n : ℕ} (m : ℕ) (p : Q S d n) (s : Fin 1 × Fin d) :
    jetSubstP m (fun s : Fin 1 × Fin d => psTrunc m (p.1 s.2)) (Chart.zR m s) = ChartJet.pj m (p.1 s.2) :=
  (jetMap_zR m _ _ s).trans (mk_psTrunc m _ (p.2 _)).symm
end GlobalTheory.ChartData
