-- Prove2me | solution 1 for GlobalTheory.SecondPartialLaw.ren_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:09:24.385991+00:00
-- url     : https://prove2.me/submissions/63631f2d-e7e6-47fb-815e-df833bab017a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSecondPartialLaw
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetMap_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jet_hom_ext


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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
noncomputable section
open GlobalTheory GlobalTheory.SecondPartialLaw
variable {S : Type} [CommRing S] (d : ℕ)
namespace GlobalTheory.SecondPartialLaw
theorem _root_.solution (m : ℕ) {n' : ℕ} (r : Fin 1 → Fin n') : jetRen (S := S) d m r = jetCopy d m (r 0) := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp only [jetRen, jetCopy, jetMap_mk, MvPolynomial.aeval_X]
end GlobalTheory.SecondPartialLaw
