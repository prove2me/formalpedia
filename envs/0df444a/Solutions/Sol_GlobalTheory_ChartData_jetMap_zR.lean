-- Prove2me | solution 1 for GlobalTheory.ChartData.jetMap_zR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:07:44.626336+00:00
-- url     : https://prove2.me/submissions/b2e66f4e-c06e-4e03-8a0f-784e0d8d65a6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsPtJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsIsChartGOfBasis

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
theorem _root_.solution {S : Type} [CommRing S] {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (h) (s : κ) :
    (jetMap φ h : Jet S κ m →ₐ[S] Jet S κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X s)) = Ideal.Quotient.mk _ (φ s) := by
  show Ideal.Quotient.mkₐ S _ (MvPolynomial.aeval φ (MvPolynomial.X s)) = _
  rw [MvPolynomial.aeval_X]; rfl
end GlobalTheory.ChartData
