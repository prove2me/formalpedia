-- Prove2me | solution 1 for GlobalTheory.FrameAdjSeries.jetSubstP_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:23.821793+00:00
-- url     : https://prove2.me/submissions/ea9d747c-1c52-4072-836a-ff2a9c04f800

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsAdjointnessSeriesOfFrames
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jet_hom_ext


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
open GlobalTheory GlobalTheory.FrameAdjSeries
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
namespace GlobalTheory.FrameAdjSeries
theorem _root_.solution {S κ κ' : Type} [CommRing S] (φ ψ : κ → MvPolynomial κ' S) :
    (jetSubstP 0 φ : Jet S κ 0 →ₐ[S] Jet S κ' 0) = jetSubstP 0 ψ := by
  apply jet_hom_ext
  intro i
  have h0 : (Ideal.Quotient.mk (orig S κ ^ (0 + 1)) (MvPolynomial.X i) : Jet S κ 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using X_mem_orig (R := S) i)
  rw [h0, map_zero, map_zero]
end GlobalTheory.FrameAdjSeries
