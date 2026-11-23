-- Prove2me | solution 1 for GlobalTheory.FrameAdjSeries.subst_psIn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:30.831817+00:00
-- url     : https://prove2.me/submissions/1454c42e-2e79-4f3e-9e3b-cead81f49e31

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsAdjointnessSeriesOfFrames
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetMap_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jet_hom_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
variable {S : Type} [CommRing S] (d : ℕ)
namespace GlobalTheory.FrameAdjSeries
theorem _root_.solution (m : ℕ) {n n' : ℕ} (r : Fin n → Fin n') (g : Fin d → MvPowerSeries (Fin n × Fin d) S) :
    jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (g p.2)) =
      (jetRen d m r).comp (jetSubstP m (fun p : Fin 1 × Fin d => psTrunc m (g p.2))) := by
  have hr : (MvPolynomial.aeval fun q : Fin n × Fin d => (MvPolynomial.X (r q.1, q.2) : MvPolynomial (Fin n' × Fin d) S)) =
      MvPolynomial.rename fun p : Fin n × Fin d => (r p.1, p.2) := MvPolynomial.algHom_ext fun q => by simp
  apply jet_hom_ext
  intro p
  simp only [jetSubstP, jetRen, AlgHom.comp_apply, jetMap_mk, MvPolynomial.aeval_X, map_sub, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq, psIn, MvPolynomial.constantCoeff_rename, hr, MvPolynomial.rename_C]
end GlobalTheory.FrameAdjSeries
