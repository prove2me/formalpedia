-- Prove2me | solution 1 for GlobalTheory.FrameAdjSeries.frame_origin_jet_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:23.821459+00:00
-- url     : https://prove2.me/submissions/256fdefe-ebc9-4776-a049-5282e8be01ce

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsAdjointnessSeriesOfFrames
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_jetAug_X
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_id
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}
namespace GlobalTheory.FrameAdjSeries
theorem _root_.solution (hch : IsChartG t x0 d F act tg uvec x) : x 0 = 1 := by
  have hj : (Algebra.ofId S (Jet S (Fin 1 × Fin d) 0)).comp jetAug = AlgHom.id S _ := by
    apply jet_hom_ext
    intro p
    rw [AlgHom.comp_apply, jetAug_X, map_zero, AlgHom.id_apply]
    exact (Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using X_mem_orig (R := S) p)).symm
  calc x 0 = 𝟙 _ ≫ x 0 := (Category.id_comp _).symm
    _ = (homAt x0 (Algebra.ofId S (Jet S (Fin 1 × Fin d) 0)) ≫ homAt x0 jetAug) ≫ x 0 := by
        rw [homAt_comp, hj, homAt_id]
    _ = homAt x0 (Algebra.ofId S (Jet S (Fin 1 × Fin d) 0)) ≫ 1 := by rw [Category.assoc, hch.zero 0]
    _ = 1 := map_one (preHom _)
end GlobalTheory.FrameAdjSeries
