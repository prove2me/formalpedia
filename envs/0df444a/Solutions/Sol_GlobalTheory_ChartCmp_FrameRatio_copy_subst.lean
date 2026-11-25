-- Prove2me | solution 1 for GlobalTheory.ChartCmp.FrameRatio.copy_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:37:53.399209+00:00
-- url     : https://prove2.me/submissions/d95b932e-709d-452d-b321-f80bea9ff39a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetFramesDifferByUnitEachOrder
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_jetMap_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetMap_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jet_hom_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_add
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.FrameRatio
namespace GlobalTheory.ChartCmp.FrameRatio
theorem _root_.solution {V : Type} [CommRing V] (d m : ℕ) (φ : Fin d → MvPowerSeries (Fin 1 × Fin d) V)
    (ψ : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V) (i : Fin 2)
    (hψ : ∀ j, ψ i j = psIn d m ![i] (φ j)) :
    (jetCopy d m i).comp (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2)) =
      (jetSubstP m fun p : Fin 2 × Fin d => ψ p.1 p.2).comp (jetCopy d m i) := by
  apply GermD.jet_hom_ext
  rintro ⟨i0, j⟩
  simp only [AlgHom.comp_apply, jetCopy, jetSubstP, GaugeR.jetMap_mk, MvPolynomial.aeval_X, hψ, psIn,
    MvPolynomial.constantCoeff_rename, map_sub, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  congr 2
  generalize psTrunc m (φ j) = P
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p k hp =>
    rw [map_mul, map_mul, hp, MvPolynomial.rename_X, MvPolynomial.aeval_X]
    obtain ⟨a, b⟩ := k
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl
end GlobalTheory.ChartCmp.FrameRatio
