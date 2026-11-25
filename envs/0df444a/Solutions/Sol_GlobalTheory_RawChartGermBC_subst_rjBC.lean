-- Prove2me | solution 1 for GlobalTheory.RawChartGermBC.subst_rjBC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:51:51.629805+00:00
-- url     : https://prove2.me/submissions/d44dfc52-2c52-4c77-9ae2-1d705a8de12e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LBPull
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_RawChartBaseChangeRigGerm
import Theorems.Thm_GlobalTheory_RawChartGermBC_spMap_comp_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetSubstP_comp_jetBC


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
open GlobalTheory GlobalTheory.RawChartGermBC
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ)
namespace GlobalTheory.RawChartGermBC
theorem _root_.solution (m n n' : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S)
    (φ' : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S') (h : ∀ p, φ' p = MvPolynomial.map ψ (φ p)) :
    (Formalism.L2.Pj.homAt (spMap ψ ≫ x0) (jetSubstP m φ')).left ≫ (rjBC ψ x0 d m n).left =
      (rjBC ψ x0 d m n').left ≫ (Formalism.L2.Pj.homAt x0 (jetSubstP m φ)).left := by
  have hφ : φ' = fun p => MvPolynomial.map ψ (φ p) := funext h
  subst hφ
  unfold rjBC Formalism.L2.Pj.homAt
  simp only [Over.homMk_left]
  exact spMap_comp_eq _ _ _ _ (PullbackSections.jetSubstP_comp_jetBC ψ m φ)
end GlobalTheory.RawChartGermBC
