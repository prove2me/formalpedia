-- Prove2me | solution 1 for GlobalTheory.FrameBaseChange.copy_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:47:01.432562+00:00
-- url     : https://prove2.me/submissions/821e6dcc-e8d7-4053-ae22-c614580d77ac

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsFrameRawChartBaseChange
import Theorems.Thm_GlobalTheory_FrameBaseChange_spec_comp
import Theorems.Thm_GlobalTheory_FrameBaseChange_jetMap_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetMap_comp_jetBC


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
open GlobalTheory GlobalTheory.FrameBaseChange
open MvPolynomial (X C)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X)
namespace GlobalTheory.FrameBaseChange
theorem _root_.solution (d m n : ℕ) (i : Fin n) :
    homAt (spMap ψ ≫ x0) (jetCopy d m i : Jet S' (Fin 1 × Fin d) m →ₐ[S'] Jet S' (Fin n × Fin d) m) ≫
        rjBC ψ x0 d m 1 =
      rjBC ψ x0 d m n ≫ homAt x0 (jetCopy d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) := by
  unfold rjBC Formalism.L2.Pj.homAt jetCopy
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.homMk_left]
  rw [spec_comp, spec_comp]
  congr 1
  have hS : ∀ p : Fin 1 × Fin d, (X (i, p.2) : MvPolynomial (Fin n × Fin d) S) ∈ orig S (Fin n × Fin d) := by
    intro p
    simp only [orig]
    exact Ideal.subset_span ⟨_, rfl⟩
  have hS' : ∀ p : Fin 1 × Fin d,
      MvPolynomial.map ψ (X (i, p.2) : MvPolynomial (Fin n × Fin d) S) ∈ orig S' (Fin n × Fin d) := by
    intro p
    rw [MvPolynomial.map_X]
    simp only [orig]
    exact Ideal.subset_span ⟨_, rfl⟩
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.jetMap_comp_jetBC ψ m (fun p : Fin 1 × Fin d => (X (i, p.2) : MvPolynomial (Fin n × Fin d) S)) hS hS'
  rw [jetMap_congr (g := fun p : Fin 1 × Fin d => MvPolynomial.map ψ (X (i, p.2) : MvPolynomial (Fin n × Fin d) S))
    (funext fun p => (MvPolynomial.map_X ψ (i, p.2)).symm) _ hS']
  exact h
end GlobalTheory.FrameBaseChange
