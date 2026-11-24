-- Prove2me | solution 1 for GlobalTheory.FrameSymmetry.pt_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:48:26.444087+00:00
-- url     : https://prove2.me/submissions/f4521b8b-1fbb-4be6-a1aa-36b31ed51a86

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSymmetrySeriesOfFrames
import Theorems.Thm_GlobalTheory_FrameSymmetry_subst_comp_copy

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
open GlobalTheory GlobalTheory.FrameSymmetry
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
namespace GlobalTheory.FrameSymmetry
theorem _root_.solution (m : ℕ) {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S) (i : Fin 2) :
    homAt x0 (jetSubstP m (fun p : Fin 2 × Fin d => φ p.1 p.2)) ≫ jptG t x0 d x m i =
      homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ i p.2)) ≫ x m := by
  unfold jptG
  rw [← Category.assoc, ← subst_comp_copy]
  congr 1
  apply Over.OverMorphism.ext
  simp only [Formalism.L2.Pj.homAt, Over.comp_left, Over.homMk_left]
  unfold spMap
  rw [← Spec.map_comp]
  rfl
end GlobalTheory.FrameSymmetry
