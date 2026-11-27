-- Prove2me | solution 1 for GlobalTheory.AnValJetEx.mem_of_spMap_jetPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:15:18.490728+00:00
-- url     : https://prove2.me/submissions/d81ca99b-7ce8-4f63-a8c9-c5709c448eef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsGeneratorJetReading
import Theorems.Thm_GlobalTheory_AnValJetEx_jet_point_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_closedPoint


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
open GlobalTheory GlobalTheory.AnValJetEx
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AnValJetEx
theorem _root_.solution {d : ℕ} {Y : Scheme.{0}} (e : (Fin d → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (m : ℕ)
    {I : Type} (r : Jet ℂ (Fin 1 × Fin d) m →+* Jet ℂ I m) (U : Y.Opens)
    (h : ⊤ ≤ (spMap r ≫ jetPt e hol m) ⁻¹ᵁ U) : e 0 cpt ∈ U := by
  let p : Sp (Jet ℂ I m) := IsLocalRing.closedPoint (Jet ℂ I m)
  have h2 : (spMap r ≫ jetPt e hol m) p ∈ U := h (show p ∈ (⊤ : (Sp (Jet ℂ I m)).Opens) from trivial)
  rw [Scheme.Hom.comp_apply] at h2
  rw [← jetPt_closedPoint e hol m, ← jet_point_eq (K := ℂ) (I := Fin 1 × Fin d) (m := m) (spMap r p)]
  exact h2
end GlobalTheory.AnValJetEx
