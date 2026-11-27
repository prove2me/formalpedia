-- Prove2me | solution 1 for GlobalTheory.AnValJetEx.contDiffAt_fr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:54:03.198837+00:00
-- url     : https://prove2.me/submissions/75c4e512-e993-4b2d-87ac-16fdad272fac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsGeneratorJetReading
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


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
theorem _root_.solution {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) {n : ℕ} (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (j : L.L.ι)
    (h : (Φ.e (Λ (colsOf n g 0))).left cpt ∈ L.L.U j) :
    ContDiffAt ℂ ω (fun v => Φ.fr j (Λ (colsOf n g v))) 0 := by
  have h1 : ContDiffAt ℂ ω (Φ.fr j) (Λ (colsOf n g 0)) :=
    (ReciprocityTheory.AnForm.Osgood.osgood g {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j} (Φ.fr j) (Φ.hol (L.L.U j) 0).1 (Φ.fr_hol j) _
      (top_le_of_mem h)).contDiffAt
  have h2 : ContDiff ℂ ω (colsOf n g) :=
    contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_apply ℂ ℂ (finProdFinEquiv (i, j))
  have h3 : ContDiff ℂ ω (fun v => Λ (colsOf n g v)) :=
    (LinearMap.toContinuousLinearMap Λ).contDiff.comp h2
  exact h1.comp 0 h3.contDiffAt
end GlobalTheory.AnValJetEx
