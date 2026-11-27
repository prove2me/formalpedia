-- Prove2me | solution 1 for GlobalTheory.AnValGenRd.top_le_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:44:43.361468+00:00
-- url     : https://prove2.me/submissions/801f6e8e-3358-40e8-a26e-929d94529930

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsHolomorphicGeneratorReadingAutomorphy
import Theorems.Thm_GlobalTheory_AnValGenRd_top_le_wchart_iff

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
open GlobalTheory GlobalTheory.AnValGenRd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
  {Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε))
namespace GlobalTheory.AnValGenRd
theorem _root_.solution {q : Sp ℂ ⟶ Z} {p : K → Fin g → ℂ} (hq : ∀ k, q ≫ φ k = (Φ.e (p k)).left) {j : K → L.L.ι}
    (hj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L.L φ j) (k : K) : ⊤ ≤ (Φ.e (p k)).left ⁻¹ᵁ L.L.U (j k) := by
  have h := (top_le_wchart_iff L.L φ j q).1 hj k
  rwa [hq k] at h
end GlobalTheory.AnValGenRd
