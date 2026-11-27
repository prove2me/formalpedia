-- Prove2me | solution 1 for GlobalTheory.AnVal.AnFr.rd_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:08:16.53871+00:00
-- url     : https://prove2.me/submissions/3bafcafb-cc13-4134-a55e-81945e971ece

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SectionReadingExistsUniqueIsTheta
import Theorems.Thm_GlobalTheory_AnVal_AnFr_exists_chart_e
import Theorems.Thm_GlobalTheory_AnVal_AnFr_rd_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_pt_uniq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_read


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
namespace GlobalTheory.AnVal
namespace AnFr
theorem _root_.solution (k : ℤ) (F : LB.Sec (LPow A L.L k (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ) :
    Φ.Rd k F θ ↔ ∀ z, ∃ j, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j ∧
      valAt' (vtfQ A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) =
        θ z * Φ.fr j z ^ k := by
  constructor
  · intro h z
    obtain ⟨j, hj⟩ := Φ.exists_chart_e z
    exact ⟨j, hj, Φ.rd_val h j z hj⟩
  · intro h j' z pt h1 h2 hj'
    obtain ⟨j, hj, hv⟩ := h z
    rw [vtf_pt_uniq A (Φ.e z) pt h1 h2]
    exact vtf_read A L.L F (Φ.e z) (fun j => Φ.fr j z) (fun a b hab => Φ.fr_g a b z hab) j j' hj hj' _ hv
end AnFr
end GlobalTheory.AnVal
