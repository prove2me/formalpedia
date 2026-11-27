-- Prove2me | solution 1 for GlobalTheory.AnVal.AnFr.genRd_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:07:21.850594+00:00
-- url     : https://prove2.me/submissions/698e5f89-63a3-452e-9d81-9bd8f8bf4460

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingPullbackPeriodRigid
import Theorems.Thm_GlobalTheory_AnVal_AnFr_genMove_e_per
import Theorems.Thm_GlobalTheory_AnVal_genMove_chart

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
open GlobalTheory GlobalTheory.AnVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
namespace GlobalTheory.AnVal
namespace AnFr
theorem _root_.solution {Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L.L φ ε)) (q : Sp ℂ ⟶ Z) (p a : K → Fin g → ℂ) (v : ℂ) (ha : ∀ k, a k ∈ Φ.lat)
    (H : Φ.GenRd φ ε t q p v) :
    Φ.GenRd φ ε t q (fun k => p k + a k) (v * ∏ k, Φ.fac (a k) (p k) ^ ε k) := by
  obtain ⟨h1, h2⟩ := H
  refine ⟨fun k => by rw [Φ.genMove_e_per _ _ (ha k)]; exact h1 k, fun j hj => ?_⟩
  rw [h2 j hj, _root_.mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  have hk := genMove_chart L.L φ q j hj k
  rw [h1 k] at hk
  rw [Φ.fr_per (a k) (ha k) (j k) (p k) hk, mul_zpow]
  rfl
end AnFr
end GlobalTheory.AnVal
