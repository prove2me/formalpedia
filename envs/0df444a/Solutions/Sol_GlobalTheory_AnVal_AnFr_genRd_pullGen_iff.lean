-- Prove2me | solution 1 for GlobalTheory.AnVal.AnFr.genRd_pullGen_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:42:04.065525+00:00
-- url     : https://prove2.me/submissions/c963ebd2-f5f2-439d-b45c-8a3a4033cb0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingPullbackPeriodRigid
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_val_pullU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_val_res


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
    (t : LB.Gen (LB.LinComb L.L φ ε)) {Z' : Scheme.{0}} (h : Z' ⟶ Z) (q : Sp ℂ ⟶ Z') (p : K → Fin g → ℂ) (v : ℂ) :
    Φ.GenRd (fun k => h ≫ φ k) ε (LB.pullGen L.L φ ε t h) q p v ↔ Φ.GenRd φ ε t (q ≫ h) p v := by
  have hc : ∀ j : K → L.L.ι, (⊤ ≤ q ⁻¹ᵁ LB.wchart L.L (fun k => h ≫ φ k) j) ↔
      ⊤ ≤ (q ≫ h) ⁻¹ᵁ LB.wchart L.L φ j := fun j =>
    ⟨fun H _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (H hy) k,
      fun H _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (H hy) k⟩
  have hv : ∀ j : K → L.L.ι, (⊤ ≤ q ⁻¹ᵁ LB.wchart L.L (fun k => h ≫ φ k) j) →
      valAt' q (LB.wchart L.L (fun k => h ≫ φ k) j) ((LB.pullGen L.L φ ε t h).s j).val =
        valAt' (q ≫ h) (LB.wchart L.L φ j) (t.s j).val := fun j hp =>
    (vtf_val_res q _ hp _).trans (vtf_val_pullU _ _ _ _)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => by rw [Category.assoc]; exact h1 k, fun j hj => ?_⟩
    exact (hv j ((hc j).2 hj)).symm.trans (h2 j ((hc j).2 hj))
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => by rw [← h1 k, Category.assoc], fun j hj => ?_⟩
    exact (hv j hj).trans (h2 j ((hc j).1 hj))
end AnFr
end GlobalTheory.AnVal
