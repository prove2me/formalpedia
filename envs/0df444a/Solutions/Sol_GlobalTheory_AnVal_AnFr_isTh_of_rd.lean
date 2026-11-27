-- Prove2me | solution 1 for GlobalTheory.AnVal.AnFr.isTh_of_rd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:36:17.691453+00:00
-- url     : https://prove2.me/submissions/3a482ff2-9d48-4aea-abe5-98336c2f1fef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SectionReadingExistsUniqueIsTheta
import Theorems.Thm_GlobalTheory_AnVal_isHolFam_vtfQ
import Theorems.Thm_GlobalTheory_AnVal_AnFr_exists_chart_e
import Theorems.Thm_GlobalTheory_AnVal_AnFr_rd_val
import Theorems.Thm_GlobalTheory_AnVal_AnFr_rd_eq_div
import Theorems.Thm_GlobalTheory_AnVal_AnFr_e_add_lat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_chart


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
theorem _root_.solution {k : ℤ} {F : LB.Sec (LPow A L.L k (Over.mk x0))} {θ : (Fin g → ℂ) → ℂ}
    (h : Φ.Rd k F θ) : Φ.IsTh k θ := by
  constructor
  · intro z0
    obtain ⟨j, hj⟩ := Φ.exists_chart_e z0
    have hO : IsOpen {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j} := (Φ.hol (L.L.U j) 0).1
    have hv := (isHolFam_vtfQ Φ.e Φ.hol ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j))).2
    have hv' := hv.mono (s := {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j})
      (fun z hz => vtf_chart A L.L k (Φ.e z) (fun _ => j) hz)
    have hd : DifferentiableOn ℂ θ {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j} :=
      (hv'.mul ((Φ.fr_hol j).zpow (m := -k) (Or.inl fun z hz => Φ.fr_ne j z hz))).congr fun z hz => by
        rw [Φ.rd_eq_div h j z hz, div_eq_mul_inv, ← zpow_neg]
        rfl
    exact hd.differentiableAt (hO.mem_nhds hj)
  · intro a ha z
    obtain ⟨j, hj⟩ := Φ.exists_chart_e z
    have hj' : ⊤ ≤ (Φ.e (z + a)).left ⁻¹ᵁ L.L.U j := by rw [Φ.e_add_lat ha]; exact hj
    have h1 := Φ.rd_val h j z hj
    have h2 := Φ.rd_val h j (z + a) hj'
    rw [Φ.e_add_lat ha, h1, Φ.fr_per a ha j z hj, mul_zpow] at h2
    apply mul_right_cancel₀ (zpow_ne_zero k (Φ.fr_ne j (z + a) hj'))
    rw [← h2, AnFr.fac]
    ring
end AnFr
end GlobalTheory.AnVal
