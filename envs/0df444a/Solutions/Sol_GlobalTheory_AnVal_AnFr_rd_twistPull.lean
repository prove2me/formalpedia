-- Prove2me | solution 1 for GlobalTheory.AnVal.AnFr.rd_twistPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:40:41.761007+00:00
-- url     : https://prove2.me/submissions/7d52c994-92a2-4593-a973-0eeeac6ed713

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ReadingTwistedPullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtfQ_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtfQ_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_pt_uniq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_read
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_twist


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal
namespace GlobalTheory.AnVal
namespace AnFr
theorem _root_.solution : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (ψ : Over.mk x0 ⊗ A ⟶ Over.mk x0 ⊗ A) (m : Over.mk x0 ⊗ A ⟶ A) (hm : ψ ≫ snd (Over.mk x0) A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd (Over.mk x0) A).left, m.left] ![a, -b])) (s : LB.Sec (LPow A L.L b (Over.mk x0))) (s' : LB.Sec (LPow A L.L a (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ) (p : (Fin g → ℂ) → Fin g → ℂ) (v : (Fin g → ℂ) → ℂ), ψ ≫ fst (Over.mk x0) A = fst (Over.mk x0) A → IsTwistPull A L.L ψ m hm a b α s s' → Φ.Rd b s θ → (∀ z, (ptSecT A (Φ.e z)).left ≫ m.left = (Φ.e (p z)).left ∧ ∃ j : Fin 2 → L.L.ι, ⊤ ≤ (ptSecT A (Φ.e z)).left ⁻¹ᵁ LB.wchart L.L ![(snd (Over.mk x0) A).left, m.left] j ∧ valAt' (ptSecT A (Φ.e z)).left (LB.wchart L.L ![(snd (Over.mk x0) A).left, m.left] j) (α.s j).val = v z * (Φ.fr (j 0) z ^ a * Φ.fr (j 1) (p z) ^ (-b))) → Φ.Rd a s' (fun z => v z * θ (p z)) := by
  intro S A _ _ L x0 g Φ ψ m hm a b α s s' θ p v hψ ht hs hα j' z pt h1 h2 hj'
  obtain ⟨hmz, j, hj, hv⟩ := hα z
  change (vtfQ A (Φ.e z)).left ≫ m.left = _ at hmz
  change ⊤ ≤ (vtfQ A (Φ.e z)).left ⁻¹ᵁ _ at hj
  change valAt' (vtfQ A (Φ.e z)).left _ _ = _ at hv
  have h0 : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (j 0) := by
    rw [← vtfQ_snd A (Φ.e z)]
    intro q hq
    exact LB.wchart_le L.L ![(snd (Over.mk x0) A).left, m.left] j 0 (hj hq)
  have h1' : ⊤ ≤ (Φ.e (p z)).left ⁻¹ᵁ L.L.U (j 1) := by
    rw [← hmz]
    intro q hq
    exact LB.wchart_le L.L ![(snd (Over.mk x0) A).left, m.left] j 1 (hj hq)
  have e1 : ((vtfQ A (Φ.e z)).left ≫ ψ.left) ≫ (snd (Over.mk x0) A).left = (Φ.e (p z)).left := by
    rw [Category.assoc, ← Over.comp_left, hm, hmz]
  have e2 : ((vtfQ A (Φ.e z)).left ≫ ψ.left) ≫ (fst (Over.mk x0) A).left = 𝟙 (Sp ℂ) := by
    rw [Category.assoc, ← Over.comp_left, hψ]
    exact vtfQ_fst A (Φ.e z)
  have hr := hs (j 1) (p z) _ e1 e2 h1'
  have tw := vtf_twist A L.L ht (vtfQ A (Φ.e z)).left j hj
  have hne := Φ.fr_ne (j 1) (p z) h1'
  rw [vtf_pt_uniq A (Φ.e z) pt h1 h2]
  refine vtf_read A L.L s' (Φ.e z) (fun i => Φ.fr i z) (fun i i' h => Φ.fr_g i i' z h) (j 0) j' h0 hj' _ ?_
  refine tw.trans ?_
  refine (congrArg₂ (· * ·) hv hr).trans ?_
  have hz : Φ.fr (j 1) (p z) ^ b ≠ 0 := zpow_ne_zero _ hne
  rw [zpow_neg]
  field_simp
end AnFr
end GlobalTheory.AnVal
