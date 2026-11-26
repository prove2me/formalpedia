-- Prove2me | solution 1 for Malliavin.isWienerTotal_of_processLpEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:21.681267+00:00
-- url     : https://prove2.me/submissions/8b19660d-930a-411b-8dea-f08e5c3a4eac

import Definitions.Def_Malliavin_MultipleIntegral
import Definitions.Def_Malliavin_WienerChaos
import Theorems.Thm_Malliavin_multipleIntegralCLM_mem_homogeneousChaos
import Theorems.Thm_Malliavin_homogeneousChaos_zero_eq_constants
import Theorems.Thm_Malliavin_IteratedIntegralConstruction_hasSum_simplexIntegralLI
import Theorems.Thm_Malliavin_IteratedIntegralConstruction_positiveIteratedTowerLI_surjective_of_processLpEmbedding
import Theorems.Thm_Malliavin_exists_multipleIntegralCLM_eq_simplexIntegralLI
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Topology symmDiff
noncomputable section
open Malliavin
universe u v u_1 u_2 u_4 u_6
universe u₁ u₂ u₃
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) [SecondCountableTopology (RandomL2 P)]
    (hmeas : ∀ t, Measurable (B t))
    (hexhausts : Function.Surjective (processLpEmbedding P B hmeas)) :
    IsWienerTotal hB := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [IsWienerTotal, wienerSubspace, eq_top_iff]
  intro F _
  let oneP := IteratedIntegralConstruction.probabilityOne hB
  let c : ℝ := inner ℝ oneP F
  let X0 : RandomL2 P := F - c • oneP
  have hone : inner ℝ oneP oneP = 1 := by
    rw [real_inner_self_eq_norm_sq,
      IteratedIntegralConstruction.norm_probabilityOne hB]
    norm_num
  have hX0 : inner ℝ oneP X0 = 0 := by
    dsimp [X0]
    rw [inner_sub_right, inner_smul_right, hone]
    simp only [c, mul_one, sub_self]
  let X : IteratedIntegralConstruction.CenteredRandomL2 hB :=
    ⟨X0, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hX0⟩
  obtain ⟨f, hf⟩ :=
    IteratedIntegralConstruction.positiveIteratedTowerLI_surjective_of_processLpEmbedding
      hB hmeas hexhausts X
  have hterm (n : ℕ) :
      IteratedIntegralConstruction.simplexIntegralLI hB n (f n) ∈
        wienerSubspace hB := by
    obtain ⟨g, hg⟩ := exists_multipleIntegralCLM_eq_simplexIntegralLI hB n (f n)
    apply Submodule.le_topologicalClosure
    apply le_iSup (fun k : ℕ ↦
      (homogeneousChaos hB k : Submodule ℝ (RandomL2 P))) (n + 1)
    rw [← hg]
    exact multipleIntegralCLM_mem_homogeneousChaos hB (n + 1) g
  have hXmem : (X : RandomL2 P) ∈ wienerSubspace hB := by
    have hXsum : HasSum
        (fun n ↦ IteratedIntegralConstruction.simplexIntegralLI hB n (f n))
        (X : RandomL2 P) := by
      simpa only [hf] using
        IteratedIntegralConstruction.hasSum_simplexIntegralLI hB f
    rw [← hXsum.tsum_eq]
    exact tsum_mem (Submodule.isClosed_topologicalClosure _) hterm
  have hone_mem : c • oneP ∈ wienerSubspace hB := by
    apply Submodule.le_topologicalClosure
    apply le_iSup (fun k : ℕ ↦
      (homogeneousChaos hB k : Submodule ℝ (RandomL2 P))) 0
    rw [homogeneousChaos_zero_eq_constants hB]
    apply Submodule.le_topologicalClosure
    refine ⟨c, ?_⟩
    change (Lp.constL 2 P ℝ) c = c • oneP
    rw [show c = c • (1 : ℝ) by simp only [smul_eq_mul, mul_one], map_smul]
    simp only [Lp.constL_apply, smul_eq_mul, mul_one, IteratedIntegralConstruction.probabilityOne,
      indicatorConstLp_univ, oneP]
  have hdecomp : F = c • oneP + (X : RandomL2 P) := by
    change F = c • oneP + X0
    dsimp only [X0]
    abel
  rw [hdecomp]
  exact add_mem hone_mem hXmem
end Malliavin
