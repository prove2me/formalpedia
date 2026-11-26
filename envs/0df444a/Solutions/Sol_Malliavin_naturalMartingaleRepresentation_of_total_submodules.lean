-- Prove2me | solution 1 for Malliavin.naturalMartingaleRepresentation_of_total_submodules
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:53:58.142906+00:00
-- url     : https://prove2.me/submissions/b14a1d25-ad6e-4455-a689-204d7845fc25

import Definitions.Def_Malliavin_NaturalClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Definitions.Def_Malliavin_ChaosMartingaleRepresentation
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_isClosed_naturalItoRange
import Theorems.Thm_Malliavin_naturalItoRange_le_expectationMap_ker
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (K : ℕ → Submodule ℝ (RandomL2 P))
    (htotal : (⨆ n : ℕ, K n).topologicalClosure = ⊤)
    (hzero : K 0 ≤ (centeredPartCLM (P := P)).ker)
    (hpositive : ∀ n : ℕ, 0 < n → K n ≤ naturalItoRange hB hsm hnat) :
    NaturalMartingaleRepresentation hB hsm hnat := by
  let M : Submodule ℝ (RandomL2 P) :=
    (naturalItoRange hB hsm hnat).comap
      (centeredPartCLM (P := P)).toLinearMap
  have hMclosed : IsClosed (M : Set (RandomL2 P)) := by
    exact (isClosed_naturalItoRange hB hsm hnat).preimage
      (centeredPartCLM (P := P)).continuous
  have hgraded (n : ℕ) : K n ≤ M := by
    cases n with
    | zero =>
        intro F hF
        change centeredPartCLM F ∈ naturalItoRange hB hsm hnat
        rw [show centeredPartCLM F = 0 by exact hzero hF]
        exact zero_mem _
    | succ n =>
        intro F hF
        change centeredPartCLM F ∈ naturalItoRange hB hsm hnat
        have hFmem : F ∈ naturalItoRange hB hsm hnat :=
          hpositive (n + 1) (Nat.zero_lt_succ n) hF
        have hcentered : CameronMartin.expectationMap P F = 0 :=
          naturalItoRange_le_expectationMap_ker hB hsm hnat hFmem
        have hexpect : expectationL2 F = 0 := by
          rw [expectationL2, ← CameronMartin.expectationMap_apply, hcentered]
          exact map_zero _
        rw [centeredPartCLM_apply, hexpect, sub_zero]
        exact hFmem
  have htop : (⊤ : Submodule ℝ (RandomL2 P)) ≤ M := by
    rw [← htotal]
    exact Submodule.topologicalClosure_minimal _ (iSup_le hgraded) hMclosed
  intro F
  have hmem : centeredPartCLM F ∈ naturalItoRange hB hsm hnat := by
    exact htop (Submodule.mem_top : F ∈ (⊤ : Submodule ℝ (RandomL2 P)))
  obtain ⟨U, hU⟩ := hmem
  refine ⟨U, ?_⟩
  rw [centeredPartCLM_apply] at hU
  change naturalItoIntegral hB hsm hnat U = F - expectationL2 F at hU
  calc
    F = expectationL2 F + (F - expectationL2 F) := by abel
    _ = expectationL2 F + naturalItoIntegral hB hsm hnat U := by rw [← hU]
end Malliavin
