-- Prove2me | solution 2 for OAI.LipschitzCounterexample.CompactWSC.abs_prod_sub_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:57:22.328762+00:00
-- url     : https://prove2.me/submissions/8704c383-4659-4d65-9ceb-36ff66955f33

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SmoothMultiplier.lean:L21-L43
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.CompactWSC.abs_prod_sub_prod_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBlocks
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothHilbert
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MolecularApproximation
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothCalculus
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_EnergyEstimates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BlockSelection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothMultiplier

-- ---- from OAI.Analysis.LipschitzEquivalence.SmoothMultiplier ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

namespace OAI

universe uH uIndex

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem abs_prod_le_one {ι : Type uIndex} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) : |∏ i ∈ s, a i| ≤ 1 := by
  rw [Finset.abs_prod]
  exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) ha).trans_eq (by simp)

theorem abs_prod_sub_prod_le {ι : Type uIndex} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |(∏ i ∈ s, a i)-(∏ i ∈ s, b i)| ≤ ∑ i ∈ s, |a i-b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have ha' : ∀ j ∈ s, |a j| ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hb' : ∀ j ∈ s, |b j| ≤ 1 := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi,Finset.prod_insert hi,Finset.sum_insert hi]
    have he : a i*(∏ j ∈ s, a j)-b i*(∏ j ∈ s, b j) =
        a i*((∏ j ∈ s, a j)-(∏ j ∈ s, b j))+(a i-b i)*(∏ j ∈ s, b j) := by ring
    rw [he]
    calc
      _ ≤ |a i| * |(∏ j ∈ s, a j)-(∏ j ∈ s, b j)|+|a i-b i| * |∏ j ∈ s, b j| := by
        simpa only [abs_mul] using abs_add_le (a i*((∏ j ∈ s, a j)-(∏ j ∈ s, b j)))
          ((a i-b i)*(∏ j ∈ s, b j))
      _ ≤ (∑ j ∈ s, |a j-b j|)+|a i-b i| := by
        apply add_le_add
        · exact (mul_le_mul_of_nonneg_right (ha i (Finset.mem_insert_self _ _)) (abs_nonneg _)).trans
            (by simpa using ih ha' hb')
        · simpa using mul_le_mul_of_nonneg_left (abs_prod_le_one s b hb') (abs_nonneg (a i-b i))
      _ = _ := add_comm _ _

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter


theorem solution.{uIndex} : type_of% @_root_.OAI.LipschitzCounterexample.CompactWSC.abs_prod_sub_prod_le.{uIndex} := @_root_.OAI.LipschitzCounterexample.CompactWSC.abs_prod_sub_prod_le.{uIndex}
