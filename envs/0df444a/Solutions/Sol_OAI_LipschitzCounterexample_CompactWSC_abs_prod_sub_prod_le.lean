-- Prove2me | solution 1 for OAI.LipschitzCounterexample.CompactWSC.abs_prod_sub_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:07:35.246614+00:00
-- url     : https://prove2.me/submissions/1d459a8f-1c22-4c38-8a85-1b6cba9c3924

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
universe uH uIndex
open scoped ContDiff BigOperators NNReal Topology
open Set Filter
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]


theorem solution {ι : Type uIndex} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |(∏ i ∈ s, a i)-(∏ i ∈ s, b i)| ≤ ∑ i ∈ s, |a i-b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have haj := ha j (Finset.mem_insert_self _ _)
    have hbj := hb j (Finset.mem_insert_self _ _)
    have ih' := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi)) (fun i hi => hb i (Finset.mem_insert_of_mem hi))
    have hpb : |∏ i ∈ s, b i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i hi => hb i (Finset.mem_insert_of_mem hi))
    have e : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        a j * ((∏ i ∈ s, a i) - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [e]
    calc _ ≤ |a j * ((∏ i ∈ s, a i) - ∏ i ∈ s, b i)| + |(a j - b j) * ∏ i ∈ s, b i| := abs_add_le _ _
      _ = |a j| * |(∏ i ∈ s, a i) - ∏ i ∈ s, b i| + |a j - b j| * |∏ i ∈ s, b i| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * (∑ i ∈ s, |a i - b i|) + |a j - b j| * 1 := by
          gcongr
      _ = _ := by ring

