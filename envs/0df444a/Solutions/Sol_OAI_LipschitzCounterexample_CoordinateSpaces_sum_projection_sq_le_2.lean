-- Prove2me | solution 2 for OAI.LipschitzCounterexample.CoordinateSpaces.sum_projection_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:20:21.021118+00:00
-- url     : https://prove2.me/submissions/7fd9cf31-0adb-4fa4-b683-2ca5cbda71c1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SeparableCoordinates.lean:L136-L162
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.CoordinateSpaces.sum_projection_sq_le. The node keeps its source
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

-- ---- from OAI.Analysis.LipschitzEquivalence.SeparableCoordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uI uE uM

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]
theorem inner_eq_zero_of_disjoint {S T : Set (Σ n, ι n)} (hST : Disjoint S T)
    {x y : Hilbert (ι := ι)} (hx : x ∈ space S) (hy : y ∈ space T) : ⟪x,y⟫_ℝ = 0 := by
  rw [lp.inner_eq_tsum]
  suffices h : ∀ n, ⟪x n,y n⟫_ℝ = 0 by simp only [h, tsum_zero]
  intro n
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hs : (⟨n,a⟩ : Σ n, ι n) ∈ S
  · have ht : (⟨n,a⟩ : Σ n, ι n) ∉ T := fun ht => Set.disjoint_left.mp hST hs ht
    rw [(mem_space T y).mp hy ⟨n,a⟩ ht, inner_zero_right]
  · rw [(mem_space S x).mp hx ⟨n,a⟩ hs, inner_zero_left]

end LipschitzCounterexample.CoordinateSpaces

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

theorem norm_projection_sq (S : Set (Σ n, ι n)) (x : Hilbert (ι := ι)) :
    ‖projection S x‖^2 = ⟪x,projection S x⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq]
  exact (inner_projection S (projection_mem S x) x).trans (real_inner_comm _ _)

theorem sum_projection_sq_le {I : Type uI} [Fintype I] (S : I → Set (Σ n, ι n))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (x : Hilbert (ι := ι)) :
    ∑ i, ‖projection (S i) x‖^2 ≤ ‖x‖^2 := by
  let v := fun i => projection (S i) x
  have hv : Pairwise (fun i j => ⟪v i,v j⟫_ℝ = 0) := by
    intro i j hij
    exact inner_eq_zero_of_disjoint (hS hij) (projection_mem (S i) x) (projection_mem (S j) x)
  have hs : ‖∑ i, v i‖^2 = ∑ i, ‖v i‖^2 := by
    rw [← real_inner_self_eq_norm_sq, inner_sum]
    simp_rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · exact real_inner_self_eq_norm_sq _
    · intro j hj hji
      exact hv hji
    · simp
  have ht : ⟪x,∑ i, v i⟫_ℝ = ∑ i, ‖v i‖^2 := by
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (norm_projection_sq (S i) x).symm
  have he := norm_sub_sq_real x (∑ i, v i)
  rw [hs,ht] at he
  have hn := sq_nonneg ‖x-∑ i, v i‖
  dsimp [v] at hs ht he hn ⊢
  linarith
end LipschitzCounterexample.CoordinateSpaces

namespace LipschitzCounterexample.HilbertSlots
open scoped ENNReal NNReal InnerProductSpace Topology
variable {E : ℕ → Type uE} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]

end LipschitzCounterexample.HilbertSlots

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set CoordinateSpaces

end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.FreeSpace
open scoped Topology NNReal
open Filter Set
variable {M : Type uM} [MetricSpace M] [Zero M]

end LipschitzCounterexample.FreeSpace

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

end LipschitzCounterexample.CoordinateSpaces

end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CoordinateSpaces
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set


theorem solution.{uIndex,uI} : type_of% @_root_.OAI.LipschitzCounterexample.CoordinateSpaces.sum_projection_sq_le.{uIndex,uI} := @_root_.OAI.LipschitzCounterexample.CoordinateSpaces.sum_projection_sq_le.{uIndex,uI}
