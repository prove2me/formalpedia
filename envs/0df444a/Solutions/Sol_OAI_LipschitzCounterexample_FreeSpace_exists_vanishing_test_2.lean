-- Prove2me | solution 2 for OAI.LipschitzCounterexample.FreeSpace.exists_vanishing_test
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:40:07.673106+00:00
-- url     : https://prove2.me/submissions/7123b3dc-b04f-4fcc-a434-3e1e610915fd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SupportedDuality.lean:L43-L84
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.FreeSpace.exists_vanishing_test. The node keeps its source
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
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_linearize_unique

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
end LipschitzCounterexample.CoordinateSpaces

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

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

theorem supported_isClosed (K : Set M) : IsClosed (supported K : Set (Space M)) :=
  Submodule.isClosed_topologicalClosure _

theorem point_mem_supported {K : Set M} {x : M} (hx : x ∈ K) : point x ∈ supported K :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨x,hx,rfl⟩)

end LipschitzCounterexample.FreeSpace

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

end LipschitzCounterexample.CoordinateSpaces

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.SupportedDuality ----
namespace OAI

universe uM uE

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem dual_as_test (T : Space M →L[ℝ] ℝ) :
    test (normalized (fun x => T (point x)) (dual_point_lipschitz T)) = T := by
  have hzero : T (point 0) = 0 := by simp
  exact (linearize_unique _ (dual_point_lipschitz T) hzero _ (by
    intro x
    change T (point x)-T (point 0) = T (point x)
    rw [hzero,sub_zero])).symm.trans
    (linearize_unique _ (dual_point_lipschitz T) hzero T (fun _ => rfl))

theorem exists_vanishing_test (K : Set M) (μ : Space M) {ε : ℝ}
    (hfar : ∀ ν : Space M, ν ∈ supported K → ε ≤ ‖μ-ν‖) :
    ∃ f : M → ℝ, LipschitzWith 1 f ∧ f 0 = 0 ∧ (∀ x ∈ K, f x = 0) ∧
      ∀ hf : LipschitzWith 1 f, ε ≤ test (normalized f hf) μ := by
  let S := supported K
  let : IsClosed (S : Set (Space M)) := supported_isClosed K
  have hnorm : ε ≤ ‖S.mkQL μ‖ := by
    by_contra h
    have ht : 0 < ε-‖S.mkQL μ‖ := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨x,hx,hxnorm⟩ := Submodule.Quotient.norm_mk_lt (S.mkQL μ) ht
    have hmem : μ-x ∈ S := by
      apply (Submodule.Quotient.mk_eq_zero S).mp
      change S.mkQ (μ-x) = 0
      rw [map_sub]
      change S.mkQL μ-(Submodule.Quotient.mk x) = 0
      rw [hx,sub_self]
    have hbad := hfar (μ-x) hmem
    rw [sub_sub_cancel] at hbad
    linarith
  obtain ⟨g,hgn,hg⟩ := exists_dual_vector'' ℝ (S.mkQL μ)
  let T := g.comp S.mkQL
  have hT : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    exact (g.le_opNorm _).trans (by
      have hm := Submodule.Quotient.norm_mk_le S v
      change ‖S.mkQL v‖ ≤ ‖v‖ at hm
      change ‖g‖ * ‖S.mkQL v‖ ≤ 1 * ‖v‖
      exact mul_le_mul hgn hm (norm_nonneg _) zero_le_one)
  have hf : LipschitzWith 1 (fun x => T (point x)) :=
    (dual_point_lipschitz T).weaken (by exact_mod_cast hT)
  refine ⟨(fun x => T (point x)),hf,by simp,?_,?_⟩
  · intro x hx
    change g (Submodule.Quotient.mk (point x)) = 0
    rw [(Submodule.Quotient.mk_eq_zero S).mpr (point_mem_supported hx),map_zero]
  · intro hf'
    have he : normalized (fun x => T (point x)) hf' =
        normalized (fun x => T (point x)) (dual_point_lipschitz T) := rfl
    rw [he,dual_as_test]
    change ε ≤ g (S.mkQL μ)
    rw [hg]
    exact hnorm

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.LocalizedLinearization
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} {E : Type uE} [MetricSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [Zero M]

end LipschitzCounterexample.LocalizedLinearization

end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.FreeSpace
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open scoped NNReal Topology
open Filter Set LocalizedLinearization


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.FreeSpace.exists_vanishing_test.{uM} := @_root_.OAI.LipschitzCounterexample.FreeSpace.exists_vanishing_test.{uM}
