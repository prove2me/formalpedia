-- Prove2me | solution 1 for OAI.LipschitzCounterexample.SeparatingStages.D_local_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:22:15.464389+00:00
-- url     : https://prove2.me/submissions/a2209cdf-f681-48d6-8c62-9f215b3ad2ad

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SeparableCoordinates.lean:L190-L218
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.SeparatingStages.D_local_orthogonality. The node keeps its source
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
import Theorems.Thm_OAI_LipschitzCounterexample_SeparatingStages_finite_slot_locality

-- ---- from OAI.Analysis.LipschitzEquivalence.HilbertBijection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace
open HilbertSlots RadialBudget SlowAngles RotatingStages

end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter

theorem D_coord (x : M) (n : ℕ) :
    D x n = (scalarSlot slot x n - ⟪slot n x,x.fst n⟫_ℝ) • slot n x := by
  change movingSlotsMap slot norm_slot x n - x.fst n = _
  rw [movingSlotsMap_apply,slotCoord]
  abel

end LipschitzCounterexample.SeparatingStages

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.SeparableCoordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

theorem D_local_orthogonality {I : Type uI} [Fintype I] (x : I → M) (hx : Function.Injective x) :
    ∃ r : ℝ, 0 < r ∧ ∃ l : ℕ, ∃ S : I → Set (Σ n, BlockLabel n),
      (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
      (∀ i a, a ∈ S i → l ≤ a.1) ∧
      (∀ i y, y ∈ Metric.ball (x i) r → tailCLM l (D y) ∈ space (S i)) := by
  classical
  obtain ⟨r,hr,l,hl⟩ := finite_slot_locality x hx
  let S : I → Set (Σ n, BlockLabel n) := fun i =>
    {a | l ≤ a.1 ∧ ∃ y ∈ Metric.ball (x i) r, slot a.1 y a.2 ≠ 0}
  refine ⟨r,hr,l,S,?_,?_,?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro ⟨n,a⟩ ⟨hn,y,hy,hya⟩ ⟨_,z,hz,hza⟩
    exact (hl i j hij n hn y hy z hz a).elim hya hza
  · intro i a ha
    exact ha.1
  · intro i y hy
    rw [mem_space]
    rintro ⟨n,a⟩ ha
    rw [tailCLM_coord]
    by_cases hn : l ≤ n
    · rw [ite_eq_left hn, D_coord]
      change (scalarSlot slot y n - ⟪slot n y,y.fst n⟫_ℝ) * slot n y a = 0
      have hz : slot n y a = 0 := by
        by_contra h
        exact ha ⟨hn,y,hy,h⟩
      rw [hz,mul_zero]
    · rw [ite_eq_right hn]
      rfl

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
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.SeparatingStages
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set CoordinateSpaces


theorem solution.{uI} : type_of% @_root_.OAI.LipschitzCounterexample.SeparatingStages.D_local_orthogonality.{uI} := @_root_.OAI.LipschitzCounterexample.SeparatingStages.D_local_orthogonality.{uI}
