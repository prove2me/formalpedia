-- Prove2me | solution 1 for OAI.LipschitzCounterexample.CompactWSC.ConstructionPrefix.extend
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:09:14.427207+00:00
-- url     : https://prove2.me/submissions/69cffa46-d4f4-4cc6-b21d-8fa2ac904df2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/DetectingSequence.lean:L37-L100
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.CompactWSC.ConstructionPrefix.extend. The node keeps its source
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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_DetectingSequence
import Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_selection_step

-- ---- from OAI.Analysis.LipschitzEquivalence.DetectingSequence ----
namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem damping_congr (n : ℕ) {z z' : ℕ → Smooth H}
    (h : ∀ i < n, z i = z' i) (x : H) :
    damping (Finset.range n) z x = damping (Finset.range n) z' x := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [h i (Finset.mem_range.mp hi)]

namespace ConstructionPrefix
variable {K Q : Set H} {C ρ α : ℝ} {μ : ℕ → Space H} {ε η : ℕ → ℝ}

theorem extend (hQ : IsCompact Q) (hC : 0 ≤ C) (hα : 0 < α)
    (hε : ∀ i, 0 < ε i) (hη : ∀ i, 0 < η i) {n : ℕ}
    (p : ConstructionPrefix K Q C ρ α μ ε η n) :
    ∃ q : ConstructionPrefix K Q C ρ α μ ε η (n+1),
      ∀ i < n, q.z i = p.z i ∧ q.w i = p.w i ∧ q.a i = p.a i := by
  classical
  obtain ⟨f,w,a,hf,hf0,hw0,hPa,hhigh,herr,hrich⟩ :=
    selection_step hQ hC hα _ p.rich (fun i : Fin n => p.z i)
      (fun i => p.lip i i.isLt) (hε n) (hη n)
  let z' := Function.update p.z n f
  let w' := Function.update p.w n w
  let a' := Function.update p.a n a
  have hz (i : ℕ) (hi : i < n) : z' i = p.z i := Function.update_of_ne (by omega) _ _
  have hw (i : ℕ) (hi : i < n) : w' i = p.w i := Function.update_of_ne (by omega) _ _
  have ha (i : ℕ) (hi : i < n) : a' i = p.a i := Function.update_of_ne (by omega) _ _
  have hzn : z' n = f := by simp [z']
  have hwn : w' n = w := by simp [w']
  have han : a' n = a := by simp [a']
  refine ⟨{
    z := z'
    w := w'
    a := a'
    lip := ?_
    zero := ?_
    high := ?_
    mass := ?_
    error := ?_
    rich := ?_ },fun i hi => ⟨hz i hi,hw i hi,ha i hi⟩⟩
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi|rfl
    · rw [hz i hi]; exact p.lip i hi
    · rw [hzn]; exact hf
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi|rfl
    · rw [hz i hi,hw i hi]; exact p.zero i hi
    · rw [hzn,hwn]; exact ⟨hf0,hw0⟩
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi|rfl
    · rw [hz i hi,ha i hi]; exact p.high i hi
    · rw [hzn,han]; exact hhigh
  · intro i j hji hi
    have hj : j < n := by omega
    rw [hz j hj]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi|rfl
    · rw [ha i hi]; exact p.mass i j hji hi
    · rw [han]; exact hPa j hj
  · intro i hi x hx
    have hd : damping (Finset.range i) z' x = damping (Finset.range i) p.z x :=
      damping_congr i (fun j hj => hz j (by omega)) x
    rw [hd]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi|rfl
    · rw [hz i hi,hw i hi]; exact p.error i hi x hx
    · rw [hzn,hwn]
      have he := herr x hx
      have hprod := Fin.prod_univ_eq_prod_range (fun j => 1-‖Smooth.grad x (p.z j)‖) i
      change ‖Smooth.grad x w-(∏ j : Fin i, (1-‖Smooth.grad x (p.z j)‖)) • Smooth.grad x f‖ ≤ ε i at he
      rw [hprod] at he
      exact he
  · intro N
    obtain ⟨v,hv,hP⟩ := hrich N
    refine ⟨v,hv,fun i j hj => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj|rfl
    · rw [hz j hj]; exact (hP i).1 j hj
    · rw [hzn]; exact (hP i).2

end ConstructionPrefix

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC OAI.LipschitzCounterexample.CompactWSC.ConstructionPrefix
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace


theorem solution.{uH} : type_of% @_root_.OAI.LipschitzCounterexample.CompactWSC.ConstructionPrefix.extend.{uH} := @_root_.OAI.LipschitzCounterexample.CompactWSC.ConstructionPrefix.extend.{uH}
