-- Prove2me | solution 1 for OAI.LipschitzCounterexample.CompactWSC.exists_detecting_sequence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:12:47.799064+00:00
-- url     : https://prove2.me/submissions/2a8b77f8-7a7a-4163-9135-5f6ec3d1e6e5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/DetectingSequence.lean:L104-L165
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.CompactWSC.exists_detecting_sequence. The node keeps its source
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
import Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_ConstructionPrefix_extend

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

end ConstructionPrefix

theorem exists_detecting_sequence {K Q : Set H} (hQ : IsCompact Q)
    {C ρ α : ℝ} {μ : ℕ → Space H} (hC : 0 ≤ C) (hα : 0 < α)
    (hRich : (triangularRows K C ρ α μ).Rich) (ε η : ℕ → ℝ)
    (hε : ∀ i, 0 < ε i) (hη : ∀ i, 0 < η i) :
    ∃ (z w : ℕ → Smooth H) (a : ℕ → RowItem K C ρ μ),
      (∀ i, LipschitzWith 1 (z i).val) ∧
      (∀ i, (z i).val 0 = 0 ∧ (w i).val 0 = 0) ∧
      (∀ i, α ≤ smoothPair (a i).a (z i)) ∧
      (∀ i j, j < i → gradMass (a i).a (z j) ≤ η j) ∧
      ∀ i x, x ∈ Q →
        ‖Smooth.grad x (w i)-damping (Finset.range i) z x • Smooth.grad x (z i)‖ ≤ ε i := by
  classical
  obtain ⟨v,hv⟩ := hRich 1
  let p0 : ConstructionPrefix K Q C ρ α μ ε η 0 := {
    z := fun _ => 0
    w := fun _ => 0
    a := fun _ => v 0
    lip := fun i hi => (Nat.not_lt_zero i hi).elim
    zero := fun i hi => (Nat.not_lt_zero i hi).elim
    high := fun i hi => (Nat.not_lt_zero i hi).elim
    mass := fun i _ _ hi => (Nat.not_lt_zero i hi).elim
    error := fun i hi => (Nat.not_lt_zero i hi).elim
    rich := fun N => by
      obtain ⟨v,hv⟩ := hRich N
      exact ⟨v,hv,fun _ i hi => (Nat.not_lt_zero i hi).elim⟩ }
  have hex (n : ℕ) (p : ConstructionPrefix K Q C ρ α μ ε η n) :=
    p.extend hQ hC hα hε hη
  let next (n : ℕ) (p : ConstructionPrefix K Q C ρ α μ ε η n) := (hex n p).choose
  have hn (n : ℕ) (p : ConstructionPrefix K Q C ρ α μ ε η n) (i : ℕ) (hi : i < n) :
      (next n p).z i = p.z i ∧ (next n p).w i = p.w i ∧ (next n p).a i = p.a i :=
    (hex n p).choose_spec i hi
  let p : (n : ℕ) → ConstructionPrefix K Q C ρ α μ ε η n := Nat.rec p0 next
  have hp (n : ℕ) : p (n+1) = next n (p n) := rfl
  have hstable (i m : ℕ) (him : i < m) :
      (p m).z i = (p (i+1)).z i ∧ (p m).w i = (p (i+1)).w i ∧
      (p m).a i = (p (i+1)).a i := by
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases hi : i < m
      · rw [hp]
        exact ⟨(hn m (p m) i hi).1.trans (ih hi).1,
          (hn m (p m) i hi).2.1.trans (ih hi).2.1,
          (hn m (p m) i hi).2.2.trans (ih hi).2.2⟩
      · have : m = i := by omega
        subst m
        exact ⟨rfl,rfl,rfl⟩
  let z := fun i => (p (i+1)).z i
  let w := fun i => (p (i+1)).w i
  let a := fun i => (p (i+1)).a i
  refine ⟨z,w,a,fun i => (p (i+1)).lip i (by omega),
    fun i => (p (i+1)).zero i (by omega),fun i => (p (i+1)).high i (by omega),?_,?_⟩
  · intro i j hji
    have hm := (p (i+1)).mass i j hji (by omega)
    rw [(hstable j (i+1) (by omega)).1] at hm
    exact hm
  · intro i x hx
    have he := (p (i+1)).error i (by omega) x hx
    have hd : damping (Finset.range i) (p (i+1)).z x = damping (Finset.range i) z x :=
      damping_congr i (fun j hj => (hstable j (i+1) (by omega)).1) x
    rw [hd] at he
    exact he

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace


theorem solution.{uH} : type_of% @_root_.OAI.LipschitzCounterexample.CompactWSC.exists_detecting_sequence.{uH} := @_root_.OAI.LipschitzCounterexample.CompactWSC.exists_detecting_sequence.{uH}
