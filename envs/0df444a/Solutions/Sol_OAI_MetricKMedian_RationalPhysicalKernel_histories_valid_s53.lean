-- Prove2me | solution 1 for OAI.MetricKMedian.RationalPhysicalKernel.histories_valid_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:30:40.816513+00:00
-- url     : https://prove2.me/submissions/184bbe13-6d77-4b05-bf54-f07109da0640

import Mathlib
import Definitions.Def_OAIQ053K037
import Definitions.Def_OAIQ053K039
import Definitions.Def_OAIQ053K043
import Theorems.Thm_OAI_MetricKMedian_CopyState_valid_advance_s53
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_graph_data_all_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Process_StateInvariants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F J X : Type*} [Fintype F] [DecidableEq F] [Fintype J] [DecidableEq J]
variable [PseudoMetricSpace X] {Δ : ℕ}

omit [Fintype J] [DecidableEq J] in
 theorem valid_initial (A : Finset (Copy (F := F) Δ)) (S₀ : J → Finset (Copy (F := F) Δ))
    (g : ℝ) (location : F → X) (client : J → X) (R : J → ℝ)
    (hA : 1 ≤ mass g A) (hS : ∀ j, S₀ j ⊆ A) : Valid g location client R S₀ (A,S₀) :=
  ⟨hA,hS,fun _ => Subset.rfl,fun j _ => hS j⟩

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalRoundEvents
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch
variable {I : Type} [LinearOrder I] [Fintype I]

theorem events_property (μ : SparseIntegerLaw (I → Finset I)) (Δ : ℕ) (g β p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (Q : Event I g β → Prop)
    (hQ : ∀ i : Fin μ.length, ∀ Z : Finset (HeavyAction (graph μ.states[i.val])
      (heavySet (graphMass μ.states[i.val] g) β)), Q ⟨μ.states[i.val],Z⟩) :
    ∀ i : Fin (events μ Δ g β p φ hp hφ hupper).length,
      Q (events μ Δ g β p φ hp hφ hupper).states[i.val] := by
  apply SparseIntegerLaw.bindIndexed_property _ _ Q
  intro i j
  have he := SparseIntegerLaw.map_states
    (proposal μ.states[i.val] Δ g β p φ hp hφ hupper
      (enumeration (graph μ.states[i.val]) (heavySet (graphMass μ.states[i.val] g) β)))
    (fun Z => (⟨μ.states[i.val],Z⟩ : Event I g β)) j
  rw [he]
  exact hQ i _

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset
variable {F J : Type} [LinearOrder F] {Δ : ℕ}

theorem replay_extend (g β : ℚ) (x : ℕ → ℝ) (d : J → F → ℝ)
    (S₀ : J → Finset (CopyState.Copy (F := F) Δ))
    (h : SparseHistories.History (State F Δ g β)) (s : State F Δ g β) :
    replay g β x d S₀ (SparseHistories.extend h s)=
      labels g β (x h.2.length) d s (replay g β x d S₀ h) := by
  simp only [replay,SparseHistories.extend,replayList,List.length_cons,Nat.add_sub_cancel]

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalHistoryValid
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F J X : Type} [LinearOrder F] [Fintype F] [Fintype J] [DecidableEq J]
  [PseudoMetricSpace X] {Δ : ℕ}

attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.rationalHistoryValidCopyOrder
omit [Fintype J] [DecidableEq J] in
theorem histories_valid_s53_oai (d₀ : F → F → ℚ) (location : F → X) (client : J → X)
    (hd₀ : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (S₀ : J → Finset (CopyState.Copy (F := F) Δ))
    (R : J → ℝ) (T : ℕ) (x : ℕ → ℝ)
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t<T, 0<(P t:ℝ)) (hP1 : ∀ t<T, (P t:ℝ)≤1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hSA : ∀ j, S₀ j⊆A)
    (hR : ∀ j, 0≤R j) (hm : ∀ j, mass (g:ℝ) (S₀ j)=1)
    (hdR : ∀ j i, i∈S₀ j → dist (client j) (location i.1)≤R j)
    (a : Fin (histories d₀ g β p φ P hp hφ hupper A T).length) :
    let z := (histories d₀ g β p φ P hp hφ hupper A T).states[a.val];
    CopyState.Valid (g:ℝ) location client R S₀
      (z.1.1, replay g β x (fun j f => dist (client j) (location f)) S₀ z) := by
  let d := fun j f => dist (client j) (location f)
  let κ := fun t => step (Δ:=Δ) d₀ g β p φ (P t) hp hφ hupper
  have hh : ∀ t≤T, ∀ a : Fin (SparseHistories.tree κ (A,none) t).length,
      let z := (SparseHistories.tree κ (A,none) t).states[a.val];
      CopyState.Valid (g:ℝ) location client R S₀ (z.1.1,replay g β x d S₀ z) := by
    intro t
    induction t with
    | zero =>
      intro _ a
      simpa only [SparseHistories.tree,SparseIntegerLaw.dirac,Vector.getElem_replicate,
        replay,replayList,labels] using CopyState.valid_initial A S₀ (g:ℝ) location client R hA hSA
    | succ t ih =>
      intro ht
      simp only [SparseHistories.tree]
      apply SparseIntegerLaw.bindIndexed_property _ _ (fun z =>
        CopyState.Valid (g:ℝ) location client R S₀ (z.1.1,replay g β x d S₀ z))
      intro b c
      let z := (SparseHistories.tree κ (A,none) t).states[b.val]
      have hv := ih (by omega) b
      have he := SparseIntegerLaw.map_states (κ t z.1) (SparseHistories.extend z) c
      change (SparseHistories.branch (κ t) z).states[c.val]=_ at he
      rw [he]
      rw [replay_extend]
      obtain ⟨D,hD⟩ := graph_data_all_s53 d₀ location hd₀ g (P t) z.1.1 hg hunit
        (hP t (by omega)) (hP1 t (by omega)) hv.1
      have hprop := RationalBatchData.events_property (graphLaw d₀ g (P t) z.1.1) Δ g β p φ
        hp hφ hupper (fun e => CopyState.Valid (g:ℝ) location client R S₀
          ((updateEvent g β z.1.1 e).1,
            labels g β (x z.2.length) d (updateEvent g β z.1.1 e) (replay g β x d S₀ z)))
        (fun i Z => by
          exact CopyState.valid_advance_s53 (z.1.1,replay g β x d S₀ z) S₀ location client R D
            (graphLaw d₀ g (P t) z.1.1).states[i.val]
            (RationalBatchData.heavySet
              (RationalBatchData.graphMass (graphLaw d₀ g (P t) z.1.1).states[i.val] g) β)
            Z (x z.2.length) hg.le hunit (hP t (by omega)) (hP1 t (by omega)) hR hm hdR (hD i) hv)
      have hevent := SparseIntegerLaw.map_states
        (RationalBatchData.events (graphLaw d₀ g (P t) z.1.1) Δ g β p φ hp hφ hupper)
        (updateEvent g β z.1.1) c
      change (κ t z.1).states[c.val]=_ at hevent
      simpa only [SparseHistories.extend,hevent] using hprop c
  exact hh T le_rfl a

end MetricKMedian.RationalPhysicalKernel
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.RationalPhysicalKernel.histories_valid_s53_oai := @OAI.MetricKMedian.RationalPhysicalKernel.histories_valid_s53_oai
