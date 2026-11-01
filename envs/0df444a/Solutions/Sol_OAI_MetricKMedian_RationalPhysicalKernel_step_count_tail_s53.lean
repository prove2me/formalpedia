-- Prove2me | solution 1 for OAI.MetricKMedian.RationalPhysicalKernel.step_count_tail_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:31:05.201983+00:00
-- url     : https://prove2.me/submissions/bd3e14b3-ccab-497d-b982-3b4b1c00f118

import Mathlib
import Definitions.Def_OAIQ053K020
import Definitions.Def_OAIQ053K037
import Definitions.Def_OAIQ053K039
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_graph_data_s53
import Theorems.Thm_OAI_MetricKMedian_SparseCopyState_physical_count_tail_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Process_FiniteGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteGraph

variable {I H : Type*} [Fintype H] [DecidableEq I] [DecidableEq H]

theorem mem_touching (E : H → Finset I) (S : Finset I) (h : H) :
    h ∈ touching E S ↔ ∃ i ∈ S, i ∈ E h := by
  simp only [touching, Finset.mem_biUnion, incoming, Finset.mem_filter,
    Finset.mem_univ, true_and]

end MetricKMedian.FiniteGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalBatchData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch PhysicalPotential
variable {I E : Type} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

theorem graph_eq (G : I → Finset I) : graph G=graphActions G := rfl

omit [DecidableEq I] in
theorem cast_amount (m : I → ℚ) : (amount m:ℝ)=SourceBalance.amount (fun i => (m i:ℝ)) := by
  simp only [amount,SourceBalance.amount,Rat.cast_sum,Rat.cast_max,Rat.cast_sub,Rat.cast_one,Rat.cast_zero]

omit [DecidableEq I] [Fintype I] in
theorem cast_bias (m : I → ℚ) (p φ : ℚ) (i : I) :
    (bias m p φ i:ℝ)=SourceBalance.bias (fun i => (m i:ℝ)) (p:ℝ) (φ:ℝ) i := by
  have he : (1:ℚ)< m i ↔ (1:ℝ)<(m i:ℝ) := by exact_mod_cast Iff.rfl
  simp only [bias,SourceBalance.bias,he]
  split_ifs <;> simp only [Rat.cast_mul,Rat.cast_add,Rat.cast_one]

theorem cast_graphMass (G : I → Finset I) (g : ℚ) (h : I) :
    (graphMass G g h:ℝ)=mass (g:ℝ) ((graphActions G).erase h) := by
  simp only [graphMass,graph_eq,Rat.cast_mul,Rat.cast_natCast,mass]

omit [DecidableEq I] in
theorem heavySet_eq (m : I → ℚ) (b : ℚ) :
    heavySet m b=univ.filter (fun i => max (1:ℝ) ((b:ℝ)*SourceBalance.amount (fun i => (m i:ℝ)))<(m i:ℝ)) := by
  ext i
  simp only [heavySet,mem_filter,mem_univ,true_and,← cast_amount]
  exact_mod_cast (Iff.rfl : max (1:ℚ) (b*amount m)< m i ↔ max (1:ℚ) (b*amount m)< m i)

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseRealExpectation
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

theorem expectation_def (μ : SparseIntegerLaw α) (f : α → ℝ) :
    μ.expectation f=∑ i : Fin μ.length, (μ.law.rational.weight i:ℝ)*f μ.states[i.val] := rfl

theorem expectation_bindIndexed (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (f : β → ℝ) :
    (μ.bindIndexed κ).expectation f=
      ∑ a, (μ.law.rational.weight a:ℝ)*(κ a).expectation f := by
  let ρ := μ.law.rational.sigma (fun a => (κ a).law.rational)
  calc
    _ = ∑ z, (ρ.weight z:ℝ)*f (κ z.1).states[z.2.val] := by
      unfold expectation realIndex
      change (∑ i, (((ρ.integer.reindex finSigmaFinEquiv).rational.weight i):ℝ)*
        f ((Vector.ofFn (fun j => let z := finSigmaFinEquiv.symm j;
          (κ z.1).states[z.2.val]))[i.val])) = _
      simp only [Vector.getElem_ofFn]
      change (∑ i, (ρ.integer.rational.weight (finSigmaFinEquiv.symm i):ℝ)*
        f (κ (finSigmaFinEquiv.symm i).1).states[(finSigmaFinEquiv.symm i).2.val]) = _
      simp only [RationalLaw.integer_weight]
      exact (finSigmaFinEquiv (n := fun a => (κ a).length)).symm.sum_comp
        (fun z : Sigma (fun a : Fin μ.length => Fin (κ a).length) =>
          (ρ.weight z:ℝ)*f (κ z.1).states[z.2.val])
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [ρ,RationalLaw.sigma,Rat.cast_mul,mul_assoc,← mul_sum,expectation_def]

theorem expectation_map (μ : SparseIntegerLaw α) (g : α → β) (f : β → ℝ) :
    (μ.map g).expectation f=μ.expectation (fun a => f (g a)) := by
  simp only [expectation_def,map,Vector.getElem_map]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseMixture
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

theorem real_expect_all [Fintype α] [DecidableEq α] (μ : SparseIntegerLaw α) (f : α → ℝ) :
    μ.real.expect f=μ.expectation f := by
  rw [real,FiniteLaw.expect_map]
  rfl

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalBatchFacts
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch PhysicalPotential
variable {I E : Type} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

omit [Fintype I] in
theorem conflicts_eq (D : Actions I E) (Δ : ℕ) (e : E) :
    conflicts D Δ e=balancedConflicts D Δ e := by
  unfold conflicts balancedConflicts balanced balancedActions
  split_ifs with he
  · ext f
    constructor
    · intro hf
      obtain ⟨hb,hne,i,hi⟩ := mem_filter.mp hf
      apply mem_erase.mpr
      refine ⟨hne,mem_inter.mpr ⟨?_,hb⟩⟩
      exact (FiniteGraph.mem_touching _ _ _).mpr ⟨i,(mem_inter.mp hi).1,(mem_inter.mp hi).2⟩
    · intro hf
      obtain ⟨hne,hf⟩ := mem_erase.mp hf
      obtain ⟨ht,hb⟩ := mem_inter.mp hf
      obtain ⟨i,hi,hif⟩ := (FiniteGraph.mem_touching _ _ _).mp ht
      exact mem_filter.mpr ⟨hb,hne,⟨i,mem_inter.mpr ⟨hi,hif⟩⟩⟩
  · rfl

theorem proposal_eq (G : I → Finset I) (Δ : ℕ) (g β p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1) {n : ℕ}
    (enum : Fin n ≃ HeavyAction (graph G) (heavySet (graphMass G g) β))
    (hpp : 0 ≤ p ∧ p ≤ 1)
    (hq : ∀ e : HeavyAction (graph G) (heavySet (graphMass G g) β),
      0 ≤ bias (graphMass G g) p φ (heavyParent (graph G) _ e) ∧
      bias (graphMass G g) p φ (heavyParent (graph G) _ e) ≤ 1) :
    proposal G Δ g β p φ hp hφ hupper enum =
      SparseEnumeratedBatch.law enum
        (balancedActions (heavyActions (graphActions G) (heavySet (graphMass G g) β)) Δ)
        (balancedConflicts (heavyActions (graphActions G) (heavySet (graphMass G g) β)) Δ)
        p (fun e => bias (graphMass G g) p φ (heavyParent (graph G) _ e)) hpp hq := by
  unfold proposal
  dsimp only
  congr 1
  funext e
  exact conflicts_eq _ _ e

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalRoundEvents
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

theorem events_expectation (μ : SparseIntegerLaw (I → Finset I)) (Δ : ℕ) (g β p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1) (V : Event I g β → ℝ) :
    (events μ Δ g β p φ hp hφ hupper).expectation V=
      μ.expectation (fun G =>
        (proposal G Δ g β p φ hp hφ hupper
          (enumeration (graph G) (heavySet (graphMass G g) β))).expectation (fun Z => V ⟨G,Z⟩)) := by
  rw [events,SparseIntegerLaw.expectation_bindIndexed]
  simp only [SparseIntegerLaw.expectation_def,SparseIntegerLaw.map,Vector.getElem_map]

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalKernel
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset
variable {F : Type} [LinearOrder F] [Fintype F] {Δ : ℕ}

attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.instLinearOrderCopy
omit [Fintype F] in

theorem step_expectation (d : F → F → ℚ) (g β p φ P : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β) (V : State F Δ g β → ℝ) :
    (step d g β p φ P hp hφ hupper s).expectation V=
      (graphLaw d g P s.1).expectation (fun G =>
        (RationalBatchData.proposal G Δ g β p φ hp hφ hupper
          (RationalBatchData.enumeration (RationalBatchData.graph G)
            (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))).expectation
          (fun Z => V (updateEvent g β s.1 ⟨G,Z⟩))) := by
  exact (SparseIntegerLaw.expectation_map
    (RationalBatchData.events (graphLaw d g P s.1) Δ g β p φ hp hφ hupper)
    (updateEvent g β s.1) V).trans
      (RationalBatchData.events_expectation (graphLaw d g P s.1) Δ g β p φ hp hφ hupper
        (fun e => V (updateEvent g β s.1 e)))

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalProposalCount
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch PhysicalPotential
variable {I : Type} [DecidableEq I] [Fintype I]

theorem graph_heavy_eq (G : I → Finset I) (g β : ℚ) :
    heavySet (graphMass G g) β=
      univ.filter (fun h => max (1:ℝ)
        ((β:ℝ)*SourceBalance.amount (fun h => mass (g:ℝ) ((graphActions G).erase h)))<
        mass (g:ℝ) ((graphActions G).erase h)) := by
  simpa only [cast_graphMass] using heavySet_eq (graphMass G g) β

end MetricKMedian.RationalBatchData

namespace MetricKMedian.RationalBatchData
open Finset FixedBatch PhysicalPotential
variable {F : Type} [DecidableEq F] {Δ n : ℕ}

theorem proposal_count_tail (A : Finset (CopyState.Copy (F := F) Δ)) (G : A → Finset A)
    (g β p φ : ℚ) (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (enum : Fin n ≃ HeavyAction (graph G) (heavySet (graphMass G g) β))
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
    (hφ : 0 < (φ:ℝ)) (hφ1 : (φ:ℝ) ≤ 1) (hβ : 0 < (β:ℝ))
    (hunit : (g:ℝ)*(Δ:ℝ)=1) (hG : ∀ i, (G i).card=Δ)
    (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ (φ:ℝ)*(g:ℝ)) :
    (proposal G Δ g β p φ hp0 hφ0 hupper enum).real.prob
      (fun Z => mass (g:ℝ) A+4/((g:ℝ)*(β:ℝ)) <
        mass (g:ℝ) (transition A G (heavySet (graphMass G g) β) Z)) ≤
      96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ)) := by
  have hpp : 0 ≤ p ∧ p ≤ 1 := ⟨hp0,by have hh := mul_nonneg hp0 hφ0; nlinarith only [hh,hupper]⟩
  let H := heavySet (graphMass G g) β
  let q := fun e : HeavyAction (graph G) H => bias (graphMass G g) p φ (heavyParent (graph G) H e)
  have hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1 := fun e => bias_probability _ hp0 hφ0 hupper _
  have hh := @SparseCopyState.physical_count_tail_s53 F _ Δ n A G g p (φ:ℝ) (β:ℝ)
    hg hg1 hp hφ hφ1 hβ hunit hG hpp hsmall
  dsimp only at hh
  rw [← graph_heavy_eq G g β] at hh
  have hqcast : ∀ e, (q e:ℝ)=SourceBalance.bias
      (fun h => mass (g:ℝ) ((graphActions G).erase h)) (p:ℝ) (φ:ℝ)
      (heavyParent (graph G) H e) := by
    intro e
    simpa only [q,cast_graphMass] using cast_bias (graphMass G g) p φ (heavyParent (graph G) H e)
  have ht := hh enum q hq hqcast
  rw [proposal_eq G Δ g β p φ hp0 hφ0 hupper enum hpp hq]
  exact ht

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalCount
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}

attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.rationalPhysicalCountCopyOrder
omit [Fintype F] in

theorem step_count_tail_s53_oai (d : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
    (g β p φ P : ℚ) (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β)
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
    (hφ : 0 < (φ:ℝ)) (hφ1 : (φ:ℝ) ≤ 1) (hβ : 0 < (β:ℝ))
    (hunit : (g:ℝ)*(Δ:ℝ)=1) (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hA : 1 ≤ mass (g:ℝ) s.1) (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ (φ:ℝ)*(g:ℝ)) :
    (step d g β p φ P hp0 hφ0 hupper s).expectation
      (fun t => if mass (g:ℝ) s.1+4/((g:ℝ)*(β:ℝ)) < mass (g:ℝ) t.1 then 1 else 0) ≤
      96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ)) := by
  let μ := graphLaw d g P s.1
  let ν : (G : s.1 → Finset s.1) → SparseIntegerLaw
      (Finset (FixedBatch.HeavyAction (RationalBatchData.graph G)
        (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))) :=
    fun G => RationalBatchData.proposal G Δ g β p φ hp0 hφ0 hupper
      (RationalBatchData.enumeration (RationalBatchData.graph G)
        (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))
  let V := fun (G : s.1 → Finset s.1) Z =>
    if mass (g:ℝ) s.1+4/((g:ℝ)*(β:ℝ)) < mass (g:ℝ)
      (RationalBatchData.transition s.1 G
        (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β) Z) then (1:ℝ) else 0
  obtain ⟨D,hgood,_,_⟩ := graph_data_s53 d location hd g P s.1 hg hunit hP hP1 hA
  have hc : ∀ G, 0 < μ.real.weight G → (ν G).real.expect (V G) ≤
      96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ)) := by
    intro G hG
    exact RationalBatchData.proposal_count_tail s.1 G g β p φ hp0 hφ0 hupper
      (RationalBatchData.enumeration (RationalBatchData.graph G)
        (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))
      hg hg1 hp hφ hφ1 hβ hunit (hgood G hG).1 hsmall
  have hh := μ.real.expect_mono_support hc
  rw [FiniteLaw.expect_const] at hh
  rw [step_expectation, ← SparseIntegerLaw.real_expect_all]
  change μ.real.expect (fun G => (ν G).expectation (V G)) ≤ _
  have he : ∀ G, (ν G).expectation (V G)=(ν G).real.expect (V G) :=
    fun G => (SparseIntegerLaw.real_expect_all (ν G) (V G)).symm
  simp_rw [he]
  exact hh

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.RationalPhysicalKernel.step_count_tail_s53_oai := @OAI.MetricKMedian.RationalPhysicalKernel.step_count_tail_s53_oai
