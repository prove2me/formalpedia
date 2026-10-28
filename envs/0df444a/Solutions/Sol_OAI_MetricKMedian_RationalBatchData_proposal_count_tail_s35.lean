-- Prove2me | solution 1 for OAI.MetricKMedian.RationalBatchData.proposal_count_tail_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:17:16.944246+00:00
-- url     : https://prove2.me/submissions/9e5cec56-bb6e-4f5c-9d6d-789069704577

import Mathlib
import Definitions.Def_OAIQ035K011
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K039
import Definitions.Def_OAIQ035K040
import Theorems.Thm_OAI_MetricKMedian_SparseCopyState_physical_count_tail_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Process_FiniteGraph
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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalBatchData
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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalBatchFacts
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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalProposalCount
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

theorem proposal_count_tail_s35_oai (A : Finset (CopyState.Copy (F := F) Δ)) (G : A → Finset A)
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
  have hh := @SparseCopyState.physical_count_tail_s35 F _ Δ n A G g p (φ:ℝ) (β:ℝ)
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

theorem solution : type_of% @OAI.MetricKMedian.RationalBatchData.proposal_count_tail_s35_oai := @OAI.MetricKMedian.RationalBatchData.proposal_count_tail_s35_oai
