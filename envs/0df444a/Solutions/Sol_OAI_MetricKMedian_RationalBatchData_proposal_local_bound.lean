-- Prove2me | solution 1 for OAI.MetricKMedian.RationalBatchData.proposal_local_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:43:45.312989+00:00
-- url     : https://prove2.me/submissions/bdd45e4b-bba9-40bf-a162-5aaef10a3a87
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K039
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedFixedBatch_actual_local_bound

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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalProposalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset PhysicalPotential Analytic FixedBatch
variable {I : Type} [DecidableEq I] [Fintype I] {n : ℕ}

theorem proposal_local_bound_oai (G : I → Finset I) (S F : Finset I) (Δ : ℕ)
    (g β p φ : ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (enum : Fin n ≃ HeavyAction (graph G) (heavySet (graphMass G g) β))
    {x h R b b' : ℝ} (d : I → ℝ)
    (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hG : ∀ i, (G i).card=Δ) (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hφ1 : (φ:ℝ) ≤ 1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction (g:ℝ))
    (hy : mass (g:ℝ) S ≤ 1) (hF : F ⊆ S) (hHS : heavySet (graphMass G g) β ∩ S ⊆ F)
    (hd0 : ∀ i, 0 ≤ d i) (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S, d i ≤ R)
    (hbQ : b ≤ 5*((PhysicalPotential.cost (g:ℝ) d S+(1-mass (g:ℝ) S)*b)/(g:ℝ)))
    (hb0 : 0 ≤ b) (hbR : b ≤ 5*R) (hb'0 : 0 ≤ b') (hb' : b' ≤ b)
    (hbF : ∀ i ∈ F, b' ≤ d i) (hbH : ∀ i ∈ heavySet (graphMass G g) β, b' ≤ d i) :
    let D := heavy (graph G) (heavySet (graphMass G g) β)
    (proposal G Δ g β p φ hp hφ hupper enum).real.expect (fun A =>
      potential (x*Real.exp (-h)) (g:ℝ) d
        (nextAliveAt D (coefficient x (mass (g:ℝ) S)) d (S \ F) A)
        (nextCap D d b' A)-potential x (g:ℝ) d S b) ≤
      h*(timeRate x (mass (g:ℝ) S)*PhysicalPotential.cost (g:ℝ) d S+
        (g:ℝ)*(∑ e ∈ relevant (graphActions G) S, charge (graphActions G) x (g:ℝ) b d S e))+
      batchConstant Δ*h*((φ:ℝ)+h)*R := by
  dsimp only
  let H := heavySet (graphMass G g) β
  let q := fun e : HeavyAction (graph G) H => bias (graphMass G g) p φ (heavyParent (graph G) H e)
  have hpp : 0 ≤ p ∧ p ≤ 1 := ⟨hp,by have hh := mul_nonneg hp hφ; nlinarith only [hh,hupper]⟩
  have hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1 := fun e => bias_probability _ hp hφ hupper _
  have hqb : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+(φ:ℝ))*(p:ℝ) := by
    intro e
    exact_mod_cast bias_bounds (graphMass G g) hp hφ (heavyParent (graph G) H e)
  have ht := SparseEnumeratedFixedBatch.actual_local_bound G H S F Δ enum p q hpp hq
    d hprob hG hg hg1 hunit hx0 hx1 hh0 hh1 (by exact_mod_cast hφ) hφ1 hqb hsmall
    hy hF hHS hd0 hR0 hdR hbQ hb0 hbR hb'0 hb' hbF hbH
  rw [proposal_eq G Δ g β p φ hp hφ hupper enum hpp hq]
  exact ht

end MetricKMedian.RationalBatchData
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.RationalBatchData.proposal_local_bound_oai := @OAI.MetricKMedian.RationalBatchData.proposal_local_bound_oai
