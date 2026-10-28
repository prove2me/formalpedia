-- Prove2me | solution 1 for OAI.MetricKMedian.RationalPhysicalKernel.histories_count_tail_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:25:25.966665+00:00
-- url     : https://prove2.me/submissions/5f3482c5-e53a-4154-ac12-2f76483a7a44

import Mathlib
import Definitions.Def_OAIQ035K045
import Definitions.Def_OAIQ035K047
import Theorems.Thm_OAI_MetricKMedian_RationalBatchData_proposal_count_tail_s35
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_graph_data_s35
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_mass_s35
import Theorems.Thm_OAI_MetricKMedian_SparseHistories_count_tail_up_to_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseRealExpectation
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseMixture
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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalRoundEvents
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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalKernel
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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalCount
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

theorem step_count_tail (d : F → F → ℚ) (location : F → X)
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
  obtain ⟨D,hgood,_,_⟩ := graph_data_s35 d location hd g P s.1 hg hunit hP hP1 hA
  have hc : ∀ G, 0 < μ.real.weight G → (ν G).real.expect (V G) ≤
      96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ)) := by
    intro G hG
    exact RationalBatchData.proposal_count_tail_s35 s.1 G g β p φ hp0 hφ0 hupper
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

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalHistoryCount
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

omit [Fintype F] in

theorem histories_count_tail_s35_oai (d : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ)
    (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ)
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
    (hφ : 0 < (φ:ℝ)) (hφ1 : (φ:ℝ) ≤ 1) (hβ : 0 < (β:ℝ))
    (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t < T, 0 < (P t:ℝ)) (hP1 : ∀ t < T, (P t:ℝ) ≤ 1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ (φ:ℝ)*(g:ℝ)) :
    (histories d g β p φ P hp0 hφ0 hupper A T).expectation
      (fun z => if mass (g:ℝ) A+(T:ℝ)*(4/((g:ℝ)*(β:ℝ))) < mass (g:ℝ) z.1.1 then 1 else 0) ≤
      (T:ℝ)*(96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ))) := by
  let κ := fun t => step (Δ := Δ) d g β p φ (P t) hp0 hφ0 hupper
  apply SparseHistories.count_tail_up_to_s35 κ (A,none)
    (fun s => mass (g:ℝ) s.1) (4/((g:ℝ)*(β:ℝ)))
    (96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ))) T
  intro t ht i hi
  have hm := histories_mass_s35 d g β p φ P hp0 hφ0 hupper A t hg.le hunit hA ⟨i,hi⟩
  exact step_count_tail d location hd g β p φ (P t) hp0 hφ0 hupper
    (SparseHistories.tree κ (A,none) t).states[i].1
    hg hg1 hp hφ hφ1 hβ hunit (hP t ht) (hP1 t ht) hm hsmall

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.RationalPhysicalKernel.histories_count_tail_s35_oai := @OAI.MetricKMedian.RationalPhysicalKernel.histories_count_tail_s35_oai
