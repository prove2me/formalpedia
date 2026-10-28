-- Prove2me | solution 1 for OAI.MetricKMedian.RationalPhysicalKernel.graph_data
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:48:10.147997+00:00
-- url     : https://prove2.me/submissions/c45bf762-2f4d-40b4-ba9c-258849a38c89

import Mathlib
import Definitions.Def_OAIQ035K045
import Definitions.Def_OAIQ035K047
import Theorems.Thm_OAI_MetricKMedian_Taper_physical_sparse_graph

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset FixedBatch
variable {F : Type*} [DecidableEq F] [Fintype F] (Δ : ℕ)

omit [Fintype F] in
 theorem own_card_le (A : Finset (Copy (F := F) Δ)) (i : A) : (own Δ A i).card ≤ Δ := by
  have hc : (own Δ A i).image Subtype.val ⊆ slots Δ i.val.1 := by
    rintro h hh
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hh
    exact (mem_slots _ _ _).mpr ((mem_own _ _ _ _).mp ht)
  have hh := card_le_card hc
  rw [card_image_of_injective _ Subtype.val_injective,card_slots] at hh
  exact hh

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F : Type} [LinearOrder F] [Fintype F] {Δ : ℕ}

omit [Fintype F] in
                                                                        
theorem own_card (A : Finset (CopyState.Copy (F := F) Δ)) (i : A) :
    (own A i).card ≤ Δ := by
  exact CopyState.own_card_le Δ A i

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalGraphInstance
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

attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.instLinearOrderCopy_1
omit [Fintype F] in

theorem graph_data_oai (d : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
    (g P : ℚ) (A : Finset (CopyState.Copy (F := F) Δ))
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2) (hA : 1 ≤ mass (g:ℝ) A) :
    ∃ D : Taper.GraphData Δ (g:ℝ) (P:ℝ) (fun i : A => location i.val.1) (CopyState.own Δ A),
      (∀ G, 0 < (graphLaw d g P A).real.weight G → D.Good G) ∧
      (∀ h i, (graphLaw d g P A).real.expect (fun G => GraphLaw.edge G h i)=D.marginal h i) ∧
      (∀ h l i j, i≠j → (graphLaw d g P A).real.expect
        (fun G => GraphLaw.edge G h i*GraphLaw.edge G l j)=D.marginal h i*D.marginal l j) := by
  let dA : A → A → ℚ := fun i j => d i.val.1 j.val.1
  have hd0 : ∀ i j, 0 ≤ dA i j := by
    intro i j
    have hh : 0 ≤ (dA i j:ℝ) := by rw [← hd]; exact dist_nonneg
    exact_mod_cast hh
  have hown : ∀ i j, j∈own A i → dA i j=0 := by
    intro i j hj
    have he : j.val.1=i.val.1 := (mem_filter.mp hj).2
    have hh : (dA i j:ℝ)=0 := by rw [← hd,he,dist_self]
    exact_mod_cast hh
  have htotal : 1 ≤ ∑ _i : A, (g:ℝ) := by
    simpa only [sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul,mass,mul_comm] using hA
  let D := Taper.physicalGraphData Δ g P dA (fun i : A => location i.val.1) (own A)
    hg hunit hP hP1 hd0 (fun i j => hd _ _) htotal hown (own_card A)
  have hh := Taper.physical_sparse_graph (enumeration A) Δ g P dA
    (fun i : A => location i.val.1) (own A) hg hunit hP hP1 hd0
      (fun i j => hd _ _) htotal hown (own_card A)
  exact ⟨D,hh.2⟩

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.RationalPhysicalKernel.graph_data_oai := @OAI.MetricKMedian.RationalPhysicalKernel.graph_data_oai
