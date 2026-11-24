-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.chi_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:05:12.822649+00:00
-- url     : https://prove2.me/submissions/1c7c5298-9e56-4334-8808-2b59148e9f89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFrameProperties
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_norm_ne_zero_of_isUnit
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_e_mul_eS
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_eS_idem
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_eta_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Filter Topology
variable {K : UQ} (B : InvAlg K)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution {e π : ι → B.A} {S : Finset ι} (h : IsFrame B e π S) (I J : Finset ι) (hJ : J ⊆ S) :
    chi B e I (∏ j ∈ J, π j) = (-1) ^ (J ∩ I).card := by
  have he := h.1.1.toOrthogonalIdempotents
  set E := eS B e I with hEdef
  have hE := eS_idem B he I

  have h1 : (∏ j ∈ J.filter (· ∉ I), π j) * E = E := by
    refine Finset.prod_induction _ (fun t => t * E = E) (fun a b ha hb => by rw [mul_assoc, hb, ha]) (one_mul _) ?_
    intro j hj
    obtain ⟨hjJ, hjI⟩ := Finset.mem_filter.1 hj
    have hEe : E = (1 - e j) * E := by
      rw [sub_mul, one_mul, mul_comm (e j) E, hEdef, mul_comm, e_mul_eS B he, if_neg hjI, sub_zero]
    show π j * E = E
    rw [hEe, ← mul_assoc, (h.2 j (hJ hjJ)).2.1]
  have h2 : (∏ j ∈ J.filter (· ∈ I), π j) * (1 - E) = 1 - E := by
    refine Finset.prod_induction _ (fun t => t * (1 - E) = 1 - E) (fun a b ha hb => by rw [mul_assoc, hb, ha]) (one_mul _) ?_
    intro j hj
    obtain ⟨hjJ, hjI⟩ := Finset.mem_filter.1 hj
    have hEe : 1 - E = (1 - e j) * (1 - E) := by
      have := e_mul_eS B he j I
      rw [if_pos hjI] at this
      rw [← hEdef] at this
      linear_combination -this
    show π j * (1 - E) = 1 - E
    rw [hEe, ← mul_assoc, (h.2 j (hJ hjJ)).2.1]
  have hprod : (∏ j ∈ J, π j) * E + (1 - E) = ∏ j ∈ J.filter (· ∈ I), π j := by
    rw [← Finset.prod_filter_mul_prod_filter_not J (· ∈ I), mul_assoc]
    rw [h1]
    linear_combination -h2
  unfold chi
  rw [← hEdef, hprod, map_prod, eta_prod]
  · rw [Finset.filter_mem_eq_inter]
    rw [Finset.prod_congr rfl fun j hj => (h.2 j (hJ (Finset.mem_inter.1 hj).1)).2.2, Finset.prod_const]
  · intro j hj
    exact norm_ne_zero_of_isUnit B (h.2 j (hJ (Finset.mem_filter.1 hj).1)).1.1
end GlobalTheory.UnitLemma.Desc
