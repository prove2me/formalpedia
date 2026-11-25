-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.iterationSum_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:12:12.073539+00:00
-- url     : https://prove2.me/submissions/3b45e1be-f7bd-4df0-a876-e0ffbb6df39f

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral
import Theorems.Thm_GlobalTheory_CompareIterDegree_l1_add_le
import Theorems.Thm_GlobalTheory_CompareIterDegree_comb_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CompareIterDegree
open Formalism.QuantumDeterminants Formalism.HermitianLatticeCounting.ExpansionTerms GlobalTheory.IndefiniteRowSideFullHecke.DegreeProportionalWords
namespace GlobalTheory.CompareIterDegree
theorem _root_.solution (h : Iteration) : IterationSum := by
  intro A V ι _ _ _ N M j D w lam R Γ hN hM hΓ hone L μ c hc
  classical
  have key : ∀ S : Finset A, S ⊆ c.support → ∃ c' : A →₀ ℂ,
      wordOp D L (∑ ν ∈ S, c ν • j (μ + ν)) = comb j μ c' ∧
      (∀ ν' ∈ c'.support, ∃ ν ∈ c.support, N (ν' - ν) ≤ (wordWt w L : ℝ) ∧ M (ν' - ν) ≤ (L.length : ℝ)) ∧
      l1 c' ≤ Γ ^ wordWt w L * ∑ ν ∈ S, ‖c ν‖ := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; exact ⟨0, by simp [comb], by simp, by simp [l1]⟩
    | insert ν S hν ih =>
      intro hS
      obtain ⟨c', h1, h2, h3⟩ := ih ((subset_insert _ _).trans hS)
      have hνc : ν ∈ c.support := hS (mem_insert_self _ _)
      obtain ⟨a, ha, hs, hl⟩ := h A V ι N M j D w lam R Γ hN hM hΓ hone L (μ + ν) (hc ν hνc)
      set b : A →₀ ℂ := c ν • Finsupp.equivMapDomain (Equiv.addLeft ν) a with hb
      have hbs : ∀ x, b x = c ν * a (x - ν) := by
        intro x; simp [hb, Finsupp.equivMapDomain_apply, neg_add_eq_sub]
      refine ⟨b + c', ?_, ?_, ?_⟩
      · rw [sum_insert hν, map_add, map_smul, h1, ha, comb_eq j μ (b + c'), map_add, hb, map_smul,
          Finsupp.equivMapDomain_eq_mapDomain, Finsupp.linearCombination_mapDomain, comb_eq, comb_eq]
        simp [Function.comp_def, add_assoc]
      · intro x hx
        rcases mem_union.1 (Finsupp.support_add hx) with hx | hx
        · refine ⟨ν, hνc, hs _ ?_⟩
          rw [Finsupp.mem_support_iff] at hx ⊢
          rw [hbs] at hx
          exact right_ne_zero_of_mul hx
        · exact h2 x hx
      · have hb1 : l1 b = ‖c ν‖ * l1 a := by
          have e1 : l1 b = (Finsupp.equivMapDomain (Equiv.addLeft ν) a).sum fun _ z => ‖c ν • z‖ :=
            Finsupp.sum_smul_index' (h := fun _ z => ‖z‖) (by simp)
          rw [e1, Finsupp.sum_equivMapDomain]
          simp [Finsupp.sum, l1, mul_sum]
        rw [sum_insert hν, mul_add]
        refine (l1_add_le _ _).trans (add_le_add ?_ h3)
        rw [hb1, mul_comm]
        exact mul_le_mul_of_nonneg_right hl (norm_nonneg _)
  exact key c.support subset_rfl
end GlobalTheory.CompareIterDegree
