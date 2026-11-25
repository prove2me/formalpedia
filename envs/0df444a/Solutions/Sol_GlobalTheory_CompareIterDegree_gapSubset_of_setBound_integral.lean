-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.gapSubset_of_setBound_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:36:56.815577+00:00
-- url     : https://prove2.me/submissions/f683157e-ea68-4e63-bb06-81b59cbe1296

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral
import Theorems.Thm_GlobalTheory_CompareIterDegree_eSet_empty
import Theorems.Thm_GlobalTheory_CompareIterDegree_gapTwo_iff
import Theorems.Thm_GlobalTheory_CompareIterDegree_weaken_consts
import Theorems.Thm_Formalism_QuantumDeterminants_formal_degree_pos_holds


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
theorem _root_.solution (h : DegSetBound) (n : ℕ) (μ : Fin n → ℝ) (I : Finset (Fin n))
    (hanti : StrictAnti μ) (hint : ∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ)) :
    ((∀ J ⊆ I, GapTwo (μ + eSet J)) →
      (1 / (4 * (n : ℝ) ^ 2)) ^ I.card ≤ fdegHC (μ + eSet I) / fdegHC μ ∧
        fdegHC (μ + eSet I) / fdegHC μ ≤ (Real.exp 1 * n) ^ I.card) ∧
    ((∀ J ⊆ I, GapTwo (μ - eSet J)) →
      (1 / (4 * (n : ℝ) ^ 2)) ^ I.card ≤ fdegHC (μ - eSet I) / fdegHC μ ∧
        fdegHC (μ - eSet I) / fdegHC μ ≤ (Real.exp 1 * n) ^ I.card) := by
  have w : (1 / (4 * (n : ℝ) ^ 2)) ^ I.card ≤ ((n : ℝ) ^ I.card)⁻¹ ∧
      (n : ℝ) ^ I.card ≤ (Real.exp 1 * n) ^ I.card ∧ 0 < (n : ℝ) ^ I.card := by
    rcases I.eq_empty_or_nonempty with rfl | ⟨s, _⟩
    · simp
    · obtain ⟨w1, w2⟩ := weaken_consts s.pos
      have : (0 : ℝ) < n := by exact_mod_cast s.pos
      rw [← inv_pow, ← one_div (n : ℝ)]
      exact ⟨pow_le_pow_left₀ (by positivity) w1 _, pow_le_pow_left₀ (by positivity) w2 _, by positivity⟩
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · have h0 := hg ∅ (empty_subset _)
    rw [eSet_empty, add_zero] at h0
    obtain ⟨a, b⟩ := h n μ I hanti hint ((gapTwo_iff hanti).2 h0)
    exact ⟨w.1.trans a, b.trans w.2.1⟩
  · have h0 := hg ∅ (empty_subset _)
    rw [eSet_empty, sub_zero] at h0
    have hI := hg I subset_rfl
    have hanti' : StrictAnti (μ - eSet I) := fun a b hab => by
      have := (gapTwo_iff hanti).2 h0 a b hab
      simp only [Pi.sub_apply, eSet]
      split_ifs <;> linarith
    obtain ⟨a, b⟩ := h n (μ - eSet I) I hanti' (fun a b => by
      obtain ⟨m, hm⟩ := hint a b
      refine ⟨m - (if a ∈ I then 1 else 0) + (if b ∈ I then 1 else 0), ?_⟩
      simp only [Pi.sub_apply, eSet]
      push_cast
      linarith) ((gapTwo_iff hanti').2 hI)
    have e : (fun a => (μ - eSet I) a + if a ∈ I then 1 else 0) = μ := by
      funext a; simp [eSet]
    rw [e] at a b
    have p : 0 < fdegHC μ / fdegHC (μ - eSet I) :=
      div_pos (formal_degree_pos_holds n _ hanti.injective) (formal_degree_pos_holds n _ hanti'.injective)
    rw [← inv_div (fdegHC μ)]
    exact ⟨w.1.trans (inv_anti₀ p b), le_trans (inv_le_of_inv_le₀ w.2.2 a) w.2.1⟩
end GlobalTheory.CompareIterDegree
