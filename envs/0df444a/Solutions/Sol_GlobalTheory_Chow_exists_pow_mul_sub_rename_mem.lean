-- Prove2me | solution 1 for GlobalTheory.Chow.exists_pow_mul_sub_rename_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:20.688722+00:00
-- url     : https://prove2.me/submissions/05c1b6be-df52-44a0-8123-35328b2d9693

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
variable {σ β : Type*} [Fintype σ]
namespace GlobalTheory.Chow
theorem _root_.solution {R : Type*} [CommRing R] (u : σ → R) (j : σ)
    (h : MvPolynomial (β × σ) R) :
    ∃ (m : ℕ) (g : MvPolynomial {v : β × σ // v ∉ elimIndices Set.univ j} R),
      h * C (u j ^ m) - rename Subtype.val g ∈ Ideal.span (Set.range (linForm u : β → _)) := by
  classical
  induction h using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, by simp⟩
  | add f g hf hg =>
    obtain ⟨m, f', hf⟩ := hf
    obtain ⟨n, g', hg⟩ := hg
    refine ⟨m + n, f' * C (u j ^ n) + g' * C (u j ^ m), ?_⟩
    have := Ideal.add_mem _ (Ideal.mul_mem_right (C (u j ^ n)) _ hf)
      (Ideal.mul_mem_right (C (u j ^ m)) _ hg)
    convert this using 1
    simp only [map_add, map_mul, map_pow, rename_C]
    ring
  | mul_X f v hf =>
    obtain ⟨m, f', hf⟩ := hf
    by_cases hv : v ∈ elimIndices Set.univ j
    · obtain ⟨i, k⟩ := v
      obtain rfl : k = j := hv.2
      let r : MvPolynomial {v : β × σ // v ∉ elimIndices Set.univ k} R :=
        ∑ l : {l : σ // l ≠ k}, C (u l) * X ⟨(i, l.1), fun h => l.2 h.2⟩
      have hr : linForm u i = C (u k) * X (i, k) + rename Subtype.val r := by
        rw [linForm_eq u i k, Finset.sum_subtype (p := fun l => l ≠ k) (F := inferInstance) _
          (by simp)]
        simp [r]
      refine ⟨m + 1, -(f' * r), ?_⟩
      have := Ideal.add_mem _ (Ideal.mul_mem_right (C (u k) * X (i, k)) _ hf)
        (Ideal.mul_mem_left _ (rename Subtype.val f') (Ideal.subset_span ⟨i, rfl⟩))
      convert this using 1
      simp only [hr, map_neg, map_mul, map_pow, pow_succ]
      ring
    · refine ⟨m, f' * X ⟨v, hv⟩, ?_⟩
      have := Ideal.mul_mem_right (X v) _ hf
      convert this using 1
      simp only [map_mul, rename_X]
      ring
end GlobalTheory.Chow
