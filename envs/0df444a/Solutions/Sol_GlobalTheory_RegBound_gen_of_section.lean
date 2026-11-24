-- Prove2me | solution 1 for GlobalTheory.RegBound.gen_of_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:14:06.617034+00:00
-- url     : https://prove2.me/submissions/746eff69-af55-4ff3-b93d-c3f468fffa19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
import Theorems.Thm_GlobalTheory_RegBound_comp_succ_mul
import Theorems.Thm_GlobalTheory_RegBound_comp_zero_mul
import Theorems.Thm_GlobalTheory_RegBound_mem_sup_span
import Theorems.Thm_GlobalTheory_RegBound_hom_genIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
namespace GlobalTheory.RegBound
theorem _root_.solution {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) {h : MvPolynomial σ K}
    (hh : h.IsHomogeneous 1) (hreg : ∀ F, h * F ∈ I → F ∈ I) {e : ℕ} {F : MvPolynomial σ K}
    (hF : F ∈ I) (hFe : F.IsHomogeneous (e + 1)) (hg : F ∈ genIn (I ⊔ Ideal.span {h}) e) :
    F ∈ genIn I e := by
  have h1 : genIn (I ⊔ Ideal.span {h}) e ≤ genIn I e ⊔ Ideal.span {h} := by
    refine Ideal.span_le.2 ?_
    rintro G ⟨hG, hGe⟩
    obtain ⟨A, hA, B, hAB⟩ := mem_sup_span.1 hG
    have : G = homogeneousComponent e A + homogeneousComponent e (h * B) := by
      rw [← map_add, ← hAB, homogeneousComponent_eq_self hGe]
    rw [this]
    refine Submodule.add_mem_sup
      (Ideal.subset_span ⟨hI A hA _, homogeneousComponent_isHomogeneous _ _⟩) ?_
    cases e with
    | zero => rw [comp_zero_mul hh]; exact Submodule.zero_mem _
    | succ e => rw [comp_succ_mul hh]; exact Ideal.mem_span_singleton.2 ⟨_, rfl⟩
  obtain ⟨A, hA, B, hAB⟩ := mem_sup_span.1 (h1 hg)
  have hAI : A ∈ I := (Ideal.span_le.2 fun G hG => hG.1 : genIn I e ≤ I) hA
  have hB : B ∈ I := hreg B (by simpa [hAB] using I.sub_mem hF hAI)
  have : F = homogeneousComponent (e + 1) A + h * homogeneousComponent e B := by
    rw [← comp_succ_mul hh, ← map_add, ← hAB, homogeneousComponent_eq_self hFe]
  rw [this]
  exact Ideal.add_mem _ (hom_genIn I e A hA _) (Ideal.mul_mem_left _ _
    (Ideal.subset_span ⟨hI B hB _, homogeneousComponent_isHomogeneous _ _⟩))
end GlobalTheory.RegBound
