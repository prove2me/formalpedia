-- Prove2me | solution 1 for GlobalTheory.WeylRowAll.coeffMap_mem_weyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:45:50.839402+00:00
-- url     : https://prove2.me/submissions/a8541fbe-6ef1-43b9-87b2-5b3f53f6770f

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeylRowActionMemWeylLatticeSquare
import Theorems.Thm_GlobalTheory_WeylRowAll_coeff_coeffMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_applyWord_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_hw_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.WeylRowAll
namespace GlobalTheory.WeylRowAll
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (c : S →+ R)
    (hc : ∀ (s : S) (a : R), c (s * φ a) = c s * a) {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (F : MvPolynomial (Fin r × Fin n) S) (hF : F ∈ Formalism.GradedWeylDivisibility.weyl S r n hn ν) :
    coeffMap c F ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  have key : ∀ s : S, coeffMap c (s • F) ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
    unfold Formalism.GradedWeylDivisibility.weyl at hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      intro s
      have : coeffMap c (s • Formalism.GradedWeylDivisibility.applyWord S w (Formalism.GradedWeylDivisibility.hw S hn ν)) =
          c s • Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν) := by
        ext m
        rw [coeff_coeffMap, ← Formalism.GradedWeylDivisibility.lclosedeq_hw_map φ, Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map,
          coeff_smul, coeff_smul, coeff_map, smul_eq_mul, smul_eq_mul, hc]
      show coeffMap c (s • Formalism.GradedWeylDivisibility.applyWord S w (Formalism.GradedWeylDivisibility.hw S hn ν)) ∈ _
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩)
    | zero =>
      intro s
      have : coeffMap c (s • (0 : MvPolynomial (Fin r × Fin n) S)) = 0 := by
        ext m; simp [coeff_coeffMap]
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      intro s
      have : coeffMap c (s • (x + y)) = coeffMap c (s • x) + coeffMap c (s • y) := by
        ext m; simp [coeff_coeffMap, mul_add]
      rw [this]; exact Submodule.add_mem _ (hx s) (hy s)
    | smul a x _ hx =>
      intro s
      rw [smul_smul]; exact hx _
  simpa using key 1
end GlobalTheory.WeylRowAll
