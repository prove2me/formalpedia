-- Prove2me | solution 1 for GlobalTheory.LocalQuad.TraceIsometry.finiteDimensional_of_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:49:04.006279+00:00
-- url     : https://prove2.me/submissions/63d0d913-eb3c-4fd2-b1b8-2db423df9cc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.LocalQuad GlobalTheory.LocalQuad.TraceIsometry
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] {c : E →+* E}
namespace GlobalTheory.LocalQuad.TraceIsometry
theorem _root_.solution (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t) : FiniteDimensional F E := by
  classical
  obtain ⟨δ, hδ⟩ : ∃ δ : E, ∀ x : E, ∃ s t : F, x = s • (1 : E) + t • δ := by
    by_cases h : ∀ t, c t = t
    · refine ⟨0, fun x => ?_⟩
      obtain ⟨s, hs⟩ := (hF x).1 (h x)
      exact ⟨s, 0, by simp [Algebra.smul_def, hs]⟩
    · push Not at h
      obtain ⟨u, hu⟩ := h
      have hne : u - c u ≠ 0 := sub_ne_zero.2 hu.symm
      have hne' : c u - u ≠ 0 := sub_ne_zero.2 hu
      refine ⟨u - c u, fun x => ?_⟩
      obtain ⟨s, hs⟩ := (hF ((x + c x) / 2)).1 (by
        rw [map_div₀, map_add, hc, map_ofNat, add_comm])
      obtain ⟨t, ht⟩ := (hF ((x - c x) / (2 * (u - c u)))).1 (by
        rw [map_div₀, map_sub, hc, map_mul, map_ofNat, map_sub, hc]
        field_simp
        ring)
      refine ⟨s, t, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, hs, ht]
      field_simp
      ring
  refine Module.finite_def.2 ⟨{1, δ}, ?_⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨s, t, rfl⟩ := hδ x
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
end GlobalTheory.LocalQuad.TraceIsometry
