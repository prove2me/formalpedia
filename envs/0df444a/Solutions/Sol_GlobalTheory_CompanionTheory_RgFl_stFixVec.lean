-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgFl.stFixVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:26:42.11286+00:00
-- url     : https://prove2.me/submissions/7f5c6415-8b19-4dd8-bba1-77999108d3b7

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FixedVectorStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_exists_least_norm_unique
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.Fl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl
namespace GlobalTheory.CompanionTheory.RgFl
theorem _root_.solution : StFixVec := by
  intro G H _ _ _ _ _ _ _ σ hiso hcont
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  obtain ⟨v, hv⟩ : ∃ v : H, ‖v‖ = 1 :=
    ⟨((‖x‖ : ℂ)⁻¹) • x, by
      have : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
      simp [norm_smul, this]⟩
  have hopen : IsOpen {g : G | ‖σ g v - v‖ < 1 / 2} :=
    isOpen_lt (((hcont v).sub continuous_const).norm) continuous_const
  have hone : (1 : G) ∈ {g : G | ‖σ g v - v‖ < 1 / 2} := by simp
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean _ (hopen.mem_nhds hone)
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  set A : Set H := Set.range (fun k : V => σ (k : G) v) with hA
  set C : Set H := closure (convexHull ℝ A) with hC
  have hvA : v ∈ A := ⟨1, by simp⟩
  have hCne : C.Nonempty := ⟨v, subset_closure (subset_convexHull ℝ A hvA)⟩
  have hCconv : Convex ℝ C := (convex_convexHull ℝ A).closure
  have hCball : C ⊆ Metric.closedBall v (1 / 2) := by
    refine closure_minimal (convexHull_min ?_ (convex_closedBall _ _)) Metric.isClosed_closedBall
    rintro _ ⟨k, rfl⟩
    have := hV k.2
    simp only [Set.mem_setOf_eq] at this
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact this.le
  have hstable : ∀ k : V, ∀ y ∈ C, σ (k : G) y ∈ C := by
    intro k y hy
    have hmaps : Set.MapsTo (σ (k : G)) (convexHull ℝ A) (convexHull ℝ A) := by
      have hconvpre : Convex ℝ ((σ (k : G)).toLinearMap.restrictScalars ℝ ⁻¹' convexHull ℝ A) :=
        (convex_convexHull ℝ A).linear_preimage _
      have hsub : A ⊆ (σ (k : G)).toLinearMap.restrictScalars ℝ ⁻¹' convexHull ℝ A := by
        rintro _ ⟨l, rfl⟩
        refine subset_convexHull ℝ A ⟨k * l, ?_⟩
        simp
      exact fun z hz => convexHull_min hsub hconvpre hz
    exact map_mem_closure (σ (k : G)).continuous hy hmaps
  obtain ⟨u, huC, hu⟩ := exists_least_norm_unique hCne isClosed_closure hCconv
  refine ⟨V.toSubgroup, u, V.isOpen, ?_, ?_⟩
  · rintro rfl
    have := hCball huC
    rw [Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg, hv] at this
    norm_num at this
  · intro k hk
    exact (hu _ (hstable ⟨k, hk⟩ u huC)).2 (hiso k u).le
end GlobalTheory.CompanionTheory.RgFl
