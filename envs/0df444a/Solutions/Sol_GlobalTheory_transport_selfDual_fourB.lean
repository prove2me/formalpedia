-- Prove2me | solution 1 for GlobalTheory.transport_selfDual_fourB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:37:48.61331+00:00
-- url     : https://prove2.me/submissions/eef77888-a48d-4ce5-90eb-cc1346fd2557

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TransportSelfDualHaarMeasureKernelAddEquiv
import Theorems.Thm_GlobalTheory_TransportSD_map_map_equiv_left
import Theorems.Thm_GlobalTheory_TransportSD_map_map_equiv_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory.TransportSD
namespace GlobalTheory
theorem _root_.solution : ∀ {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V'] (h : V' ≃+ V), Continuous h → Continuous h.symm → ∀ (μ : Measure V) (B : V → V → ℂ), (SelfDual μ B → SelfDual (Measure.map h.symm μ) (fun x y => B (h x) (h y))) ∧ ∀ (f : V' → ℂ) (y : V'), fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f y = fourB μ B (fun v => f (h.symm v)) (h y) := by
  intro V V' _ _ _ _ _ _ _ _ h hc hs μ B
  let he : V ≃ₜ V' := { toEquiv := h.symm.toEquiv, continuous_toFun := hs, continuous_invFun := hc }
  let e : V ≃ᵐ V' := he.toMeasurableEquiv
  have he_eq : (e : V → V') = h.symm := rfl
  have hμ : Measure.map h.symm μ = Measure.map e μ := by rw [he_eq]
  have four : ∀ (f : V' → ℂ) (y : V'), fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f y = fourB μ B (fun v => f (h.symm v)) (h y) := by
    intro f y
    unfold fourB
    rw [hμ, integral_map_equiv]
    congr 1
    funext v
    rw [he_eq]
    simp
  refine ⟨fun hsd => ⟨?_, ?_⟩, four⟩
  · obtain ⟨hH, -⟩ := hsd
    rw [hμ]
    have h1 : IsFiniteMeasureOnCompacts (Measure.map e μ) := by
      refine ⟨fun K hK => ?_⟩
      rw [MeasurableEquiv.map_apply]
      have : (e : V → V') ⁻¹' K = h '' K := by
        ext v; rw [he_eq]; simp [Set.mem_image]
        constructor
        · intro hv; exact ⟨h.symm v, hv, by simp⟩
        · rintro ⟨w, hw, rfl⟩; simpa using hw
      rw [this]
      exact (hK.image hc).measure_lt_top
    have h2 : (Measure.map e μ).IsAddLeftInvariant := by
      refine ⟨fun x' => ?_⟩
      rw [map_map_equiv_left]
      have hcomp : (fun y' => x' + y') ∘ (e : V → V') = (e : V → V') ∘ (fun v => h x' + v) := by
        funext v; rw [he_eq]; simp
      rw [hcomp, ← map_map_equiv_right, hH.toIsAddLeftInvariant.map_add_left_eq_self (h x')]
    have h3 : (Measure.map e μ).IsOpenPosMeasure := by
      refine ⟨fun U hU hne => ?_⟩
      rw [MeasurableEquiv.map_apply]
      have hU' : IsOpen ((e : V → V') ⁻¹' U) := hU.preimage (by rw [he_eq]; exact hs)
      have hne' : ((e : V → V') ⁻¹' U).Nonempty := by
        obtain ⟨u, hu⟩ := hne
        exact ⟨h u, by rw [he_eq]; simpa using hu⟩
      exact hU'.measure_ne_zero μ hne'
    exact { toIsFiniteMeasureOnCompacts := h1, toIsAddLeftInvariant := h2, toIsOpenPosMeasure := h3 }
  · intro f hf y
    have hf' : IsTest (fun v => f (h.symm v)) :=
      ⟨hf.1.comp_continuous hs, hf.2.comp_homeomorph he⟩
    rw [four]
    have : (fun v => fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f (h.symm v)) =
        fourB μ B (fun v => f (h.symm v)) := by
      funext v; rw [four]; simp
    rw [this, hsd.2 _ hf' (h y)]
    simp
end GlobalTheory
