-- Prove2me | solution 1 for MutualCorrelatedAgreement_map_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:41:45.045234+00:00
-- url     : https://prove2.me/submissions/ffac72d1-ed6b-4c2e-b3d9-f61482367017

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
omit [DecidableEq F]
theorem _root_.solution [Fintype F] [DecidableEq F]
    [MeasurableSpace F] [DiscreteMeasurableSpace F]
    {L L' : Type*} [Fintype L] [Fintype L']
    (Gen : ProximityGenerator F)
    (C : Submodule F (L → F))
    (bound : ℝ) (errorstar : ℕ → ℝ → ℝ)
    (e : L' ≃ L)
    (h_mca : MutualCorrelatedAgreement Gen C bound errorstar) :
    MutualCorrelatedAgreement Gen (C.map (LinearEquiv.funCongrLeft F F e).toLinearMap) bound errorstar := by
  intro m f delta hδ_nonneg hδ_lt
  convert h_mca m (fun i ↦ f i ∘ e.symm) delta hδ_nonneg hδ_lt using 1
  congr with r
  simp only [BadEvent, ge_iff_le, Submodule.mem_map, LinearEquiv.coe_toLinearMap,
    LinearEquiv.funCongrLeft_apply, exists_exists_and_eq_and, LinearMap.funLeft_apply, ne_eq,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Function.comp_apply]
  classical
  constructor <;> rintro ⟨S, hS₁, hS₂, hS₃⟩
  · refine ⟨S.image e, ?_, ?_, ?_⟩
    · simpa [Finset.card_image_of_injective _ e.injective, Fintype.card_congr e] using hS₁
    · grind
    · obtain ⟨i, hi⟩ := hS₃
      refine ⟨i, fun u hu ↦ ?_⟩
      obtain ⟨x, hx₁, hx₂⟩ := hi u hu
      exact ⟨e x, Finset.mem_image_of_mem _ hx₁, by grind⟩
  · refine ⟨S.image e.symm, ?_, ?_, ?_⟩
    · simpa [Finset.card_image_of_injective _ e.symm.injective, Fintype.card_congr e.symm] using hS₁
    · simp_all
    · simp_all
