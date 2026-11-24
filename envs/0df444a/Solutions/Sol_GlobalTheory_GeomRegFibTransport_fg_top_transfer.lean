-- Prove2me | solution 1 for GlobalTheory.GeomRegFibTransport.fg_top_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:33:04.873626+00:00
-- url     : https://prove2.me/submissions/3737dd1d-99d1-49d0-be3c-eab0d9505b69

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GeomRegFibAdicCompletionOfEssFiniteTypeInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.GeomRegFibTransport
open ReciprocityTheory.AnForm.R.FinalTheorems
namespace GlobalTheory.GeomRegFibTransport
theorem _root_.solution {F F' K : Type} [Field F] [Field F'] [Field K] [Algebra F K] [Algebra F' K]
    (φ : F ≃+* F') (hφ : ∀ x, algebraMap F K x = algebraMap F' K (φ x))
    (h : (⊤ : IntermediateField F' K).FG) : (⊤ : IntermediateField F K).FG := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, ?_⟩
  apply IntermediateField.toSubfield_injective
  have hr : Set.range (algebraMap F K) = Set.range (algebraMap F' K) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨φ x, (hφ x).symm⟩
    · rintro ⟨x, rfl⟩; exact ⟨φ.symm x, by rw [hφ, RingEquiv.apply_symm_apply]⟩
  have h2 := congrArg IntermediateField.toSubfield hS
  rw [IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield] at h2 ⊢
  rw [hr]
  exact h2
end GlobalTheory.GeomRegFibTransport
