-- Prove2me | solution 1 for GroundTheory.Global.exists_ringEquiv_extend_of_trdeg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:49.604729+00:00
-- url     : https://prove2.me/submissions/f2770e7f-dfcf-4b4b-b020-daecc495ae9f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ExistsRingEquivExtendOfIsTranscendenceBasis
import Theorems.Thm_GroundTheory_Global_exists_ringEquiv_extend_of_isTranscendenceBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Cardinal Polynomial IntermediateField
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
namespace GroundTheory.Global
theorem _root_.solution
    {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra F₁ Ω] [Algebra F₂ Ω]
    (e : F₁ ≃+* F₂) (h : Algebra.trdeg F₁ Ω = Algebra.trdeg F₂ Ω) :
    ∃ σ : Ω ≃+* Ω, ∀ a : F₁, σ (algebraMap F₁ Ω a) = algebraMap F₂ Ω (e a) := by
  obtain ⟨s₁, hs₁⟩ := exists_isTranscendenceBasis F₁ Ω
  obtain ⟨s₂, hs₂⟩ := exists_isTranscendenceBasis F₂ Ω
  obtain ⟨φ⟩ := Cardinal.eq.1 (hs₁.cardinalMk_eq_trdeg.trans (h.trans hs₂.cardinalMk_eq_trdeg.symm))
  obtain ⟨σ, hσ, -⟩ := exists_ringEquiv_extend_of_isTranscendenceBasis e hs₁ hs₂ φ
  exact ⟨σ, hσ⟩
end GroundTheory.Global
