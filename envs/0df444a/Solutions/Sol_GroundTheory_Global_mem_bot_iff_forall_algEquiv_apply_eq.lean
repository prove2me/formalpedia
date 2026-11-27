-- Prove2me | solution 1 for GroundTheory.Global.mem_bot_iff_forall_algEquiv_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:48:34.834601+00:00
-- url     : https://prove2.me/submissions/01b93cbe-f8bf-43d0-ad14-e23807e5fa75

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ExistsRingEquivExtendOfIsTranscendenceBasis
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AutCFixed
import Theorems.Thm_GroundTheory_Global_exists_algEquiv_apply_eq_of_transcendental
import Theorems.Thm_GroundTheory_Global_exists_algEquiv_apply_eq_of_minpoly_eq

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
open Polynomial IntermediateField
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] {F : Type*} [Field F] [Algebra F Ω]
namespace GroundTheory.Global
theorem _root_.solution [PerfectField F] {x : Ω} :
    x ∈ (⊥ : IntermediateField F Ω) ↔ ∀ σ : Ω ≃ₐ[F] Ω, σ x = x := by
  refine ⟨fun hx σ => ?_, fun h => ?_⟩
  · obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.mp hx
    exact σ.commutes a
  by_contra hx
  by_cases halg : IsAlgebraic F x
  · have hsep : IsSeparable F x :=
      PerfectField.separable_of_irreducible (minpoly.irreducible halg.isIntegral)
    have hx' : x ∉ (⊥ : Subalgebra F Ω) := by
      rwa [Algebra.mem_bot, ← IntermediateField.mem_bot]
    obtain ⟨y, hne, hy⟩ :=
      (notMem_iff_exists_ne_and_isConjRoot hsep (IsAlgClosed.splits _)).mp hx'
    obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq_of_minpoly_eq halg hy
    exact hne (hσ ▸ h σ).symm
  · have htr : Transcendental F x := halg
    have htr' : Transcendental F (x + 1) := fun h' =>
      htr (by simpa using (h'.isIntegral.sub isIntegral_one).isAlgebraic)
    obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq_of_transcendental htr htr'
    have := hσ.symm.trans (h σ)
    simp at this
end GroundTheory.Global
