-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.exists_algEquiv_apply_eq_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:48:23.965169+00:00
-- url     : https://prove2.me/submissions/4671a778-d06b-4ac3-b355-7e440674bc8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Theorems.Thm_GlobalTheory_GaloisDescent_exists_ringEquiv_of_isTranscendenceBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Cardinal
open GlobalTheory GlobalTheory.GaloisDescent
namespace GlobalTheory.GaloisDescent
theorem _root_.solution {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] {x : L} (hx : Transcendental K x) : ∃ σ : L ≃ₐ[K] L, σ x = x + 1 := by
  have h1 : AlgebraicIndepOn K id ({x} : Set L) :=
    algebraicIndependent_unique_type_iff.2 hx
  obtain ⟨s, hxs, hs⟩ := exists_isTranscendenceBasis_superset h1
  let e : MvPolynomial s K ≃ₐ[K] MvPolynomial s K :=
    AlgEquiv.ofAlgHom (aeval fun i => X i + 1) (aeval fun i => X i - 1)
      (by ext i : 1; simp) (by ext i : 1; simp)
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_of_isTranscendenceBasis hs hs e.toRingEquiv
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun k => ?_, ?_⟩
  · simpa [e] using hσ (C k)
  · simpa [e] using hσ (X ⟨x, hxs rfl⟩)
end GlobalTheory.GaloisDescent
