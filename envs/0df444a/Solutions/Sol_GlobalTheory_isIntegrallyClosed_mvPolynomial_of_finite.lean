-- Prove2me | solution 1 for GlobalTheory.isIntegrallyClosed_mvPolynomial_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:37.675631+00:00
-- url     : https://prove2.me/submissions/fcd0893f-8761-415c-9e00-71f0af5cc60b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIntegrallyClosedMvPolynomialOfFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Frames
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (σ : Type) [Finite σ] (R : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] : IsIntegrallyClosed (MvPolynomial σ R) := by
  have h : ∀ n : ℕ, IsIntegrallyClosed (MvPolynomial (Fin n) R) := by
    intro n
    induction n with
    | zero => exact IsIntegrallyClosed.of_equiv (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm
    | succ n ih => exact IsIntegrallyClosed.of_equiv (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  have := h n
  exact IsIntegrallyClosed.of_equiv (MvPolynomial.renameEquiv R e).symm.toRingEquiv
end GlobalTheory
