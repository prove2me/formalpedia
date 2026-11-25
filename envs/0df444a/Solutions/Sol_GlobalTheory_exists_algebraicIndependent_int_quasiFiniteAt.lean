-- Prove2me | solution 1 for GlobalTheory.exists_algebraicIndependent_int_quasiFiniteAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:18.902785+00:00
-- url     : https://prove2.me/submissions/f92e6d47-a097-4604-a148-1938761794e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap
import Theorems.Thm_GlobalTheory_NoetherInt_quasiFiniteAt_iff
import Theorems.Thm_GlobalTheory_NoetherInt_exists_algebraicIndependent_of_quasiFiniteAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Type) [CommRing S] [IsDomain S] [CharZero S] [Algebra.FiniteType ℤ S] (𝔮 : Ideal S) [𝔮.IsPrime], ∃ (r : ℕ) (y : Fin r → S), AlgebraicIndependent ℤ y ∧ @Algebra.QuasiFiniteAt (MvPolynomial (Fin r) ℤ) S _ _ (MvPolynomial.aeval y : MvPolynomial (Fin r) ℤ →ₐ[ℤ] S).toRingHom.toAlgebra 𝔮 _ := by
  intro S _ _ _ hS 𝔮 _
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hS
  have hfe : (MvPolynomial.aeval (fun i => f (MvPolynomial.X i)) :
      MvPolynomial (Fin n) ℤ →ₐ[ℤ] S) = f := by
    apply MvPolynomial.algHom_ext
    intro i; simp
  refine NoetherInt.exists_algebraicIndependent_of_quasiFiniteAt 𝔮 n
    (fun i => f (MvPolynomial.X i)) ?_
  rw [NoetherInt.quasiFiniteAt_iff, hfe]
  refine RingHom.QuasiFinite.comp ?_ (RingHom.QuasiFinite.of_finite
    (RingHom.Finite.of_surjective _ hf))
  exact RingHom.quasiFinite_algebraMap.2 (.of_isLocalization 𝔮.primeCompl)
end GlobalTheory
