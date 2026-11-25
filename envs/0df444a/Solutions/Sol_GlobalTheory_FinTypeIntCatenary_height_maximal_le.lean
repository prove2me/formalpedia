-- Prove2me | solution 1 for GlobalTheory.FinTypeIntCatenary.height_maximal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:40:47.251596+00:00
-- url     : https://prove2.me/submissions/056ad3d6-7f8b-4bee-8228-30d2fe747cc0

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeightMaximalLePrimeAddDim
import Theorems.Thm_GlobalTheory_FinTypeIntCatenary_height_le_of_equidim
import Theorems.Thm_GlobalTheory_FinTypeIntCatenary_isCM_and_height_of_isMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinTypeIntCatenary
open ReciprocityTheory.CA
namespace GlobalTheory.FinTypeIntCatenary
theorem _root_.solution (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A]
    (P M : Ideal A) [P.IsPrime] [M.IsMaximal] :
    (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) := by
  obtain ⟨N, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType ℤ A›
  haveI : (RingHom.ker (f : MvPolynomial (Fin N) ℤ →+* A)).IsPrime := RingHom.ker_isPrime _
  let e : (MvPolynomial (Fin N) ℤ ⧸ RingHom.ker (f : MvPolynomial (Fin N) ℤ →+* A)) ≃+* A :=
    RingHom.quotientKerEquivOfSurjective (f := (f : MvPolynomial (Fin N) ℤ →+* A)) hf
  haveI : (P.comap e).IsPrime := Ideal.comap_isPrime _ _
  haveI : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
  have h := height_le_of_equidim (N + 1) (isCM_and_height_of_isMaximal N) _ (P.comap e) (M.comap e)
  rw [RingEquiv.height_comap, RingEquiv.height_comap] at h
  have hdim : ringKrullDim ((MvPolynomial (Fin N) ℤ ⧸ RingHom.ker (f : MvPolynomial (Fin N) ℤ →+* A)) ⧸
      P.comap e) = ringKrullDim (A ⧸ P) :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e
      (Ideal.map_comap_of_surjective _ e.surjective P).symm)
  rwa [hdim] at h
end GlobalTheory.FinTypeIntCatenary
