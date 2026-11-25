-- Prove2me | solution 1 for GlobalTheory.T.exists_finite_algebra_splitting_normForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:19:05.072902+00:00
-- url     : https://prove2.me/submissions/cd9f54d0-c56e-4446-a524-9f34c4848395

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteAlgebraSplittingNormForm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteAlgebraSplittingNormFormStatement
import Theorems.Thm_GlobalTheory_NormSheaf_exists_finite_split_normForm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A B K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [CharZero K] [Algebra A K] [Algebra B L] [Algebra K L] [FiniteDimensional K L]
    [IsFractionRing A K] [IsFractionRing B L] (φ : A →+* B), φ.Finite →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp φ →
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra A R), Function.Injective (algebraMap A R) ∧ Module.Finite A R ∧
      ∃ σ : Fin (Module.finrank K L) → (B →+* R), (∀ j, (σ j).comp φ = algebraMap A R) ∧
        ∀ (m : ℕ) (g : Fin m → B), ∃ P : MvPolynomial (Fin m) A,
          P.map (algebraMap A K) = GlobalTheory.NormSheaf.normForm K L (fun i => algebraMap B L (g i)) ∧
          P.map (algebraMap A R) = ∏ j, ∑ i, C (σ j (g i)) * X i := by
  first | exact @GlobalTheory.NormSheaf.exists_finite_split_normForm | exact GlobalTheory.NormSheaf.exists_finite_split_normForm | (intros; apply GlobalTheory.NormSheaf.exists_finite_split_normForm <;> assumption)
end _root_.GlobalTheory.T
