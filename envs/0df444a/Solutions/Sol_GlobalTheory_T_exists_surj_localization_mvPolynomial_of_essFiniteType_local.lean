-- Prove2me | solution 1 for GlobalTheory.T.exists_surj_localization_mvPolynomial_of_essFiniteType_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:21:23.231917+00:00
-- url     : https://prove2.me/submissions/b65067c3-dbcc-4272-b251-80447eddfedb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSurjLocalizationMvPolynomialOfEssFiniteTyp
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSurjLocalizationMvPolynomialOfEssFiniteTypStatement
import Theorems.Thm_GlobalTheory_exists_surj_localization_mvPolynomial_of_essFiniteType


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Λ R : Type) [CommRing Λ] [CommRing R] [IsLocalRing R] [Algebra Λ R] [Algebra.EssFiniteType Λ R], ∃ (n : ℕ) (P : Ideal (MvPolynomial (Fin n) Λ)) (_ : P.IsPrime) (φ : Localization.AtPrime P →ₐ[Λ] R), Function.Surjective φ := by
  first | exact @GlobalTheory.exists_surj_localization_mvPolynomial_of_essFiniteType | exact GlobalTheory.exists_surj_localization_mvPolynomial_of_essFiniteType | (intros; apply GlobalTheory.exists_surj_localization_mvPolynomial_of_essFiniteType <;> assumption)
end _root_.GlobalTheory.T
