-- Prove2me | solution 1 for GlobalTheory.T.etaleChart_localization_finiteType_formallyUnramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:06:54.857843+00:00
-- url     : https://prove2.me/submissions/baf68ee9-b767-4f90-a0e7-e850f468e224

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleChartLocalizationFiniteTypeFormallyUnramifi
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleChartLocalizationFiniteTypeFormallyUnramifiStatement
import Theorems.Thm_GlobalTheory_DenseSec_locQuot_finiteType_formallyUnramified


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (Ω : Type) [Field Ω] [Algebra R Ω] (I : Ideal (TensorProduct R Ω A)),
  letI : Algebra (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) :=
    (MvPolynomial.aeval (fun i => algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (Ideal.Quotient.mk I (1 ⊗ₜ[R] t i)))).toRingHom.toAlgebra
  Algebra.FiniteType (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) ∧
    Algebra.FormallyUnramified (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) := by
  first | exact @GlobalTheory.DenseSec.locQuot_finiteType_formallyUnramified | exact GlobalTheory.DenseSec.locQuot_finiteType_formallyUnramified | (intros; apply GlobalTheory.DenseSec.locQuot_finiteType_formallyUnramified <;> assumption)
end _root_.GlobalTheory.T
