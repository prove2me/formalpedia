-- Prove2me | solution 1 for GlobalTheory.T.whittakerFunctional_weyl_vanish_of_weylUnipotent_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:49:51.580881+00:00
-- url     : https://prove2.me/submissions/650b9b3c-f2ec-4196-aa8a-dd2113a9ffb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerFunctionalWeylVanishOfWeylUnipotentZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerFunctionalWeylVanishOfWeylUnipotentZeroStatement
import Theorems.Thm_GlobalTheory_JR_lam_flip_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ, A.InI Ψ → (∀ z, Ψ (wS A.K * nS z) = 0) → ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  first | exact @GlobalTheory.JR.lam_flip_eq_zero | exact GlobalTheory.JR.lam_flip_eq_zero | (intros; apply GlobalTheory.JR.lam_flip_eq_zero <;> assumption)
end _root_.GlobalTheory.T
