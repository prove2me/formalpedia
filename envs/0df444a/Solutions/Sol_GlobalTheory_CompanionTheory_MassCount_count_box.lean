-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MassCount.count_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:13:36.216062+00:00
-- url     : https://prove2.me/submissions/031a4ea4-8ec8-48bc-8922-99469aea7cd3

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GaloisBoundSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormThetaMul
import Theorems.Thm_UpperTheory_Reformulated_B_GaloisBoundSecond_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MassCount
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.MassCount
theorem _root_.solution [IsTotallyReal F] (N : ℕ) (hN : 0 < N) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (B : ℝ) (hB : 0 ≤ B) :
    {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ B}.Finite ∧
    (({x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ B}.ncard : ℕ) : ℝ) *
      (Ideal.absNorm I : ℝ) ≤ (4 * B * N) ^ Module.finrank ℚ F :=
  _root_.UpperTheory.Reformulated.B.GaloisBoundSecond.main N hN I hI B hB
end GlobalTheory.CompanionTheory.MassCount
