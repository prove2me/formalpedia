-- Prove2me | solution 1 for GlobalTheory.Published.chowFormExists_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:16:48.165725+00:00
-- url     : https://prove2.me/submissions/06c80d0b-39c1-4541-8246-0e6dd13c8dfa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallAevalLineVanishingIdealIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ProjPointIdealMemProjComponentsOfIsProjPureDim
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsMultiHomogeneousFixFirstBlock_b3ed944b577456bc
import Theorems.Thm_GlobalTheory_ChowHt_IsChowForm_isChowFormInt
import Theorems.Thm_GlobalTheory_Chow_IsBlockHomogeneous_unique
import Theorems.Thm_GlobalTheory_IsHilbertPoly_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.Published
open GlobalTheory.ChowHt
namespace GlobalTheory.Published
theorem _root_.solution : ChowFormExists ↔
    ∀ (k : Type) [Field k] [CharZero k] (N D : ℕ) (I : Ideal (MvPolynomial (Fin N) k)),
      I.IsHomogeneous (homogeneousSubmodule (Fin N) k) →
      (I.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) :
        MvPolynomial (Fin N) k →+* MvPolynomial (Fin N) (AlgebraicClosure k))).IsPrime →
      ringKrullDim (MvPolynomial (Fin N) k ⧸ I) = (D + 1 : ℕ) →
      ∃ f : MvPolynomial (Fin (D + 1) × Fin N) k, IsChowForm I D (hilbertDegree I) f := by
  refine ⟨fun h k _ _ N D I h1 h2 h3 => (h k N D I h1 h2 h3).imp fun _ => And.left,
    fun h k _ _ N D I h1 h2 h3 => ?_⟩
  obtain ⟨f, hf⟩ := h k N D I h1 h2 h3
  exact ⟨f, hf, fun g hg => (hf.isChowFormInt.unique hg.isChowFormInt).2⟩
end GlobalTheory.Published
