-- Prove2me | solution 1 for GlobalTheory.T.exists_imaginary_generator_cm_type
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:28:44.047982+00:00
-- url     : https://prove2.me/submissions/74e9ff99-2b75-4832-8bf2-3d06368f3e22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsImaginaryGeneratorCmType
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsImaginaryGeneratorCmTypeStatement
import Theorems.Thm_GlobalTheory_SignGen_exists_signed_generator


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : Submodule (OF E) E), IsUnit M →
    (∀ ξ ∈ M, IsCMField.complexConj E ξ = -ξ) → ∀ (I : Type) (φ : I → E →+* ℂ), IsCMType φ → ∀ (e₀ : ℤˣ) (l : ℕ), l.Prime →
    ∃ ξ ∈ M, (∀ i, 0 < ((e₀ : ℤ) : ℝ) * (φ i ξ).im) ∧
      ∀ η ∈ M, ∃ n : ℕ, n.Coprime l ∧ ∃ a : OF E, (n : E) * η = algebraMap (OF E) E a * ξ := by
  first | exact @GlobalTheory.SignGen.exists_signed_generator | exact GlobalTheory.SignGen.exists_signed_generator | (intros; apply GlobalTheory.SignGen.exists_signed_generator <;> assumption)
end _root_.GlobalTheory.T
