-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_val_sub_mul_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:43:52.036293+00:00
-- url     : https://prove2.me/submissions/e4bc2057-e193-422b-b6cf-62a91204308e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTwoPlacesOverOfIsSquareLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution {F L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ]
    [Valued L Γ] (φ : F → L) (hφ : DenseRange φ) (r c : L) :
    ∃ ρ : F, Valued.v ((r - φ ρ) * c) < (1 : Γ) := by
  have hopen : IsOpen {x : L | Valued.v x < (1 : Γ)} := by
    simpa using Valued.isOpen_ball L (1 : (MonoidWithZeroHom.ofClass
      (Valued.v : Valuation L Γ)).ValueGroup₀)
  have hcont : Continuous fun x : L => (r - x) * c := by fun_prop
  exact hφ.exists_mem_open (hopen.preimage hcont) ⟨r, by simp⟩
end GlobalTheory.QNorm
