-- Prove2me | solution 1 for GlobalTheory.AlgWtHW.isUPt_tauPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:12:06.861651+00:00
-- url     : https://prove2.me/submissions/f2374739-bbb8-49e7-8668-f7a13ec71bf2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConjugateNeSelf
import Theorems.Thm_GlobalTheory_AlgWtHW_conj_conj
import Theorems.Thm_GlobalTheory_AlgWtHW_conjugate_ne_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix
open GlobalTheory GlobalTheory.AlgWtHW
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
namespace GlobalTheory.AlgWtHW
theorem _root_.solution (τ : L →+* ℂ) (B : GL (Fin n) ℂ) : IsUPt (tauPt τ B) := by
  intro σ
  have hne := conjugate_ne_self τ
  by_cases h1 : σ = τ
  · subst h1
    simp [tauPt, hne, Matrix.transpose_transpose]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      simp only [tauPt, if_neg h1, conj_conj, if_true]
      rw [← Matrix.transpose_transpose (B.val), ← Matrix.transpose_mul, Matrix.transpose_transpose,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
    · have h3 : ComplexEmbedding.conjugate σ ≠ τ := fun e => h2 (by rw [← e, conj_conj])
      have h4 : ComplexEmbedding.conjugate σ ≠ ComplexEmbedding.conjugate τ := fun e => h1 (by
        simpa using congrArg ComplexEmbedding.conjugate e)
      simp [tauPt, h1, h2, h3, h4]
end GlobalTheory.AlgWtHW
