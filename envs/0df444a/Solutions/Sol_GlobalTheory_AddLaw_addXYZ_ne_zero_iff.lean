-- Prove2me | solution 1 for GlobalTheory.AddLaw.addXYZ_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:53:49.309568+00:00
-- url     : https://prove2.me/submissions/f23bd368-5a2a-48a0-8c06-89028619adf2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Theorems.Thm_GlobalTheory_AddLaw_ne_zero_of_nonsingular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Projective
open GlobalTheory GlobalTheory.AddLaw
variable {F : Type*} [Field F] {W : Projective F}
namespace GlobalTheory.AddLaw
theorem _root_.solution {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.addXYZ P Q ≠ 0 ↔ ¬P ≈ Q := by
  refine ⟨fun h ⟨u, e⟩ => h ?_, fun h => ?_⟩
  · have := addXYZ_smul (W' := W) Q Q u 1
    rw [one_smul, addXYZ_self] at this
    rw [← show (u : F) • Q = P from e, this]
    ext i
    fin_cases i <;> simp
  · rw [← add_of_not_equiv h]
    exact ne_zero_of_nonsingular <| nonsingular_add hP hQ
end GlobalTheory.AddLaw
