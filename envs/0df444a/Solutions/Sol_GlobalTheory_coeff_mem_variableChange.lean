-- Prove2me | solution 1 for GlobalTheory.coeff_mem_variableChange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:49.661028+00:00
-- url     : https://prove2.me/submissions/2ecdb45f-0203-46c1-9f18-20ee962f1b05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve Polynomial
variable {K : Type*} [Field K]
namespace GlobalTheory
theorem _root_.solution (S : Subring K) {W : WeierstrassCurve K} {r s t : K}
    (h₁ : W.a₁ ∈ S) (h₂ : W.a₂ ∈ S) (h₃ : W.a₃ ∈ S) (h₄ : W.a₄ ∈ S) (h₆ : W.a₆ ∈ S)
    (hr : r ∈ S) (hs : s ∈ S) (ht : t ∈ S) {W' : WeierstrassCurve K}
    (e : (⟨1, r, s, t⟩ : VariableChange K) • W = W') :
    W'.a₁ ∈ S ∧ W'.a₂ ∈ S ∧ W'.a₃ ∈ S ∧ W'.a₄ ∈ S ∧ W'.a₆ ∈ S := by
  subst e
  simp only [variableChange_def, inv_one, Units.val_one, one_pow, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> aesop
end GlobalTheory
