-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.errorCascade_le_mainFormalError
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T18:23:18.177989+00:00
-- url     : https://prove2.me/submissions/b9604498-8ec4-42e4-9c86-60c2024b985d

-- Generated proof for MIPStarRE.LDT.Test.errorCascade_le_mainFormalError.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_sigma_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_zeta1_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_zeta2_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_zeta3_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_zeta4_bound

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Test
end LIDT.MIPStarRE.LDT.Test

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean. -/
/-!
# Error cascade — core definitions

This module defines the central error quantities `mainFormalError`,
`mainFormalEnvelope`, the cascade variables `σ`, `ζ₁`, `ζ₂`, `ζ₃`, `ζ₄`,
and the `CascadeHypotheses` numeric regime used throughout the error-cascade
bookkeeping for Step 8 of `mainFormal`.

Note: this module contributes declarations to the comparator statement closure
of `mainFormal`, which must elaborate in the same environment as the
Mathlib-only `Challenge.lean`.  Keep the full `import Mathlib`; do not narrow
it.  See `docs/comparator.md`, "Environment alignment".

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Test







/-- `mainFormalError` factors as `100000 · k² · m⁴ · mainFormalEnvelope`. -/
theorem mainFormalError_eq_envelope (params : Parameters) (k : ℕ) (eps : Error) :
    mainFormalError params k eps =
      100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        mainFormalEnvelope params k eps := rfl

/-- The envelope is nonnegative whenever `ε ≥ 0`. -/
theorem mainFormalEnvelope_nonneg (params : Parameters) (k : ℕ) (eps : Error)
    (heps : 0 ≤ eps) :
    0 ≤ mainFormalEnvelope params k eps := by
  unfold mainFormalEnvelope
  refine add_nonneg (add_nonneg (Real.rpow_nonneg heps _) ?_) (Real.exp_nonneg _)
  exact Real.rpow_nonneg (by positivity) _

















namespace CascadeHypotheses

variable {params : Parameters} {k : ℕ} {eps : Error}
variable (h : CascadeHypotheses params k eps)

include h





/-- The envelope is nonneg. -/
theorem envelope_nonneg : 0 ≤ mainFormalEnvelope params k eps :=
  mainFormalEnvelope_nonneg params k eps h.hepsNN

















end CascadeHypotheses

end Test

end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Error cascade — final assembly

This module contains the final tuple-valued consolidator for the error cascade
in Step 8 of the main inductive step.

## References

* `references/ldt-paper/inductive_step.tex`, lines 230--234.
-/

@[expose] public section

open scoped BigOperators

open LIDT.MIPStarRE.LDT

open LIDT.MIPStarRE.LDT.Test

theorem solution {params : _root_.LIDT.MIPStarRE.LDT.Parameters} {k : ℕ} {eps : _root_.LIDT.MIPStarRE.LDT.Error}
    (h : _root_.LIDT.MIPStarRE.LDT.Test.CascadeHypotheses params k eps) {ν σ ζ₁ ζ₂ ζ₃ : _root_.LIDT.MIPStarRE.LDT.Error}
    (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
        Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))))
    (hσEq : σ = _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν)
    (hζ₁Eq : ζ₁ = _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1 params eps σ)
    (hζ₂Eq : ζ₂ = _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta2 ζ₁)
    (hζ₃Eq : ζ₃ = _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta3 ζ₁ ζ₂) :
    σ ≤ _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError params k eps ∧
    ζ₁ ≤ _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError params k eps ∧
    ζ₂ ≤ _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError params k eps ∧
    ζ₃ ≤ 2 * _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError params k eps ∧
    _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta4 σ ζ₁ ζ₃ ≤ _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError params k eps := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hσEq, _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError_eq_envelope]
    have hENN := h.envelope_nonneg
    have hk2m4NN : 0 ≤ ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) := by
      positivity
    nlinarith [_root_.LIDT.MIPStarRE.LDT.Test.sigma_bound h hν, hENN, hk2m4NN]
  · rw [hζ₁Eq]
    exact _root_.LIDT.MIPStarRE.LDT.Test.zeta1_bound h hν hσEq
  · rw [hζ₂Eq]
    exact _root_.LIDT.MIPStarRE.LDT.Test.zeta2_bound h hνNN hν hσEq hζ₁Eq
  · rw [hζ₃Eq]
    exact _root_.LIDT.MIPStarRE.LDT.Test.zeta3_bound h hνNN hν hσEq hζ₁Eq hζ₂Eq
  · exact _root_.LIDT.MIPStarRE.LDT.Test.zeta4_bound h hνNN hν hσEq hζ₁Eq hζ₂Eq hζ₃Eq
