-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Preliminaries.fourier_fact_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:19:23.238194+00:00
-- url     : https://prove2.me/submissions/4b7d6bb3-a7e0-4a82-abbe-919bc2a30584

-- Generated proof for MIPStarRE.LDT.Preliminaries.fourier_fact_scalar.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_FiniteFields
import Mathlib
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Preliminaries/FiniteFields.lean. -/
/-!
# Finite fields and Fourier orthogonality

This file formalizes the finite-field trace and the two Fourier orthogonality facts
from `references/ldt-paper/preliminaries.tex` (lines 15–83).

## Main results

* `fourier_fact_scalar` (`prop:fourier-fact-scalar`):
  `𝔼_{x ∈ 𝔽_q} ω^{tr[x·a]} = 1 if a = 0, 0 otherwise`
* `fourier_fact_vector` (`prop:fourier-fact-vector`):
  Vector version over `𝔽_q^m`.

## References

* `references/ldt-paper/preliminaries.tex`, lines 15–83
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

section Trace

variable {p : ℕ} [Fact p.Prime]
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod p) F]





section Honest

variable (params : Parameters) (spec : PrimePowerFieldSpec params)





end Honest
end Trace

section Fourier

-- The Fourier section uses `[Fintype F]` (rather than `[Finite F]` as in the Trace section)
-- because `AddChar.expect_eq_ite` requires a `Fintype` instance. Downstream users with
-- only `[Finite F]` can obtain `Fintype` via `Fintype.ofFinite`.
variable {p : ℕ} [Fact p.Prime]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]





omit [Fintype F] [DecidableEq F] in
private theorem ffTrace_nondegenerate [Finite F] (a : F) (ha : a ≠ 0) :
    ∃ b : F, ffTrace (p := p) (F := F) (a * b) ≠ 0 := by
  have : CharP F p := (Algebra.charP_iff (ZMod p) F p).mp (ZMod.charP p)
  have hp : p = ringChar F := by
    simpa using (ringChar.eq F p).symm
  subst p
  simpa [ffTrace] using (FiniteField.trace_to_zmod_nondegenerate F (a := a) ha)

omit [Fintype F] [DecidableEq F] in
private theorem ffChar_ne_zero [Finite F] : ffChar (p := p) (F := F) ≠ 0 := by
  rw [AddChar.ne_zero_iff]
  obtain ⟨a, ha0⟩ :=
    ffTrace_nondegenerate (p := p) (F := F) (a := (1 : F)) one_ne_zero
  have ha : ffTrace (p := p) (F := F) a ≠ 0 := by
    simpa using ha0
  refine ⟨a, ?_⟩
  rw [ffChar_apply]
  intro h
  exact ha ((AddChar.IsPrimitive.zmod_char_eq_one_iff p (ZMod.isPrimitive_stdAddChar p) _).mp h)



section Vector

variable {m : ℕ}

-- We define `ffDotProduct` directly rather than reusing `Matrix.dotProduct` to avoid
-- pulling in the full `Mathlib.Data.Matrix.Basic` import. The definitions are identical.










end Vector
end Fourier

end MIPStarRE.LDT.Preliminaries

end

end LIDT

open LIDT
/-!
# Finite fields and Fourier orthogonality

This file formalizes the finite-field trace and the two Fourier orthogonality facts
from `references/ldt-paper/preliminaries.tex` (lines 15–83).

## Main results

* `fourier_fact_scalar` (`prop:fourier-fact-scalar`):
  `𝔼_{x ∈ 𝔽_q} ω^{tr[x·a]} = 1 if a = 0, 0 otherwise`
* `fourier_fact_vector` (`prop:fourier-fact-vector`):
  Vector version over `𝔽_q^m`.

## References

* `references/ldt-paper/preliminaries.tex`, lines 15–83
-/

@[expose] public section

open scoped BigOperators

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT



-- The Fourier section uses `[Fintype F]` (rather than `[Finite F]` as in the Trace section)
-- because `AddChar.expect_eq_ite` requires a `Fintype` instance. Downstream users with
-- only `[Finite F]` can obtain `Fintype` via `Fintype.ofFinite`.
variable {p : ℕ} [Fact p.Prime]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]

theorem solution (a : F) :
    𝔼 x : F, _root_.LIDT.MIPStarRE.LDT.Preliminaries.ffChar (p := p) (F := F) (x * a) =
      if a = 0 then (1 : ℂ) else 0 := by
  let ψ : AddChar F ℂ := (_root_.LIDT.MIPStarRE.LDT.Preliminaries.ffChar (p := p) (F := F)).mulShift a
  calc
    𝔼 x : F, _root_.LIDT.MIPStarRE.LDT.Preliminaries.ffChar (p := p) (F := F) (x * a) = 𝔼 x : F, ψ x := by
      simp [ψ, AddChar.mulShift_apply, mul_comm]
    _ = if ψ = 0 then (1 : ℂ) else 0 := AddChar.expect_eq_ite ψ
    _ = if a = 0 then (1 : ℂ) else 0 := by
      by_cases ha : a = 0
      · have hψ : ψ = 0 := by
          ext x
          simp [ψ, ha]
        simp [ha, hψ]
      · have hψ : ψ ≠ 0 := by
          have hprimitive : (_root_.LIDT.MIPStarRE.LDT.Preliminaries.ffChar (p := p) (F := F)).IsPrimitive := by
            exact AddChar.IsPrimitive.of_ne_one (by
              simpa [AddChar.one_eq_zero] using (ffChar_ne_zero (p := p) (F := F)))
          simpa [ψ, AddChar.one_eq_zero] using hprimitive ha
        simp [ha, hψ]
