-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Preliminaries.fourier_fact_vector
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:19:23.284513+00:00
-- url     : https://prove2.me/submissions/f4d9a691-bf26-4e8e-b33a-fd98586b8465

-- Generated proof for MIPStarRE.LDT.Preliminaries.fourier_fact_vector.
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





section Vector

variable {m : ℕ}

-- We define `ffDotProduct` directly rather than reusing `Matrix.dotProduct` to avoid
-- pulling in the full `Mathlib.Data.Matrix.Basic` import. The definitions are identical.






omit [Fintype F] [DecidableEq F] in
private theorem ffVecChar_ne_zero [Finite F] {v : Fin m → F} (hv : v ≠ 0) :
    ffVecChar (p := p) (F := F) v ≠ 0 := by
  rw [AddChar.ne_zero_iff]
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    simpa [funext_iff] using hv
  obtain ⟨b, hb0⟩ :=
    ffTrace_nondegenerate (p := p) (F := F) (a := v i) hi
  have hb : ffTrace (p := p) (F := F) (b * v i) ≠ 0 := by
    simpa [mul_comm] using hb0
  refine ⟨Pi.single i b, ?_⟩
  have hdot : ffDotProduct (Pi.single i b) v = b * v i := by
    unfold ffDotProduct
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hi
      exact (hi (by simp)).elim
  rw [ffVecChar_apply, hdot, ffChar_apply]
  intro h
  exact hb ((AddChar.IsPrimitive.zmod_char_eq_one_iff p (ZMod.isPrimitive_stdAddChar p) _).mp h)



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












variable {m : ℕ}

-- We define `ffDotProduct` directly rather than reusing `Matrix.dotProduct` to avoid
-- pulling in the full `Mathlib.Data.Matrix.Basic` import. The definitions are identical.

theorem solution (v : Fin m → F) :
    𝔼 u : (Fin m → F), _root_.LIDT.MIPStarRE.LDT.Preliminaries.ffVecChar (p := p) (F := F) v u =
      if v = 0 then (1 : ℂ) else 0 := by
  calc
    𝔼 u : (Fin m → F), _root_.LIDT.MIPStarRE.LDT.Preliminaries.ffVecChar (p := p) (F := F) v u =
        if _root_.LIDT.MIPStarRE.LDT.Preliminaries.ffVecChar (p := p) (F := F) v = 0 then (1 : ℂ) else 0 :=
      AddChar.expect_eq_ite _
    _ = if v = 0 then (1 : ℂ) else 0 := by
      by_cases hv : v = 0
      · have hzero :
            _root_.LIDT.MIPStarRE.LDT.Preliminaries.ffVecChar (p := p) (F := F) v = 0 := by
          subst v
          ext u
          simp [_root_.LIDT.MIPStarRE.LDT.Preliminaries.ffVecChar, _root_.LIDT.MIPStarRE.LDT.Preliminaries.ffDotProduct]
        rw [if_pos hzero, if_pos hv]
      · have hvc : _root_.LIDT.MIPStarRE.LDT.Preliminaries.ffVecChar (p := p) (F := F) v ≠ 0 :=
          ffVecChar_ne_zero (p := p) (F := F) hv
        simp [hv, hvc]
