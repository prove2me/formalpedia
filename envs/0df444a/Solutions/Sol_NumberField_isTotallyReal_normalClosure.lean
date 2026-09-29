-- Prove2me | solution 1 for NumberField.isTotallyReal_normalClosure
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-09T23:51:24.767219+00:00
-- url     : https://prove2.me/submissions/d0844bf2-51ce-4344-a886-0a9fcd9ce2ad

import Mathlib

open NumberField IntermediateField

/-- Each embedding image of a totally real field is totally real. -/
private theorem isTotallyReal_fieldRange_aux (F : Type*) [Field F] [NumberField F]
    [IsTotallyReal F] (L : Type*) [Field L] [Algebra ℚ L] (f : F →ₐ[ℚ] L) :
    IsTotallyReal f.fieldRange :=
  IsTotallyReal.ofRingEquiv (AlgEquiv.ofInjectiveField f).toRingEquiv

theorem solution (F : Type*) [Field F] [NumberField F] [IsTotallyReal F] :
    IsTotallyReal (normalClosure ℚ F (AlgebraicClosure F)) := by
  set L := AlgebraicClosure F with hLdef
  haveI : Algebra.IsAlgebraic ℚ F := Algebra.IsAlgebraic.of_finite ℚ F
  haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.trans (R := ℚ) (S := F) (A := L)
  -- `ℚ` lands inside the maximal real subfield, so the latter is an intermediate field
  have hQ : ∀ q : ℚ, algebraMap ℚ L q ∈ maximalRealSubfield L := by
    intro q φ
    have h : φ (algebraMap ℚ L q) = (q : ℂ) := by
      have := map_ratCast (φ.comp (algebraMap ℚ L)) q
      simpa using this
    rw [h]
    simp
  set M : IntermediateField ℚ L := (maximalRealSubfield L).toIntermediateField hQ with hM
  -- the normal closure is the compositum of the embedding images, each totally real
  have hsub : normalClosure ℚ F L ≤ M := by
    rw [normalClosure_def]
    refine iSup_le fun f => ?_
    intro x hx
    haveI : IsTotallyReal (f.fieldRange : IntermediateField ℚ L) :=
      isTotallyReal_fieldRange_aux F L f
    haveI : IsTotallyReal (f.fieldRange : IntermediateField ℚ L).toSubfield :=
      IsTotallyReal.ofRingEquiv (RingEquiv.refl _)
    exact IsTotallyReal.le_maximalRealSubfield
      ((f.fieldRange : IntermediateField ℚ L).toSubfield) hx
  have hle : (normalClosure ℚ F L).toSubfield ≤ maximalRealSubfield L := hsub
  haveI : IsTotallyReal ((normalClosure ℚ F L).toSubfield) :=
    isTotallyReal_iff_le_maximalRealSubfield.mpr hle
  exact IsTotallyReal.ofRingEquiv (RingEquiv.refl _)
