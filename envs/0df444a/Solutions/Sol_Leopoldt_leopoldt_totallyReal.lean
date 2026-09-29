-- Prove2me | solution 1 for Leopoldt.leopoldt_totallyReal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-09T20:09:52.867586+00:00
-- url     : https://prove2.me/submissions/50254e15-85f6-4416-b6d5-56f6230ad458
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Leopoldt_leopoldt_totallyReal_galois
import Theorems.Thm_Leopoldt_defect_pos_of_defect_pos
import Definitions.Def_LeopoldtDefect

open NumberField IntermediateField


variable (F : Type*) [Field F] [NumberField F] [IsTotallyReal F]

/-- Each embedding image of a totally real field is totally real. -/
theorem isTotallyReal_fieldRange
    (L : Type*) [Field L] [Algebra ℚ L] (f : F →ₐ[ℚ] L) : IsTotallyReal f.fieldRange :=
  IsTotallyReal.ofRingEquiv (AlgEquiv.ofInjectiveField f).toRingEquiv

/-- The normal closure of a totally real number field is totally real. -/
theorem isTotallyReal_normalClosure :
    IsTotallyReal (normalClosure ℚ F (AlgebraicClosure F)) := by
  set L := AlgebraicClosure F with hLdef
  haveI : Algebra.IsAlgebraic ℚ F := Algebra.IsAlgebraic.of_finite ℚ F
  haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.trans (R := ℚ) (S := F) (A := L)
  have hQ : ∀ q : ℚ, algebraMap ℚ L q ∈ maximalRealSubfield L := by
    intro q φ
    have h : φ (algebraMap ℚ L q) = (q : ℂ) := by
      have := map_ratCast (φ.comp (algebraMap ℚ L)) q
      simpa using this
    rw [h]
    simp
  set M : IntermediateField ℚ L := (maximalRealSubfield L).toIntermediateField hQ with hM
  have hsub : normalClosure ℚ F L ≤ M := by
    rw [normalClosure_def]
    refine iSup_le fun f => ?_
    intro x hx
    haveI : IsTotallyReal (f.fieldRange : IntermediateField ℚ L) := isTotallyReal_fieldRange F L f
    haveI : IsTotallyReal (f.fieldRange : IntermediateField ℚ L).toSubfield :=
      IsTotallyReal.ofRingEquiv (RingEquiv.refl _)
    exact IsTotallyReal.le_maximalRealSubfield
      ((f.fieldRange : IntermediateField ℚ L).toSubfield) hx
  have hle : (normalClosure ℚ F L).toSubfield ≤ maximalRealSubfield L := hsub
  haveI : IsTotallyReal ((normalClosure ℚ F L).toSubfield) :=
    isTotallyReal_iff_le_maximalRealSubfield.mpr hle
  exact IsTotallyReal.ofRingEquiv (RingEquiv.refl _)

theorem solution (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (F : Type*) [Field F] [NumberField F] [IsTotallyReal F] :
    Leopoldt.LeopoldtConjecture p F := by
  set K := AlgebraicClosure F with hK
  set L := normalClosure ℚ F K with hLdef
  haveI : Algebra.IsAlgebraic ℚ F := Algebra.IsAlgebraic.of_finite ℚ F
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans (R := ℚ) (S := F) (A := K)
  haveI : IsAlgClosure ℚ K := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ K := IsAlgClosure.normal ℚ K
  haveI : IsTotallyReal L := isTotallyReal_normalClosure F
  haveI : FiniteDimensional ℚ L := normalClosure.is_finiteDimensional ℚ F K
  haveI : NumberField L := ⟨⟩
  haveI : Normal ℚ L := normalClosure.normal ℚ F K
  haveI : Algebra.IsSeparable ℚ L := Algebra.IsSeparable.of_integral ℚ L
  haveI : IsGalois ℚ L := ⟨⟩
  haveI : FiniteDimensional F L := by infer_instance
  have hL : Leopoldt.defect p L = 0 := Leopoldt.leopoldt_totallyReal_galois p hp L
  by_contra h
  have hFpos : 0 < Leopoldt.defect p F := Nat.pos_of_ne_zero h
  have := Leopoldt.defect_pos_of_defect_pos p F L hFpos
  omega
