-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.exists_polyPair_of_scalar_separated
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:47:23.112758+00:00
-- url     : https://prove2.me/submissions/390b1850-99c0-49a8-b09b-16e2ce801b51

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.exists_polyPair_of_scalar_separated.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Polynomial
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_ScalarPolynomial
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame

/- Source helpers from QPBT/Combining/ExtendedLineGame/ScalarPolynomial.lean. -/
/-!
# Scalar and base coefficients of the rounded polynomial outcomes

The singleton polynomial is transported through the canonical field equivalence
and Mathlib's equivalence between a polynomial in a sum of variables and an
iterated polynomial ring. Its individual-degree certificate controls both levels.
Splitting each base coefficient by either block gives the partial degrees used
in the fiber calculation. Independence of both wrong blocks identifies the
outcome with the existing bounded polynomial-pair combining map.

## References

`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1310-1326`,
the coefficient expansion preceding `eq:qld-g-prime-bound`.
The partial coefficient argument and separated image are at lines 1341--1368,
`eq:qld-g-2` and `eq:qld-g-non-separable`; blueprint `lem:qld-4-7`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement

noncomputable section

namespace ExtendedLineGame

private theorem coeff_coeff_sumRingEquiv {F A B : Type*} [CommSemiring F]
    (p : MvPolynomial (A ⊕ B) F) (a : A →₀ ℕ) (b : B →₀ ℕ) :
    ((MvPolynomial.sumRingEquiv F A B p).coeff a).coeff b =
      p.coeff (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (a, b)) := by
  simp [MvPolynomial.sumRingEquiv, MvPolynomial.coeff,
    AddMonoidAlgebra.curryRingEquiv, AddMonoidAlgebra.curryAddEquiv]











private theorem scalarPolynomial_renamed_exponents (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (g : _root_.MIPStarRE.QPBT.DirectPolyTuple P.extendedDirectLd) :
    ∀ e ∈ (MvPolynomial.rename (_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv P.m)
      (MvPolynomial.map (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1)).support,
      ∀ i, e i ≤ P.d := by
  intro e he i
  obtain ⟨v, hv, hvp⟩ := MvPolynomial.coeff_rename_ne_zero _ _ _
    (MvPolynomial.mem_support_iff.mp he)
  have hmem := MvPolynomial.support_map_subset _ _ (MvPolynomial.mem_support_iff.mpr hvp)
  have hdeg := _root_.LIDT.MIPStarRE.LDT.Preliminaries.degreeOf_le_of_mem_polyFunc (g (0 : Fin 1)).2
    ((_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv P.m).symm i)
  have hvbound := (MvPolynomial.le_degreeOf_of_mem_support _ hmem).trans hdeg
  change v ((_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv P.m).symm i) ≤ P.d at hvbound
  subst e
  simpa only [Finsupp.mapDomain_equiv_apply] using hvbound





private theorem blockCoefficientPolynomial_renamed_exponents (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (g : _root_.MIPStarRE.QPBT.DirectPolyTuple P.extendedDirectLd) (a : Fin 2 →₀ ℕ) (reverse : Bool) :
    ∀ e ∈ (MvPolynomial.rename ((_root_.MIPStarRE.QPBT.ExtendedLineGame.baseCoordinateEquiv P.m).trans
      (if reverse then Equiv.sumComm _ _ else Equiv.refl _))
        ((_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarPolynomial P g).coeff a)).support, ∀ i, e i ≤ P.d := by
  intro e he i
  let eqv := (_root_.MIPStarRE.QPBT.ExtendedLineGame.baseCoordinateEquiv P.m).trans
    (if reverse then Equiv.sumComm _ _ else Equiv.refl _)
  obtain ⟨v, hv, hvp⟩ := MvPolynomial.coeff_rename_ne_zero _ _ _
    (MvPolynomial.mem_support_iff.mp he)
  have hcoeff :
      (MvPolynomial.rename (_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv P.m)
        (MvPolynomial.map (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1)).coeff
        (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (a, v)) ≠ 0 := by
    simpa only [_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarPolynomial, coeff_coeff_sumRingEquiv] using hvp
  have hb := scalarPolynomial_renamed_exponents P g _
    (MvPolynomial.mem_support_iff.mpr hcoeff) (.inr (eqv.symm i))
  change v (eqv.symm i) ≤ P.d at hb
  subst e
  simpa only [Finsupp.mapDomain_equiv_apply] using hb





















private theorem sumRingEquiv_rename_inr {F A B : Type*} [CommSemiring F]
    (p : MvPolynomial B F) :
    MvPolynomial.sumRingEquiv F A B (MvPolynomial.rename Sum.inr p) =
      MvPolynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

private theorem blockCoefficientPolynomial_const {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (g : _root_.MIPStarRE.QPBT.DirectPolyTuple P.extendedDirectLd) (a : Fin 2 →₀ ℕ) (reverse : Bool)
    (h : ∃ r, _root_.MIPStarRE.QPBT.ExtendedLineGame.blockCoefficientPolynomial P g a reverse = MvPolynomial.C r) :
    ∃ r : _root_.MIPStarRE.QPBT.Poly P, (_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarPolynomial P g).coeff a = MvPolynomial.rename
      (fun i => ((_root_.MIPStarRE.QPBT.ExtendedLineGame.baseCoordinateEquiv P.m).trans
        (if reverse then Equiv.sumComm _ _ else Equiv.refl _)).symm (.inr i)) r.1 := by
  obtain ⟨r, hr⟩ := h
  have hmem : r ∈ _root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc P.m (_root_.MIPStarRE.QPBT.PauliScalar P) P.d := by
    apply _root_.MIPStarRE.QPBT.mem_polyFunc_of_degreeOf_le
    intro i
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro b hb
    have hcoeff :
        ((_root_.MIPStarRE.QPBT.ExtendedLineGame.blockCoefficientPolynomial P g a reverse).coeff 0).coeff b ≠ 0 := by
      simpa only [hr, MvPolynomial.coeff_C, ↓reduceIte] using MvPolynomial.mem_support_iff.mp hb
    have hsupport : Finsupp.sumFinsuppAddEquivProdFinsupp.symm (0, b) ∈
        (MvPolynomial.rename ((_root_.MIPStarRE.QPBT.ExtendedLineGame.baseCoordinateEquiv P.m).trans
          (if reverse then Equiv.sumComm _ _ else Equiv.refl _))
            ((_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarPolynomial P g).coeff a)).support := by
      simpa only [_root_.MIPStarRE.QPBT.ExtendedLineGame.blockCoefficientPolynomial, coeff_coeff_sumRingEquiv,
        MvPolynomial.mem_support_iff] using hcoeff
    simpa using blockCoefficientPolynomial_renamed_exponents P g a reverse _ hsupport (.inr i)
  refine ⟨⟨r, hmem⟩, ?_⟩
  let eqv := (_root_.MIPStarRE.QPBT.ExtendedLineGame.baseCoordinateEquiv P.m).trans
    (if reverse then Equiv.sumComm _ _ else Equiv.refl _)
  apply MvPolynomial.rename_injective eqv eqv.injective
  apply (MvPolynomial.sumRingEquiv (_root_.MIPStarRE.QPBT.PauliScalar P) (Fin P.m) (Fin P.m)).injective
  change _root_.MIPStarRE.QPBT.ExtendedLineGame.blockCoefficientPolynomial P g a reverse = _
  rw [hr, MvPolynomial.rename_rename]
  have heq : eqv ∘ (fun i => eqv.symm (.inr i)) = Sum.inr := by
    funext i
    exact eqv.apply_symm_apply _
  change MvPolynomial.C r =
    MvPolynomial.sumRingEquiv _ _ _ (MvPolynomial.rename
      (eqv ∘ (fun i => eqv.symm (.inr i))) r)
  rw [heq, sumRingEquiv_rename_inr]

private theorem scalarExpansion_combinePoly (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (f h : MvPolynomial (Fin P.m) (_root_.MIPStarRE.QPBT.PauliScalar P)) :
    MvPolynomial.sumRingEquiv _ _ _
      (MvPolynomial.rename (_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv P.m) (_root_.MIPStarRE.QPBT.combinePoly f h)) =
    MvPolynomial.C (MvPolynomial.rename
      (fun i => (_root_.MIPStarRE.QPBT.ExtendedLineGame.baseCoordinateEquiv P.m).symm (.inl i)) f) * MvPolynomial.X (0 : Fin 2) +
    MvPolynomial.C (MvPolynomial.rename
      (fun i => (_root_.MIPStarRE.QPBT.ExtendedLineGame.baseCoordinateEquiv P.m).symm (.inr i)) h) * MvPolynomial.X 1 := by
  have hX : _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv P.m ∘ _root_.MIPStarRE.QPBT.embX P.m =
      Sum.inr ∘ (fun i => (_root_.MIPStarRE.QPBT.ExtendedLineGame.baseCoordinateEquiv P.m).symm (.inl i)) := by
    funext i
    simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv, _root_.MIPStarRE.QPBT.embX]
  have hZ : _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv P.m ∘ _root_.MIPStarRE.QPBT.embZ P.m =
      Sum.inr ∘ (fun i => (_root_.MIPStarRE.QPBT.ExtendedLineGame.baseCoordinateEquiv P.m).symm (.inr i)) := by
    funext i
    simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv, _root_.MIPStarRE.QPBT.embZ]
  simp only [_root_.MIPStarRE.QPBT.combinePoly, map_add, map_mul, MvPolynomial.rename_X,
    MvPolynomial.rename_rename, hX, hZ]
  rw [← MvPolynomial.rename_rename, ← MvPolynomial.rename_rename]
  simp only [sumRingEquiv_rename_inr]
  have ha : _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv P.m (_root_.MIPStarRE.QPBT.alphaVar P.m) = .inl 0 := by
    simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv, _root_.MIPStarRE.QPBT.alphaVar]
  have hb : _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv P.m (_root_.MIPStarRE.QPBT.betaVar P.m) = .inl 1 := by
    simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv, _root_.MIPStarRE.QPBT.betaVar]
  rw [ha, hb, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.sumRingEquiv_X_inl]
  ring



end ExtendedLineGame

end

end MIPStarRE.QPBT

/-!
# Scalar and base coefficients of the rounded polynomial outcomes

The singleton polynomial is transported through the canonical field equivalence
and Mathlib's equivalence between a polynomial in a sum of variables and an
iterated polynomial ring. Its individual-degree certificate controls both levels.
Splitting each base coefficient by either block gives the partial degrees used
in the fiber calculation. Independence of both wrong blocks identifies the
outcome with the existing bounded polynomial-pair combining map.

## References

`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1310-1326`,
the coefficient expansion preceding `eq:qld-g-prime-bound`.
The partial coefficient argument and separated image are at lines 1341--1368,
`eq:qld-g-2` and `eq:qld-g-non-separable`; blueprint `lem:qld-4-7`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement



open MIPStarRE.QPBT.ExtendedLineGame

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (g : _root_.MIPStarRE.QPBT.DirectPolyTuple P.extendedDirectLd)
    (hlin : ∃ r t : MvPolynomial (Fin (2 * P.m)) (_root_.MIPStarRE.QPBT.PauliScalar P),
      _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarPolynomial P g = MvPolynomial.C r * MvPolynomial.X 0 +
        MvPolynomial.C t * MvPolynomial.X 1)
    (hX : ∃ r, _root_.MIPStarRE.QPBT.ExtendedLineGame.blockCoefficientPolynomial P g (Finsupp.single 0 1) true = MvPolynomial.C r)
    (hZ : ∃ r, _root_.MIPStarRE.QPBT.ExtendedLineGame.blockCoefficientPolynomial P g (Finsupp.single 1 1) false = MvPolynomial.C r) :
    ∃ pair : _root_.MIPStarRE.QPBT.PolyPair P,
      MvPolynomial.map (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1 =
        _root_.MIPStarRE.QPBT.combinePoly pair.1.1 pair.2.1 := by
  obtain ⟨f, hf⟩ := blockCoefficientPolynomial_const g _ true hX
  obtain ⟨h, hh⟩ := blockCoefficientPolynomial_const g _ false hZ
  refine ⟨(f, h), ?_⟩
  apply MvPolynomial.rename_injective (_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv P.m)
    (_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv P.m).injective
  apply (MvPolynomial.sumRingEquiv (_root_.MIPStarRE.QPBT.PauliScalar P) (Fin 2) (Fin (2 * P.m))).injective
  change _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarPolynomial P g = _
  rw [scalarExpansion_combinePoly]
  obtain ⟨r, t, hlin⟩ := hlin
  have h01 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro h
    simpa using congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  simp only [hlin, MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_X, h01, Ne.symm h01, ↓reduceIte, mul_one, mul_zero,
    add_zero, zero_add] at hf hh
  change r = MvPolynomial.rename (fun i => (_root_.MIPStarRE.QPBT.ExtendedLineGame.baseCoordinateEquiv P.m).symm (.inl i)) f.1 at hf
  change t = MvPolynomial.rename (fun i => (_root_.MIPStarRE.QPBT.ExtendedLineGame.baseCoordinateEquiv P.m).symm (.inr i)) h.1 at hh
  rw [hlin, hf, hh]
