-- Prove2me | solution 1 for GlobalTheory.RelDimFibCrit.trdeg_residueField_of_minimal_in_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:36:58.440698+00:00
-- url     : https://prove2.me/submissions/0714eb46-ac3b-4636-99d3-f6384a8f6b71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TrdegResidueFieldEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsAlgebraicOfEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsoInvCompSpec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SmoothRelativeDimOfTrdeg
import Theorems.Thm_GlobalTheory_FibreMinimalPrime_trdeg_residueField_eq
import Theorems.Thm_GlobalTheory_residueField_isAlgebraic_of_etale


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.RelDimFibCrit
namespace GlobalTheory.RelDimFibCrit
theorem _root_.solution {R B : Type} [CommRing R] [CommRing B] (φ : R →+* B) (r : ℕ)
    (hφ : φ.IsStandardSmoothOfRelativeDimension r) (P : Ideal B) [P.IsPrime]
    (hP : ∀ P' : Ideal B, P'.IsPrime → P' ≤ P → P'.comap φ = P.comap φ → P' = P) :
    @Algebra.trdeg (P.comap φ).ResidueField P.ResidueField _ _
      (Ideal.ResidueField.map (P.comap φ) P φ rfl).toAlgebra = r := by
  obtain ⟨g, rfl, hg⟩ := hφ.exists_etale_mvPolynomial
  have hQ : ∀ Q' : Ideal (MvPolynomial (Fin r) R), Q'.IsPrime → Q' ≤ P.comap g →
      Q'.comap (MvPolynomial.C : R →+* _) = (P.comap g).comap MvPolynomial.C → Q' = P.comap g := by
    intro Q' hQ' hle hc
    letI := g.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin r) R) B := hg
    haveI : Module.Flat (MvPolynomial (Fin r) R) B := inferInstance
    haveI : P.LiesOver (P.comap g) := ⟨rfl⟩
    obtain ⟨P', hP'le, hP'prime, hP'over⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := Q') P hle
    have hP'Q : P'.comap g = Q' := hP'over.over.symm
    have := hP P' hP'prime hP'le (by rw [← Ideal.comap_comap, hP'Q, hc, Ideal.comap_comap])
    rw [← hP'Q, this]
  have h1 := GlobalTheory.FibreMinimalPrime.trdeg_residueField_eq r (P.comap g) hQ
  have h2 := GlobalTheory.residueField_isAlgebraic_of_etale g hg P
  letI i12 := (Ideal.ResidueField.map ((P.comap g).comap MvPolynomial.C) (P.comap g)
    (MvPolynomial.C : R →+* _) rfl).toAlgebra
  letI i23 := (Ideal.ResidueField.map (P.comap g) P g rfl).toAlgebra
  letI i13 := (Ideal.ResidueField.map ((P.comap g).comap (MvPolynomial.C : R →+* _)) P
    (g.comp MvPolynomial.C) rfl).toAlgebra
  haveI : IsScalarTower ((P.comap g).comap (MvPolynomial.C : R →+* _)).ResidueField
      (P.comap g).ResidueField P.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    rw [Ideal.ResidueField.map_algebraMap _ (P.comap g) (MvPolynomial.C : R →+* _) rfl x,
      Ideal.ResidueField.map_algebraMap (P.comap g) P g rfl]
    exact Ideal.ResidueField.map_algebraMap ((P.comap g).comap (MvPolynomial.C : R →+* _)) P
      (g.comp MvPolynomial.C) rfl x
  have := trdeg_add_eq ((P.comap g).comap (MvPolynomial.C : R →+* _)).ResidueField
    (P.comap g).ResidueField (A := P.ResidueField)
  rw [h1, trdeg_eq_zero, add_zero] at this
  exact this.symm
end GlobalTheory.RelDimFibCrit
