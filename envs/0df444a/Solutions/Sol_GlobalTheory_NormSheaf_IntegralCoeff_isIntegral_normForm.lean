-- Prove2me | solution 1 for GlobalTheory.NormSheaf.IntegralCoeff.isIntegral_normForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:04:49.860017+00:00
-- url     : https://prove2.me/submissions/d20649d6-bc98-4811-97af-d83f495a4605

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffNormFormOfFamilyMemRangeIntegrallyClosed
import Theorems.Thm_GlobalTheory_NormSheaf_IntegralCoeff_leftMulMatrix_sum_tmul
import Theorems.Thm_GlobalTheory_NormSheaf_IntegralCoeff_isIntegral_det_of_aeval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
noncomputable section
open GlobalTheory GlobalTheory.NormSheaf GlobalTheory.NormSheaf.IntegralCoeff
open MvPolynomial
open scoped TensorProduct
namespace GlobalTheory.NormSheaf.IntegralCoeff
theorem _root_.solution (A K L : Type) [CommRing A] [Field K] [Field L] [Algebra A K]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L] {m : ℕ}
    (x : Fin m → L) (hx : ∀ i, IsIntegral A (x i)) :
    letI : Algebra (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) K) := MvPolynomial.algebraMvPolynomial
    IsIntegral (MvPolynomial (Fin m) A) (GlobalTheory.NormSheaf.normForm K L x) := by
  classical
  letI : Algebra (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) K) := MvPolynomial.algebraMvPolynomial
  set R := MvPolynomial (Fin m) K
  set R' := MvPolynomial (Fin m) A
  let F := FractionRing R
  haveI : IsScalarTower R' R F := inferInstance
  let S := R ⊗[K] L
  letI : Algebra R' S := ((algebraMap R S).comp (algebraMap R' R)).toAlgebra
  let y : S := ∑ i, (X i : R) ⊗ₜ[K] x i
  have hy : IsIntegral R' y := by
    refine IsIntegral.sum _ fun i _ => ?_
    have e : (X i : R) ⊗ₜ[K] x i = algebraMap R' S (X i) * (1 ⊗ₜ[K] x i) := by
      have hX : algebraMap R' R (X i) = X i := MvPolynomial.map_X _ _
      change _ = algebraMap R S (algebraMap R' R (X i)) * _
      rw [hX]
      change _ = ((X i : R) ⊗ₜ[K] (1 : L)) * (1 ⊗ₜ[K] x i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e]
    refine isIntegral_algebraMap.mul ?_
    refine IsIntegral.map_of_comp_eq (algebraMap A R')
      (Algebra.TensorProduct.includeRight : L →ₐ[K] S).toRingHom ?_ (hx i)
    refine RingHom.ext fun a => ?_
    change (algebraMap R' R (algebraMap A R' a)) ⊗ₜ[K] (1 : L) = (1 : R) ⊗ₜ[K] algebraMap A L a
    have h1 : algebraMap R' R (algebraMap A R' a) = algebraMap K R (algebraMap A K a) := by
      change MvPolynomial.map (algebraMap A K) (C a) = C (algebraMap A K a)
      exact MvPolynomial.map_C _ _
    rw [h1, IsScalarTower.algebraMap_apply A K L, Algebra.algebraMap_eq_smul_one (A := R) (algebraMap A K a),
      Algebra.algebraMap_eq_smul_one (A := L) (algebraMap A K a), TensorProduct.smul_tmul]
  obtain ⟨g, hgm, hgy⟩ := hy
  let bS := Algebra.TensorProduct.basis R (Module.finBasis K L)
  let φ : S →ₐ[R] Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) F :=
    (AlgHom.mapMatrix (Algebra.ofId R F)).comp (Algebra.leftMulMatrix bS)
  have hM : φ y = (algebraMap R F).mapMatrix
      (∑ i, (X i : R) • (Algebra.leftMulMatrix (Module.finBasis K L) (x i)).map (C : K →+* R)) := by
    rw [← leftMulMatrix_sum_tmul K L x]
    rfl
  have h0 : Polynomial.aeval (φ y) (g.map (algebraMap R' F)) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hh : (algebraMap F (Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) F)).comp (algebraMap R' F)
        = φ.toRingHom.comp (algebraMap R' S) := by
      refine RingHom.ext fun r => ?_
      change algebraMap F _ (algebraMap R' F r) = φ (algebraMap R S (algebraMap R' R r))
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R' R F]
      exact (IsScalarTower.algebraMap_apply R F _ _).symm
    rw [hh]
    have h2 := Polynomial.hom_eval₂ g (algebraMap R' S) φ.toRingHom y
    rw [hgy, map_zero] at h2
    exact h2.symm
  have hdet := isIntegral_det_of_aeval _ g hgm h0
  rw [hM, ← RingHom.map_det] at hdet
  exact (isIntegral_algebraMap_iff (IsFractionRing.injective R F)).mp hdet
end GlobalTheory.NormSheaf.IntegralCoeff
