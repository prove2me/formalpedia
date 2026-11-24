-- Prove2me | solution 1 for GlobalTheory.exists_etale_algHom_lift_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:50:08.772697+00:00
-- url     : https://prove2.me/submissions/e8640630-1d2c-4273-aa29-712edf523c8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Theorems.Thm_GlobalTheory_exists_etale_subset_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
universe u
variable {R : Type*} {A B : Type u} {K : Type*} [CommRing R] [CommRing A] [CommRing B] [Field K]
  [Algebra R A] [Algebra R B] [Algebra R K] [IsLocalRing B] [Algebra B K] [IsScalarTower R B K]
  [Algebra (ResidueField B) K] [IsScalarTower B (ResidueField B) K]
  [Algebra.IsSeparable (ResidueField B) K]
namespace GlobalTheory
theorem _root_.solution [Algebra.Smooth R A] (φ : A →ₐ[R] K) :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra B W) (_ : Algebra.Etale B W) (ψ : A →+* W)
      (ε : W →ₐ[B] K), ψ.comp (algebraMap R A) = (algebraMap B W).comp (algebraMap R B) ∧
        ∀ a, ε (ψ a) = φ a := by
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R)
    (p := RingHom.ker φ)
  let S := Localization.Away f
  let P := MvPolynomial (Fin n) R
  let φ' : S →ₐ[R] K := IsLocalization.Away.liftAlgHom f (Ne.isUnit hf)
  obtain ⟨Q, ε, hε⟩ := exists_etale_subset_range (B := B)
    fun i : Fin n => φ' (algebraMap P S (MvPolynomial.X i))
  choose c hc using hε
  let E := Q.Ring
  letI : Algebra R E := ((algebraMap B E).comp (algebraMap R B)).toAlgebra
  have : IsScalarTower R B E := .of_algebraMap_eq' rfl
  let χ : P →ₐ[R] K := φ'.comp (IsScalarTower.toAlgHom R _ _)
  have hχ : (ε.restrictScalars R).comp (MvPolynomial.aeval c) = χ := by
    ext i
    exact (congrArg ε (MvPolynomial.aeval_X c i)).trans (hc i)
  letI := (MvPolynomial.aeval (R := R) c).toAlgebra
  letI := χ.toAlgebra
  letI := ε.toAlgebra
  have : IsScalarTower B E K := .of_algebraMap_eq fun r => (ε.commutes r).symm
  have : IsScalarTower P E K := .of_algebraMap_eq fun r => congr($hχ r).symm
  let φ'' : S →ₐ[P] K := ⟨φ', fun r => rfl⟩
  let W := E ⊗[P] S
  let ε' : W →ₐ[E] K := Algebra.TensorProduct.lift (Algebra.ofId E K) φ'' fun _ _ => .all _ _
  refine ⟨W, inferInstance, inferInstance, Algebra.Etale.comp B E W,
    (Algebra.TensorProduct.includeRight (R := P) (A := E) (B := S)).toRingHom.comp
      (algebraMap A S), ε'.restrictScalars B, RingHom.ext fun r => ?_, fun a => ?_⟩
  · change (1 : E) ⊗ₜ[P] algebraMap A S (algebraMap R A r) = (algebraMap R E r) ⊗ₜ[P] (1 : S)
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R P S,
      ← (MvPolynomial.aeval (R := R) c).commutes r]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul _).symm
  · change ε' ((1 : E) ⊗ₜ[P] algebraMap A S a) = φ a
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact (show φ' (algebraMap A _ a) = φ a by simp [φ'])
end GlobalTheory
