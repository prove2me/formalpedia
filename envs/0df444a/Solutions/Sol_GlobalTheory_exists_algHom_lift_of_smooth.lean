-- Prove2me | solution 1 for GlobalTheory.exists_algHom_lift_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:33:52.014565+00:00
-- url     : https://prove2.me/submissions/2ebd1a2d-1bcf-4b35-af52-93265bef8a30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Theorems.Thm_GlobalTheory_isLocalRing_of_surjective_of_henselian
import Theorems.Thm_GlobalTheory_exists_algHom_lift_of_isStandardEtale

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
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]
namespace GlobalTheory
theorem _root_.solution [Algebra.Smooth R A] [IsLocalRing B] (I : Ideal B)
    [HenselianRing B I] (π : B →ₐ[R] C) (hπ : Function.Surjective π) (hI : ∀ b, b ∈ I ↔ π b = 0)
    (φ : A →ₐ[R] C) : ∃ ψ : A →ₐ[R] B, π.comp ψ = φ := by
  have : IsLocalRing C := isLocalRing_of_surjective_of_henselian I (π : B →+* C) hπ hI
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R)
    (p := (maximalIdeal C).comap φ)
  have hφf : IsUnit (φ f) := by simpa using hf
  let φ' : Localization.Away f →ₐ[R] C := IsLocalization.Away.liftAlgHom f hφf
  choose b hb using fun i : Fin n => hπ (φ' (algebraMap _ _ (MvPolynomial.X (R := R) i)))
  let χ : MvPolynomial (Fin n) R →ₐ[R] C := φ'.comp (IsScalarTower.toAlgHom R _ _)
  have hχ : π.comp (MvPolynomial.aeval b) = χ := by ext i; simp [χ, hb]
  letI := (MvPolynomial.aeval (R := R) b).toAlgebra
  letI := χ.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) B :=
    .of_algebraMap_eq fun r => ((MvPolynomial.aeval (R := R) b).commutes r).symm
  let π' : B →ₐ[MvPolynomial (Fin n) R] C := ⟨π, fun r => congr($hχ r)⟩
  let φ'' : Localization.Away f →ₐ[MvPolynomial (Fin n) R] C := ⟨φ', fun r => rfl⟩
  obtain ⟨ψ, hψ⟩ := exists_algHom_lift_of_isStandardEtale I π' hπ hI φ''
  refine ⟨(ψ.restrictScalars R).comp (IsScalarTower.toAlgHom R A _), AlgHom.ext fun a => ?_⟩
  exact congr($hψ (algebraMap A _ a)).trans (show φ' (algebraMap A _ a) = φ a by simp [φ'])
end GlobalTheory
