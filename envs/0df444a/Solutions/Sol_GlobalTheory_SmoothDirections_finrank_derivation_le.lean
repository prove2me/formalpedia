-- Prove2me | solution 1 for GlobalTheory.SmoothDirections.finrank_derivation_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:11:04.831095+00:00
-- url     : https://prove2.me/submissions/adc8696f-4af8-423e-acb8-9bde71479544

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfDirectionsLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.SmoothDirections
namespace GlobalTheory.SmoothDirections
theorem _root_.solution {k R K : Type} [Field k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] [Algebra R K] [IsScalarTower k R K] {X : Scheme.{0}}
    (s : X ⟶ Sp k) (j : Sp R ⟶ X) [Mono j] (hj : j ≫ s = spMap (algebraMap k R)) {d : ℕ}
    (ht : ∀ (r : ℕ) (β : k →+* K) (x : Sp (TrivSqZeroExt K (Fin r → K)) ⟶ X),
      x ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) →
      (∀ lam : (Fin r → K) →ₗ[K] K,
        spMap (dirMap lam) ≫ x = constPt (spMap (dirMap lam) ≫ x) → lam = 0) → r ≤ d) :
    Module.finrank K (Derivation k R K) ≤ d := by
  obtain ⟨D, hD⟩ := exists_linearIndependent_of_le_finrank
    (le_refl (Module.finrank K (Derivation k R K)))
  refine ht _ (algebraMap k K) (spMap (derivationPoint D) ≫ j) ?_ ?_
  · rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a ↦ TrivSqZeroExt.ext ?_ ?_
    · simp [derivationPoint, ← IsScalarTower.algebraMap_apply, TrivSqZeroExt.algebraMap_eq_inl]
    · funext i
      simp [derivationPoint, TrivSqZeroExt.algebraMap_eq_inl]
  · intro lam h
    simp only [constPt, ← Category.assoc, cancel_mono] at h
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
    have h₁ := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
    have h₂ (a : R) : lam (fun i ↦ D i a) = 0 := by
      have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun h₁ a)
      simpa [dirMap, derivationPoint, TrivSqZeroExt.algebraMap_eq_inl] using this
    have h₃ := Fintype.linearIndependent_iff.mp hD (fun i ↦ lam (Pi.single i 1)) (by
      ext a
      have := h₂ a
      rw [← Finset.univ_sum_single (fun i ↦ D i a), map_sum] at this
      rw [Derivation.zero_apply, ← this]
      refine (congrFun (map_sum (Derivation.coeFnAddMonoidHom (R := k) (A := R) (M := K)) _ _) a).trans ?_
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      change lam (Pi.single i 1) • D i a = _
      rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← map_smul, ← Pi.single_smul, smul_eq_mul,
        _root_.mul_one])
    refine (Pi.basisFun K _).ext fun i ↦ ?_
    simpa using h₃ i
end GlobalTheory.SmoothDirections
