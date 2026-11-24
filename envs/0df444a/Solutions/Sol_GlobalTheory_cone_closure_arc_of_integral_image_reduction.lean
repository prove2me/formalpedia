-- Prove2me | solution 1 for GlobalTheory.cone_closure_arc_of_integral_image_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:56:32.050043+00:00
-- url     : https://prove2.me/submissions/a279fd43-28a6-421f-9a39-df70af24d941

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ConeClosureArcOfIntegralImageReduction
import Theorems.Thm_GlobalTheory_exists_homogeneous_lift_nat_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (F K J ι : Type) [Field F] [Field K] [Algebra F K] [Fintype J] [Finite ι] (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)], (∀ i, Algebra.FiniteType F (A i)) → ∀ (w : ∀ i, J → A i) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J F) (d : ℕ), G.IsHomogeneous d → (∀ i, MvPolynomial.aeval (w i) G = 0) → MvPolynomial.aeval v G = 0) → ∃ (i : ι) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A i →+* FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ (∀ x : F, f (algebraMap F (A i) x) = algebraMap W (FractionRing W) (algebraMap K W (algebraMap F K x))) ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w i j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W) → (∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∃ (F : Type) (_ : Field F) (_ : CharZero F) (φ' : R →+* F), (∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ' r = n * x) ∧ ∀ (A : Type) [CommRing A] [Algebra ℚ A] (χ : R →+* A), (∀ r, φ r = 0 → χ r = 0) → ∃ χ' : F →+* A, χ'.comp φ' = χ) → ∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∀ (K J ι : Type) [Field K] [CharZero K] [Fintype J] [Finite ι] (ψ : R →+* K), (∀ r, φ r = 0 → ψ r = 0) → ∀ (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra ℚ (A i)], (∀ i, Algebra.FiniteType ℚ (A i)) → ∀ (χ : ∀ i, R →+* A i), (∀ i r, φ r = 0 → χ i r = 0) → ∀ (w : ∀ i, J → A i) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J R) (d : ℕ), G.IsHomogeneous d → (∀ i, MvPolynomial.eval₂ (χ i) (w i) G = 0) → MvPolynomial.eval₂ ψ v G = 0) → ∃ (i : ι) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A i →+* FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ (∀ r : R, f (χ i r) = algebraMap W (FractionRing W) (algebraMap K W (ψ r))) ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w i j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W := by
  intro H1 H2 R _ φ hφ K J ι _ _ _ _ ψ hψ A _ _ hA χ hχ w v hv hG
  obtain ⟨F, _, _, φ', hF, hlift⟩ := H2 R φ hφ
  obtain ⟨ψ', hψ'⟩ := hlift K ψ hψ
  choose χ' hχ' using fun i => hlift (A i) (χ i) (hχ i)
  letI : Algebra F K := ψ'.toAlgebra
  letI : ∀ i, Algebra F (A i) := fun i => (χ' i).toAlgebra
  have hA' : ∀ i, Algebra.FiniteType F (A i) := fun i => by
    haveI : IsScalarTower ℚ F (A i) :=
      IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI := hA i
    exact Algebra.FiniteType.of_restrictScalars_finiteType ℚ F (A i)
  obtain ⟨i, W, _, _, _, _, f, s, w', h1, h2, h3, h4⟩ := H1 F K J ι A hA' w v hv (by
    intro G d hd h0
    obtain ⟨n, G', hn, hG', hmap⟩ := exists_homogeneous_lift_nat_mul φ' hF G d hd
    have key := hG G' d hG' (fun i => by
      have : MvPolynomial.eval₂ (χ i) (w i) G'
          = MvPolynomial.aeval (w i) (MvPolynomial.map φ' G') := by
        rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← hχ' i]; rfl
      rw [this, hmap, map_mul, h0 i, mul_zero])
    have : MvPolynomial.eval₂ ψ v G' = MvPolynomial.aeval v (MvPolynomial.map φ' G') := by
      rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← hψ']; rfl
    rw [this, hmap, map_mul, map_natCast] at key
    exact (mul_eq_zero.1 key).resolve_left (Nat.cast_ne_zero.2 hn.ne'))
  refine ⟨i, W, inferInstance, inferInstance, inferInstance, inferInstance, f, s, w', h1, h2, fun r => ?_, h4⟩
  have := h3 (φ' r)
  rw [← hχ' i, ← hψ']
  exact this
end GlobalTheory
