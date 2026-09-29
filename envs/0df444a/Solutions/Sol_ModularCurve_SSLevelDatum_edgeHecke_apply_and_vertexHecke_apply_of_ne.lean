-- Prove2me | solution 1 for ModularCurve.SSLevelDatum.edgeHecke_apply_and_vertexHecke_apply_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/650a2a1d-c7c6-56d5-8c6d-8f21a9105f8b

import Mathlib
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ComponentGroupHecke
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSLevelDatum_edgeHecke_apply_and_vertexHecke_apply_of_ne

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace IdentB0

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable [HasPrincipalDivisors K F']
variable (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)

open Classical in

theorem correspondence_single_one_apply (x y : Place K F) :
    Divisor.correspondence φ ψ hφ hψ (Finsupp.single x 1) y =
      ∑ W ∈ Place.fiberAlong φ hφ x,
        if W.restrictAlong ψ hψ = y then
          (W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong ψ hψ : ℤ) else 0 := by
  classical
  rw [Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Divisor.pushforwardAlong_single, Finsupp.single_apply, one_mul]
  all_goals (split_ifs <;> rfl)

open Classical in

theorem correspondence_single_one_apply_eq_finsum (x y : Place K F) :
    Divisor.correspondence φ ψ hφ hψ (Finsupp.single x 1) y =
      ∑ᶠ W : Place K F',
        if W.restrictAlong φ hφ = x ∧ W.restrictAlong ψ hψ = y then
          (W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong ψ hψ : ℤ) else 0 := by
  classical
  rw [correspondence_single_one_apply]
  symm
  rw [finsum_eq_sum_of_support_subset _ (s := Place.fiberAlong φ hφ x)]
  · refine Finset.sum_congr rfl fun W hW => ?_
    rw [Place.mem_fiberAlong] at hW
    simp only [hW, true_and]
  · intro W hW
    rw [Function.mem_support] at hW
    simp only [Finset.mem_coe, Place.mem_fiberAlong]
    by_contra hx
    exact hW (if_neg fun h => hx h.1)

end Generic

section SS

open ModularCurve

variable (p : ℕ) (K : Type*) [Field K] [DecidableEq K] (N : ℕ) [NeZero N]

theorem ssHeckeMatrixC_apply_eq_correspondence (ℓ : ℕ) [NeZero ℓ]
    [HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ)]
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (y x : ↥(ssPlaces p N K)) :
    ssHeckeMatrixC p K N ℓ hα hβ y x =
      Divisor.correspondence (heckeBetaC K N ℓ) (heckeAlphaC K N ℓ) hβ hα (Finsupp.single x.1 1) y.1 := by
  rw [correspondence_single_one_apply_eq_finsum]
  all_goals rfl

variable [Fact p.Prime] [CharP K p]

theorem ssHeckeFamilyC_apply_of_ne (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
    (hlegs : ∀ (ℓ : ℕ) [NeZero ℓ], (heckeAlphaC K N ℓ).toRingHom.IsIntegral ∧ (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ≠ p) [NeZero (ℓ : ℕ)]
    [HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ)] (y x : ↥(ssPlaces p N K)) :
    ssHeckeFamilyC p K N data hKr hlegs ℓ y x =
      Divisor.correspondence (heckeBetaC K N ℓ) (heckeAlphaC K N ℓ) (hlegs ℓ).2 (hlegs ℓ).1
        (Finsupp.single x.1 1) y.1 := by
  unfold ssHeckeFamilyC
  rw [if_neg hℓ]
  exact ssHeckeMatrixC_apply_eq_correspondence p K N ℓ (hlegs ℓ).1 (hlegs ℓ).2 y x

open Classical in
theorem ssHeckeFamilyC_apply_self (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
    (hlegs : ∀ (ℓ : ℕ) [NeZero ℓ], (heckeAlphaC K N ℓ).toRingHom.IsIntegral ∧ (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) = p) (y x : ↥(ssPlaces p N K)) :
    ssHeckeFamilyC p K N data hKr hlegs ℓ y x = if frobOnPlacesGeomLevel K N data hKr x.1 = y.1 then 1 else 0 := by
  unfold ssHeckeFamilyC
  rw [if_pos hℓ]
  rfl

end SS

section Datum

open ModularCurve

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p] [DecidableEq K] {M s : ℕ} [NeZero M] [NeZero s]
variable (X : SSLevelDatum p K M s)

theorem edgeHecke_apply_of_ne (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ≠ p) [NeZero (ℓ : ℕ)]
    [HasPrincipalDivisors K ↥(charLDegeneracyRoof K (M * s) ℓ)] (y x : ↥(ssPlaces p (M * s) K)) :
    X.edgeHecke ℓ y x =
      Divisor.correspondence (heckeBetaC K (M * s) ℓ) (heckeAlphaC K (M * s) ℓ)
        (X.legsIntegral (M * s) ℓ).2 (X.legsIntegral (M * s) ℓ).1 (Finsupp.single x.1 1) y.1 :=
  ssHeckeFamilyC_apply_of_ne p K (M * s) X.frobData X.kronecker (X.legsIntegral (M * s)) ℓ hℓ y x

theorem vertexHecke_apply_of_ne (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ≠ p) [NeZero (ℓ : ℕ)]
    [HasPrincipalDivisors K ↥(charLDegeneracyRoof K M ℓ)] (y x : ↥(ssPlaces p M K)) :
    X.vertexHecke ℓ y x =
      Divisor.correspondence (heckeBetaC K M ℓ) (heckeAlphaC K M ℓ)
        (X.legsIntegral M ℓ).2 (X.legsIntegral M ℓ).1 (Finsupp.single x.1 1) y.1 :=
  ssHeckeFamilyC_apply_of_ne p K M X.frobData X.kronecker (X.legsIntegral M) ℓ hℓ y x

open Classical in
theorem edgeHecke_apply_self (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) = p) (y x : ↥(ssPlaces p (M * s) K)) :
    X.edgeHecke ℓ y x = if frobOnPlacesGeomLevel K (M * s) X.frobData X.kronecker x.1 = y.1 then 1 else 0 :=
  ssHeckeFamilyC_apply_self p K (M * s) X.frobData X.kronecker (X.legsIntegral (M * s)) ℓ hℓ y x

open Classical in
theorem vertexHecke_apply_self (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) = p) (y x : ↥(ssPlaces p M K)) :
    X.vertexHecke ℓ y x = if frobOnPlacesGeomLevel K M X.frobData X.kronecker x.1 = y.1 then 1 else 0 :=
  ssHeckeFamilyC_apply_self p K M X.frobData X.kronecker (X.legsIntegral M) ℓ hℓ y x

theorem degeneracyData_a (W : ↥(ssPlaces p (M * s) K)) :
    (X.degeneracyData.a W : Place K (modularFunctionFieldC K M)) =
      Place.restrictAlong (levelAlphaC K M s X.mem_M) X.fstIntegral W.1 := rfl

theorem degeneracyData_b (W : ↥(ssPlaces p (M * s) K)) :
    (X.degeneracyData.b W : Place K (modularFunctionFieldC K M)) =
      Place.restrictAlong (levelBetaC K M s X.mem_s) X.sndIntegral W.1 := rfl

theorem degeneracyData_w (W : ↥(ssPlaces p (M * s) K)) :
    X.degeneracyData.w W = Nat.toPNat' (placeWidth (M * s) W.1) := rfl

end Datum

end IdentB0

open IdentB0

theorem solution
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p] [DecidableEq K]
    {M s : ℕ} [NeZero M] [NeZero s] (X : SSLevelDatum p K M s)
    (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ≠ p) [NeZero (ℓ : ℕ)] :
    (∀ [HasPrincipalDivisors K ↥(charLDegeneracyRoof K (M * s) ℓ)] (y x : ↥(ssPlaces p (M * s) K)),
        X.edgeHecke ℓ y x =
          Divisor.correspondence (heckeBetaC K (M * s) ℓ) (heckeAlphaC K (M * s) ℓ)
            (X.legsIntegral (M * s) ℓ).2 (X.legsIntegral (M * s) ℓ).1 (Finsupp.single x.1 1) y.1) ∧
    (∀ [HasPrincipalDivisors K ↥(charLDegeneracyRoof K M ℓ)] (y x : ↥(ssPlaces p M K)),
        X.vertexHecke ℓ y x =
          Divisor.correspondence (heckeBetaC K M ℓ) (heckeAlphaC K M ℓ)
            (X.legsIntegral M ℓ).2 (X.legsIntegral M ℓ).1 (Finsupp.single x.1 1) y.1) := by
  refine ⟨?_, ?_⟩
  · intro _ y x
    exact IdentB0.edgeHecke_apply_of_ne X ℓ hℓ y x
  · intro _ y x
    exact IdentB0.vertexHecke_apply_of_ne X ℓ hℓ y x

end S_ModularCurve_SSLevelDatum_edgeHecke_apply_and_vertexHecke_apply_of_ne
end P2MW
export P2MW.S_ModularCurve_SSLevelDatum_edgeHecke_apply_and_vertexHecke_apply_of_ne (solution)
