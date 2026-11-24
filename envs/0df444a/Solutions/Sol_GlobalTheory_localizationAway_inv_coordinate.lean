-- Prove2me | solution 1 for GlobalTheory.localizationAway_inv_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:02.369893+00:00
-- url     : https://prove2.me/submissions/baf3334d-21d2-4a97-91a2-17ffb2ee8d3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInversionCoordinateLocalizationPolynomial
import Theorems.Thm_GlobalTheory_awayLiftAlgHom_algebraMap
import Theorems.Thm_GlobalTheory_aeval_reverse_mul_pow_of_mul_eq_one
import Theorems.Thm_GlobalTheory_algebraMap_eq_aeval_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (k : Type) [Field k] (P : Polynomial k) (hP : P ≠ 0) :
    ∃ Q : Polynomial k, Q ≠ 0 ∧
      ∃ (σ : Localization.Away P →ₐ[k] Localization.Away Q)
        (τ : Localization.Away Q →ₐ[k] Localization.Away (Polynomial.X * P)),
        (τ.comp σ).toRingHom.comp (algebraMap (Polynomial k) (Localization.Away P)) =
            algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) ∧
          τ.toRingHom.comp (algebraMap (Polynomial k) (Localization.Away Q)) =
            (Polynomial.aeval (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P *
              IsLocalization.Away.invSelf (Polynomial.X * P))).toRingHom := by
  classical
  have hrev : P.reverse ≠ 0 := fun h => hP (reverse_eq_zero.mp h)
  refine ⟨X * P.reverse, mul_ne_zero X_ne_zero hrev, ?_⟩

  set C := Localization.Away (X * P)
  set u : C := IsLocalization.Away.invSelf (X * P)
  have hu : algebraMap k[X] C (X * P) * u = 1 := IsLocalization.Away.mul_invSelf _
  set xC : C := algebraMap k[X] C X
  set xi : C := algebraMap k[X] C P * u
  have hxC : xC * xi = 1 := by rw [← hu, map_mul]; ring
  have hPC : IsUnit (algebraMap k[X] C P) :=
    isUnit_iff_exists_inv.mpr ⟨xC * u, by rw [← hu, map_mul]; ring⟩
  have hxi : IsUnit xi := isUnit_iff_exists_inv'.mpr ⟨xC, hxC⟩
  have hτ : IsUnit (aeval xi (X * P.reverse)) := by
    rw [map_mul, aeval_X]
    refine hxi.mul ?_
    have key := aeval_reverse_mul_pow_of_mul_eq_one (k := k) xC xi hxC P
    rw [← algebraMap_eq_aeval_X] at key
    exact isUnit_of_mul_isUnit_left (key ▸ hPC)
  let τ := awayLiftAlgHom (X * P.reverse) (aeval xi) hτ

  set B := Localization.Away (X * P.reverse)
  set v : B := IsLocalization.Away.invSelf (X * P.reverse)
  have hv : algebraMap k[X] B (X * P.reverse) * v = 1 := IsLocalization.Away.mul_invSelf _
  set yB : B := algebraMap k[X] B X
  set yi : B := algebraMap k[X] B P.reverse * v
  have hyB : yB * yi = 1 := by rw [← hv, map_mul]; ring
  have hrevB : IsUnit (algebraMap k[X] B P.reverse) :=
    isUnit_iff_exists_inv.mpr ⟨yB * v, by rw [← hv, map_mul]; ring⟩
  have hyi : IsUnit yi := isUnit_iff_exists_inv'.mpr ⟨yB, hyB⟩
  have hσ : IsUnit (aeval yi P) := by
    have key := aeval_reverse_mul_pow_of_mul_eq_one (k := k) yi yB (by rw [mul_comm]; exact hyB) P
    rw [← algebraMap_eq_aeval_X] at key
    rw [← key]
    exact hrevB.mul (hyi.pow _)
  let σ := awayLiftAlgHom P (aeval yi) hσ
  have hτalg : ∀ q : k[X], τ (algebraMap k[X] B q) = aeval xi q :=
    awayLiftAlgHom_algebraMap _ _ _
  have hσalg : ∀ q : k[X], σ (algebraMap k[X] (Localization.Away P) q) = aeval yi q :=
    awayLiftAlgHom_algebraMap _ _ _
  refine ⟨σ, τ, ?_, ?_⟩
  · have hτyi : τ yi = xC := by
      have h1 : τ yB * τ yi = 1 := by rw [← map_mul, hyB, map_one]
      have h2 : τ yB = xi := by rw [hτalg, aeval_X]
      rw [h2] at h1
      calc τ yi = τ yi * (xC * xi) := by rw [hxC, mul_one]
        _ = xC * (xi * τ yi) := by ring
        _ = xC := by rw [h1, mul_one]
    have hext : ((τ.comp σ).comp (IsScalarTower.toAlgHom k k[X] (Localization.Away P))) =
        IsScalarTower.toAlgHom k k[X] C := by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
      rw [hσalg, aeval_X, hτyi]
    exact RingHom.ext fun p => DFunLike.congr_fun hext p
  · exact RingHom.ext fun p => hτalg p
end GlobalTheory
