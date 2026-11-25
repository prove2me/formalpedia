-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CayleyAny.mobius_selfadj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:18:37.427394+00:00
-- url     : https://prove2.me/submissions/da8d2bcb-85b9-48ef-ba21-972ef52e3748

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaResiduallyUnipotentCayleyTransform
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_CayleyCase___algebraMap_33721809830a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyAny
open GlobalTheory.UnitLemma.CayleyCase
variable {K : UQ}
namespace GlobalTheory.UnitLemma.CayleyAny
theorem _root_.solution (B : InvAlg K) (x y ξ : K.O) (Y : B.A) (hu : B.g * B.σ B.g = 1)
    (hxy : K.c (algebraMap K.O K.E x) = algebraMap K.O K.E y)
    (hξ : algebraMap K.O K.E ξ * K.c (algebraMap K.O K.E ξ) = 1)
    (w : B.A) (hw : (B.g - algebraMap K.O B.A ξ) * w = 1)
    (hY : Y * (B.g - algebraMap K.O B.A ξ) =
      algebraMap K.O B.A y * B.g - algebraMap K.O B.A x * algebraMap K.O B.A ξ) :
    B.σ Y = Y := by
  have sx : B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A y := by
    rw [σ_algebraMap, hxy, ← IsScalarTower.algebraMap_apply]
  have sy : B.σ (algebraMap K.O B.A y) = algebraMap K.O B.A x := by
    rw [σ_algebraMap, ← hxy, K.c_c, ← IsScalarTower.algebraMap_apply]
  have hξA : algebraMap K.O B.A ξ * B.σ (algebraMap K.O B.A ξ) = 1 := by
    rw [σ_algebraMap, IsScalarTower.algebraMap_apply K.O K.E B.A ξ, ← map_mul, hξ, map_one]
  have h1 := congrArg B.σ hY
  rw [map_mul, map_sub, map_sub, map_mul, map_mul, sx, sy] at h1
  set G := B.g
  set Gs := B.σ B.g
  set ξA := algebraMap K.O B.A ξ
  set ξs := B.σ (algebraMap K.O B.A ξ)
  set xA := algebraMap K.O B.A x
  set yA := algebraMap K.O B.A y
  have key : (B.σ Y - Y) * (G - ξA) = 0 := by
    linear_combination (-G * ξA) * h1 - hY - (xA * ξA - B.σ Y * ξA) * hu - (B.σ Y * G - yA * G) * hξA
  calc B.σ Y = B.σ Y * ((G - ξA) * w) := by rw [hw, mul_one]
    _ = Y * ((G - ξA) * w) + (B.σ Y - Y) * (G - ξA) * w := by ring
    _ = Y := by rw [key, hw]; ring
end GlobalTheory.UnitLemma.CayleyAny
