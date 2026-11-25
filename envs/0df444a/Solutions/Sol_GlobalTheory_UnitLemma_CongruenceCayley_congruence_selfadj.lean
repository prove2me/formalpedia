-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CongruenceCayley.congruence_selfadj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:34:52.109121+00:00
-- url     : https://prove2.me/submissions/b6e7298a-61a5-4ab1-a412-ce58ad281cb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KappaSumZeroAndStableSumMulZeroOfNotIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaResiduallyUnipotentCayleyTransform
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityOfPrincipalCongruence
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_CayleyCase___algebraMap_33721809830a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CongruenceCayley
open GlobalTheory.UnitLemma.CayleyCase
variable {K : UQ}
namespace GlobalTheory.UnitLemma.CongruenceCayley
theorem _root_.solution (B : InvAlg K) (a x y : K.O) (ha0 : a ≠ 0)
    (hac : K.c (algebraMap K.O K.E a) = algebraMap K.O K.E a)
    (hxy : K.c (algebraMap K.O K.E x) = algebraMap K.O K.E y)
    (hu : (1 + algebraMap K.O B.A a * B.g) * B.σ (1 + algebraMap K.O B.A a * B.g) = 1)
    (Y w : B.A)
    (hw : (algebraMap K.O B.A (x - y) + algebraMap K.O B.A (x * a) * B.g) * w = 1)
    (hY : Y * (algebraMap K.O B.A (x - y) + algebraMap K.O B.A (x * a) * B.g) =
      algebraMap K.O B.A (x * y) * B.g) :
    B.σ Y = Y := by
  have sx : B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A y := by
    rw [σ_algebraMap, hxy, ← IsScalarTower.algebraMap_apply]
  have sy : B.σ (algebraMap K.O B.A y) = algebraMap K.O B.A x := by
    rw [σ_algebraMap, ← hxy, K.c_c, ← IsScalarTower.algebraMap_apply]
  have sa : B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A a := by
    rw [σ_algebraMap, hac, ← IsScalarTower.algebraMap_apply]
  have h1 := congrArg B.σ hY
  simp only [map_mul, map_sub, map_add, sx, sy, sa] at h1 hY hw
  rw [map_add, map_one, map_mul, sa] at hu
  set G := B.g
  set S := B.σ B.g
  set xA := algebraMap K.O B.A x
  set yA := algebraMap K.O B.A y
  set aA := algebraMap K.O B.A a
  have key : (B.σ Y - Y) * (xA - yA + xA * aA * G) * aA = 0 := by
    linear_combination (-aA * (1 + aA * G)) * h1 - (xA * yA - aA * B.σ Y * yA) * hu - aA * hY
  have key2 : (B.σ Y - Y) * aA = 0 := by
    calc (B.σ Y - Y) * aA = (B.σ Y - Y) * (xA - yA + xA * aA * G) * aA * w := by
          linear_combination (-(B.σ Y - Y) * aA) * hw
      _ = 0 := by rw [key, zero_mul]
  have hae : algebraMap K.O K.E a ≠ 0 := by
    intro h; exact ha0 (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))
  have : (algebraMap K.O K.E a) • (B.σ Y - Y) = 0 := by
    rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_comm]; exact key2
  exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_left hae)
end GlobalTheory.UnitLemma.CongruenceCayley
