-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CayleyCase.cayley_selfadj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:04:33.909442+00:00
-- url     : https://prove2.me/submissions/4381b662-af8f-4f6e-b26f-81aef533a5ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_CayleyCase___algebraMap_33721809830a
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase
variable {K : UQ}
namespace GlobalTheory.UnitLemma.CayleyCase
theorem _root_.solution (B : InvAlg K) (s ε : K.O) (Y : B.A) (hu : B.g * B.σ B.g = 1)
    (hs : algebraMap K.O K.E s * K.c (algebraMap K.O K.E s) = 1)
    (hε : K.c (algebraMap K.O K.E ε) = -algebraMap K.O K.E ε)
    (w : B.A) (hw : (B.g + algebraMap K.O B.A s) * w = 1)
    (hY : Y * (B.g + algebraMap K.O B.A s) = algebraMap K.O B.A ε * (B.g - algebraMap K.O B.A s)) :
    B.σ Y = Y := by
  have h1 := congrArg B.σ hY
  simp only [map_mul, map_add, map_sub, σ_algebraMap, hε, map_neg] at h1
  have he : algebraMap K.E B.A (algebraMap K.O K.E ε) = algebraMap K.O B.A ε :=
    (IsScalarTower.algebraMap_apply _ _ _ _).symm
  rw [he] at h1
  have hs0 : algebraMap K.O B.A s * algebraMap K.E B.A (K.c (algebraMap K.O K.E s)) = 1 := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A s, ← map_mul, hs, map_one]
  set s' := algebraMap K.O B.A s
  set t := algebraMap K.E B.A (K.c (algebraMap K.O K.E s))
  have hs' : s' * t = 1 := hs0
  set ε' := algebraMap K.O B.A ε
  have key : (B.σ Y - Y) * (B.g + s') = 0 := by
    linear_combination (B.g * s') * h1 - hY - (s' * B.σ Y + s' * ε') * hu - (B.g * B.σ Y - B.g * ε') * hs'
  calc B.σ Y = B.σ Y * ((B.g + s') * w) := by rw [hw, mul_one]
    _ = Y * ((B.g + s') * w) + (B.σ Y - Y) * (B.g + s') * w := by ring
    _ = Y := by rw [key, hw]; ring
end GlobalTheory.UnitLemma.CayleyCase
