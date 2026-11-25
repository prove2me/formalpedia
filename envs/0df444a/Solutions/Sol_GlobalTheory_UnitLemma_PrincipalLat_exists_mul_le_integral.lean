-- Prove2me | solution 1 for GlobalTheory.UnitLemma.PrincipalLat.exists_mul_le_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:11:51.652629+00:00
-- url     : https://prove2.me/submissions/bacd9517-8a41-4454-85e1-01256c703368

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Theorems.Thm_GlobalTheory_UnitLemma_PrincipalLat_exists_mul_isIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PrincipalLat
variable {O E A : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
  [CommRing A] [Algebra E A] [Algebra O A] [IsScalarTower O E A] [Module.Finite E A]
variable (E)
include E
namespace GlobalTheory.UnitLemma.PrincipalLat
theorem _root_.solution (J : Submodule O A) (hJ : J.FG) :
    ∃ c : O, c ≠ 0 ∧ ∀ z ∈ J, IsIntegral O (algebraMap O A c * z) := by
  classical
  obtain ⟨s, rfl⟩ := hJ
  choose f hf0 hf using fun y : A => exists_mul_isIntegral (O := O) E y
  refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.2 fun y _ => hf0 y, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.mul_prod_erase s f hy, map_mul, mul_comm (algebraMap O A (f y)), mul_assoc]
    exact isIntegral_algebraMap.mul (hf y)
  | zero => rw [mul_zero]; exact isIntegral_zero
  | add x y _ _ hx hy => rw [mul_add]; exact hx.add hy
  | smul o x _ hx => rw [mul_smul_comm]; exact hx.smul o
end GlobalTheory.UnitLemma.PrincipalLat
