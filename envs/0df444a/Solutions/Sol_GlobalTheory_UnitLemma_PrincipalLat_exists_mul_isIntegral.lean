-- Prove2me | solution 1 for GlobalTheory.UnitLemma.PrincipalLat.exists_mul_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:35.293008+00:00
-- url     : https://prove2.me/submissions/47d502d3-b6fa-4241-93ee-d8f82c3c27ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra

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
theorem _root_.solution (y : A) : ∃ c : O, c ≠ 0 ∧ IsIntegral O (algebraMap O A c * y) := by
  have : Algebra.IsAlgebraic O A :=
    (IsFractionRing.comap_isAlgebraic_iff (A := O) (K := E) (C := A)).mpr inferInstance
  obtain ⟨c, hc, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := O) y).exists_integral_multiple
  exact ⟨c, hc, by rwa [Algebra.smul_def] at h⟩
end GlobalTheory.UnitLemma.PrincipalLat
