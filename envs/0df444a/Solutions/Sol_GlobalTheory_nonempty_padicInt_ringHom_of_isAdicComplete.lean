-- Prove2me | solution 1 for GlobalTheory.nonempty_padicInt_ringHom_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:34:09.245471+00:00
-- url     : https://prove2.me/submissions/77c51cb9-3ab7-4b9c-8d4b-aa7248f3060d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NonemptyPadicIntRingHomOfIsAdicComplete
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_GlobalTheory_IsPolynomialFunction_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X



set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open IsLocalRing
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {V : Type*} [CommRing V] (I : Ideal V)
    [IsAdicComplete I V] (p : ℕ) [Fact p.Prime] (hp : (p : V) ∈ I) : Nonempty (ℤ_[p] →+* V) := by
  have hzero : ∀ n : ℕ, ∀ a ∈ Ideal.span {((p ^ n : ℕ) : ℤ)}, (Int.castRingHom (V ⧸ I ^ n)) a = 0 := by
    intro n a ha
    obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have h : ((p ^ n : ℕ) : V ⧸ I ^ n) = 0 := by
      rw [show ((p ^ n : ℕ) : V ⧸ I ^ n) = Ideal.Quotient.mk _ ((p : V) ^ n) by simp,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow hp n
    rw [map_mul, map_natCast, h, mul_zero]
  let g : (n : ℕ) → ZMod (p ^ n) →+* V ⧸ I ^ n := fun n =>
    (Ideal.Quotient.lift _ (Int.castRingHom _) (hzero n)).comp
      (Int.quotientSpanNatEquivZMod (p ^ n)).symm.toRingHom
  refine ⟨IsAdicComplete.liftRingHom I (fun n => (g n).comp (PadicInt.toZModPow n)) ?_⟩
  intro m n hle
  have hg : (Ideal.Quotient.factorPow I hle).comp (g n) =
      (g m).comp (ZMod.castHom (pow_dvd_pow p hle) _) := Subsingleton.elim _ _
  ext x
  have hx := RingHom.congr_fun hg (PadicInt.toZModPow n x)
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle]
  exact hx
end _root_.GlobalTheory
end GlobalTheory
