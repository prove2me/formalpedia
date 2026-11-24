-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleCharLocal.exists_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:26:46.746916+00:00
-- url     : https://prove2.me/submissions/e448f7ef-1348-44bb-8a25-58660fb444a8

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct RestrictedProduct nonZeroDivisors
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleCharLocal
namespace GlobalTheory.CompanionTheory.AdeleCharLocal
theorem _root_.solution (g : ℝ → ℂ) (hc : Continuous g) (hn : ∀ t, ‖g t‖ = 1) (h0 : g 0 = 1)
    (hadd : ∀ s t, g (s + t) = g s * g t) :
    ∃ c : ℝ, ∀ t : ℝ, g t = Complex.exp (2 * Real.pi * Complex.I * ((c * t : ℝ) : ℂ)) := by
  have hm : ∀ a, g a ∈ Submonoid.unitSphere ℂ := fun a => by simpa [Submonoid.unitSphere] using hn a
  let χ : C(ℝ, Circle) := ⟨fun a => ⟨g a, hm a⟩, hc.subtype_mk hm⟩
  have hχ : ∀ s t, χ (s + t) = χ s * χ t := fun s t => Subtype.ext (hadd s t)
  obtain ⟨L, ⟨hL0, hL⟩, hu⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts χ 0 0
    (by rw [Circle.exp_zero]; exact Subtype.ext h0.symm)
  have hL' : ∀ t, Circle.exp (L t) = χ t := congrFun hL
  have hLa : ∀ s t, L (s + t) = L s + L t := fun s t => by
    have := hu ⟨fun t => L (s + t) - L s, by fun_prop⟩ ⟨by simp, by
      funext t
      show Circle.exp (L (s + t) - L s) = χ t
      rw [Circle.exp_sub, hL', hL', hχ, mul_div_cancel_left]⟩
    have h2 : L (s + t) - L s = L t := DFunLike.congr_fun this t
    linarith
  let l : ℝ →+ ℝ := AddMonoidHom.mk' L hLa
  refine ⟨L 1 / (2 * Real.pi), fun t => ?_⟩
  have h3 : L t = t * L 1 := by
    have := map_real_smul l L.continuous t 1
    simpa [l] using this
  have h4 : g t = (Circle.exp (L t) : ℂ) := by rw [hL']; rfl
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [h4, Circle.coe_exp, h3]
  congr 1
  push_cast
  field_simp
end GlobalTheory.CompanionTheory.AdeleCharLocal
