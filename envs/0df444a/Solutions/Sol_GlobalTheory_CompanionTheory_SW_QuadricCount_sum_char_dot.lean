-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadricCount.sum_char_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:30:52.867802+00:00
-- url     : https://prove2.me/submissions/f88fa6ca-d827-45f9-be92-40097c5a5442

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadricCount
open ComplexConjugate
variable {k : Type} [Field k] [Fintype k] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.QuadricCount
theorem _root_.solution (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {w : ι → k} (hw : w ≠ 0) :
    ∑ y : ι → k, ψ (y ⬝ᵥ w) = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  obtain ⟨c, hc⟩ := (AddChar.ne_one_iff).mp hψ
  have hi' : w i ≠ 0 := hi
  have he : (Pi.single i (c / w i) : ι → k) ⬝ᵥ w = c := by
    rw [single_dotProduct]
    field_simp
  have hS : ψ c * ∑ y : ι → k, ψ (y ⬝ᵥ w) = ∑ y : ι → k, ψ (y ⬝ᵥ w) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addRight (Pi.single i (c / w i) : ι → k)) _ _ ?_
    intro x
    rw [Equiv.coe_addRight, add_dotProduct, he, AddChar.map_add_eq_mul, mul_comm]
  have h0 : (ψ c - 1) * ∑ y : ι → k, ψ (y ⬝ᵥ w) = 0 := by
    rw [sub_mul, hS, one_mul, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc)
end GlobalTheory.CompanionTheory.SW.QuadricCount
