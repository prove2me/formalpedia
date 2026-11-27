-- Prove2me | solution 1 for GlobalTheory.exists_isAlgClosed_addValuation_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:18.311395+00:00
-- url     : https://prove2.me/submissions/83683dc8-f3c8-4423-b8a8-41d068d14ccb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsNnrealValuationOfAddValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsIsAlgClosedAddValuationIsAdicComplete
import Theorems.Thm_GlobalTheory_expNegTop_inj_of_eq
import Theorems.Thm_GlobalTheory_isNonarchimedean_expNegAbsoluteValue
import Theorems.Thm_GlobalTheory_exists_norm_eq_of_completion
import Theorems.Thm_GlobalTheory_exists_addValuation_expNegTop_eq_nnnorm
import Theorems.Thm_GlobalTheory_isAlgClosed_of_denseRange


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped NNReal
namespace GlobalTheory
theorem _root_.solution :
    ∀ (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [CharZero F₀] (v₀ : AddValuation F₀ (WithTop ℚ))
      (p : ℕ), p.Prime → 0 < v₀ (p : F₀) →
      ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : CharZero F) (e : F₀ →+* F)
        (v : AddValuation F (WithTop ℚ)), (∀ x, v (e x) = v₀ x) ∧
        IsAdicComplete (Ideal.span {(p : ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v)})
          (ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v) := by
  intro F₀ _ _ _ v₀ p hp hv
  let w := expNegAbsoluteValue v₀
  have hw : ∀ x, w x = (expNegTop (v₀ x) : ℝ) := fun _ => rfl
  have hp1 : w (p : F₀) < 1 := by
    rw [hw, ← NNReal.coe_one, NNReal.coe_lt_coe, ← expNegTop_zero, ← not_le, expNegTop_le_iff]
    exact not_le.2 hv
  have hp0 : 0 < w (p : F₀) := w.pos (Nat.cast_ne_zero.2 hp.ne_zero)
  letI : NontriviallyNormedField (WithAbs w) :=
    { (inferInstance : NormedField (WithAbs w)) with
      non_trivial := ⟨(WithAbs.toAbs w (p : F₀))⁻¹, by
        rw [norm_inv]
        change 1 < (w (p : F₀))⁻¹
        exact (one_lt_inv₀ hp0).2 hp1⟩ }
  haveI : IsUltrametricDist (WithAbs w) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y =>
      isNonarchimedean_expNegAbsoluteValue v₀ x.ofAbs y.ofAbs
  haveI : IsAlgClosed (WithAbs w) := IsAlgClosed.of_ringEquiv F₀ _ (WithAbs.equiv w).symm
  let C := UniformSpace.Completion (WithAbs w)
  letI : NontriviallyNormedField C := completionNontriviallyNormedField (WithAbs w)
  haveI : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra (WithAbs w)
  haveI : IsAlgClosed C :=
    isAlgClosed_of_denseRange (K := WithAbs w) UniformSpace.Completion.denseRange_coe
  let e : F₀ →+* C := (algebraMap (WithAbs w) C).comp (WithAbs.equiv w).symm.toRingHom
  have he : ∀ x, ‖e x‖₊ = expNegTop (v₀ x) := fun x =>
    NNReal.coe_injective (UniformSpace.Completion.norm_coe (WithAbs.toAbs w x))
  haveI : CharZero C := charZero_of_injective_ringHom e.injective
  obtain ⟨v, hvC⟩ := exists_addValuation_expNegTop_eq_nnnorm (C := C) fun x => by
    obtain ⟨y, hy⟩ := exists_norm_eq_of_completion x
    exact ⟨v₀ y.ofAbs, NNReal.coe_injective hy.symm⟩
  have hmem : ∀ x : C, NormedField.valuation x ≤ 1 ↔ 0 ≤ v x := fun x => by
    rw [NormedField.valuation_apply, ← hvC, ← expNegTop_zero, expNegTop_le_iff]
  have hO : (NormedField.valuation (K := C)).Integers (ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v) :=
    ⟨Subtype.val_injective, fun x => (hmem _).2 x.2, fun r hr => ⟨⟨r, (hmem r).1 hr⟩, rfl⟩⟩
  refine ⟨C, inferInstance, inferInstance, inferInstance, e, v,
    fun x => expNegTop_inj_of_eq (by rw [hvC, he]),
    NormIntegers.isAdicComplete_span_singleton hO ?_⟩
  rw [map_natCast, ← map_natCast e, ← coe_nnnorm, he, ← hw]
  exact hp1
end GlobalTheory
