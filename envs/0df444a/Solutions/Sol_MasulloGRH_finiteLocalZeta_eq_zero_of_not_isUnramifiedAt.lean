-- Prove2me | solution 1 for MasulloGRH.finiteLocalZeta_eq_zero_of_not_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T18:50:19.788506+00:00
-- url     : https://prove2.me/submissions/40402ad5-d562-4c3b-8cb2-b66b17d2ae72

import Mathlib
import Definitions.Def_MasulloGRH_HeckeLFunction
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures
import Theorems.Thm_MasulloGRH_finiteLocalMulTamagawa_isHaarMeasure_and_units

open MeasureTheory NumberField IsDedekindDomain MasulloGRH
open scoped MasulloGRH

set_option autoImplicit false
set_option maxHeartbeats 600000

private theorem localComponent_mul {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F)
    (v : HeightOneSpectrum (𝓞 F)) (x y : (v.adicCompletion F)ˣ) :
    χ.localComponent v (x * y) = χ.localComponent v x * χ.localComponent v y := by
  have hFinite : finiteIdeleSingle v (x * y) = finiteIdeleSingle v x * finiteIdeleSingle v y := by
    simp [finiteIdeleSingle, RestrictedProduct.mulSingle_mul] <;> rfl
  have hSingle : ideleSingle v (x * y) = ideleSingle v x * ideleSingle v y := by
    let e : (InfiniteAdeleRing F)ˣ × (FiniteAdeleRing (𝓞 F) F)ˣ ≃*
        (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)ˣ := MulEquiv.prodUnits.symm
    change e (1, finiteIdeleSingle v (x * y)) = e (1, finiteIdeleSingle v x) *
      e (1, finiteIdeleSingle v y)
    rw [hFinite, ← map_mul e, Prod.mk_mul_mk, one_mul]
  let π := QuotientGroup.mk' (principalIdeles F)
  change (χ (π (ideleSingle v (x * y))) : ℂ) =
    (χ (π (ideleSingle v x)) : ℂ) * (χ (π (ideleSingle v y)) : ℂ)
  rw [hSingle, map_mul π, map_mul χ, Circle.coe_mul]

theorem solution (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F)
    (v : HeightOneSpectrum (𝓞 F)) (hχ : ¬ χ.IsUnramifiedAt v) (f : v.adicCompletion F → ℂ)
    (hf : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
      ∀ x : v.adicCompletion F, f (u * x) = f x) (s : ℂ) :
    ∫ x : (v.adicCompletion F)ˣ, f (x : v.adicCompletion F) * χ.localComponent v x *
      ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ s ∂(finiteLocalMulTamagawa F v) = 0 := by
  unfold HeckeCharacter.IsUnramifiedAt at hχ
  push Not at hχ
  obtain ⟨u, hu, hχu⟩ := hχ
  have hNorm : ‖(u : v.adicCompletion F)‖ = 1 := by
    rw [FinitePlace.norm_def, hu, map_one, NNReal.coe_one]
  let w (x : (v.adicCompletion F)ˣ) := f (x : v.adicCompletion F) * χ.localComponent v x *
    ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ s
  have hTranslate (x : (v.adicCompletion F)ˣ) : w (u * x) = χ.localComponent v u * w x := by
    simp only [w, Units.val_mul, hf u hu, localComponent_mul, norm_mul, hNorm, one_mul]
    ring
  have : (finiteLocalMulTamagawa F v).IsHaarMeasure :=
    (finiteLocalMulTamagawa_isHaarMeasure_and_units F v).1
  have hIntegral := integral_mul_left_eq_self (μ := finiteLocalMulTamagawa F v) w u
  simp_rw [hTranslate, integral_const_mul] at hIntegral
  change (∫ x, w x ∂(finiteLocalMulTamagawa F v)) = 0
  by_contra hne
  exact hχu (mul_right_cancel₀ hne (hIntegral.trans (one_mul _).symm))
