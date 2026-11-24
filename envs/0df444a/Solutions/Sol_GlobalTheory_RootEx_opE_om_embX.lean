-- Prove2me | solution 1 for GlobalTheory.RootEx.opE_om_embX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:14:32.928818+00:00
-- url     : https://prove2.me/submissions/c686742a-45bc-4ea0-a308-b89df4e44114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_nabs_pos
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_nabs_inv
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_nabs_one
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_card_cols
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_card_rows
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_embX_val
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_det_embX
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_integral_left
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_integral_right
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_opE_const_mul
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory.RootEx.OpELevi
namespace GlobalTheory.RootEx
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), (∀ g : GL n k, opE ψ ν p (om μ 1 (embX c g) Φ) = ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) • om μ 1 g (opE ψ ν p Φ)) ∧ ∀ g : GL n' k, opE ψ ν p (om μ (embX (c + 1) g) 1 Φ) = ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 2) / 2 - p) : ℝ) : ℂ) • om μ g 1 (opE ψ ν p Φ) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p h1 h2 ψ ν _ μ Φ
  refine ⟨fun g => ?_, fun g => ?_⟩
  · funext x₀
    unfold om
    rw [opE_const_mul]
    simp only [← map_inv, embX_val, Units.val_one, Matrix.mul_one, det_embX, Pi.smul_apply,
      smul_eq_mul, map_one, nabs_one, Real.one_rpow, Complex.ofReal_one]
    erw [integral_left p ψ ν (g⁻¹).val (Matrix.GeneralLinearGroup.det g)⁻¹ (by rw [← map_inv]; rfl) Φ]
    have hp := nabs_pos (Matrix.GeneralLinearGroup.det g)
    set t := nabs k (Matrix.GeneralLinearGroup.det g) with ht
    have key : t ^ (-(Fintype.card (n' ⊕ Fin (c + 1)) : ℝ) / 2) *
        (t⁻¹ ^ Fintype.card {i : Fin (c + 1) // p < i.val + 1})⁻¹ =
        t ^ (((c : ℝ) + 1) / 2 - p) * t ^ (-(Fintype.card n' : ℝ) / 2) := by
      rw [inv_pow, inv_inv, ← Real.rpow_natCast, card_cols p h1 h2, ← Real.rpow_add hp,
        ← Real.rpow_add hp]
      congr 1
      simp only [Fintype.card_sum, Fintype.card_fin]
      push_cast; ring
    rw [nabs_inv, ← ht, Complex.real_smul]
    have key' := congrArg (fun r : ℝ => (r : ℂ)) key
    simp only [Complex.ofReal_mul] at key'
    linear_combination (((μ (Matrix.GeneralLinearGroup.det g⁻¹) : ℂˣ) : ℂ) *
      opE ψ ν p Φ ((g⁻¹).val * x₀)) * key'
  · funext x₀
    unfold om
    rw [opE_const_mul]
    simp only [inv_one, embX_val, Units.val_one, Matrix.one_mul, det_embX, Pi.smul_apply,
      smul_eq_mul, map_one, nabs_one, Real.one_rpow, Complex.ofReal_one]
    erw [integral_right p ψ ν g.val (Matrix.GeneralLinearGroup.det g) rfl Φ]
    have hp := nabs_pos (Matrix.GeneralLinearGroup.det g)
    set t := nabs k (Matrix.GeneralLinearGroup.det g) with ht
    have key : t ^ ((Fintype.card (n ⊕ Fin c) : ℝ) / 2) *
        (t ^ Fintype.card {l : Fin c // l.val + 1 < p})⁻¹ =
        t ^ (((c : ℝ) + 2) / 2 - p) * t ^ ((Fintype.card n : ℝ) / 2) := by
      rw [← Real.rpow_natCast, card_rows p h1 h2, ← Real.rpow_neg hp.le, ← Real.rpow_add hp,
        ← Real.rpow_add hp]
      congr 1
      simp only [Fintype.card_sum, Fintype.card_fin]
      push_cast; ring
    rw [Complex.real_smul]
    have key' := congrArg (fun r : ℝ => (r : ℂ)) key
    simp only [Complex.ofReal_mul] at key'
    linear_combination (((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      opE ψ ν p Φ (x₀ * g.val)) * key'
end GlobalTheory.RootEx
