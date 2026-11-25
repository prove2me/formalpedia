-- Prove2me | solution 1 for GlobalTheory.RootEx.Model.exists_isPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:07:59.025733+00:00
-- url     : https://prove2.me/submissions/c986ae8a-36ce-4c65-9a62-0028ec23985f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Theorems.Thm_GlobalTheory_RootEx_Model_conj_mem
import Theorems.Thm_GlobalTheory_RootEx_Model_simpleSum_conj
import Theorems.Thm_GlobalTheory_RootEx_Model_chi_mul
import Theorems.Thm_GlobalTheory_RootEx_Model_reg_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootEx.Model
theorem _root_.solution (ψ : AddChar k Circle) (p : ℕ) :
    ∃ b : (GL n k →₀ ℂ) →ₗ[ℂ] (GL (n ⊕ Fin c) k →₀ ℂ) →ₗ[ℂ] ℂ,
      IsPos ψ p (reg (GL n k))
        (reg (GL (n ⊕ Fin c) k)) b ∧ b ≠ 0 := by
  let w : GL n k → ℂ := fun g =>
    ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ)
  have hw : ∀ g g', w (g * g') = w g * w g' := by
    intro g g'
    simp only [w, nabs, map_mul, NNReal.coe_mul]
    rw [Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]; push_cast; rfl
  let b : (GL n k →₀ ℂ) →ₗ[ℂ] (GL (n ⊕ Fin c) k →₀ ℂ) →ₗ[ℂ] ℂ :=
    Finsupp.linearCombination ℂ fun g => Finsupp.linearCombination ℂ fun h => w g * chi ψ p ((embX c g)⁻¹ * h)
  have hb : ∀ g h x y, b (Finsupp.single g x) (Finsupp.single h y) = x * (y * (w g * chi ψ p ((embX c g)⁻¹ * h))) := by
    intro g h x y; simp [b]
  refine ⟨b, ⟨?_, ?_⟩, ?_⟩
  · intro φ u hu v
    induction φ using Finsupp.induction_linear with
    | zero => simp
    | add a a' h1 h2 => simp only [map_add, LinearMap.add_apply, h1, h2]; ring
    | single g x =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add a a' h1 h2 => simp only [map_add, h1, h2]; ring
      | single h y =>
        rw [reg_single, hb, hb,
          show (embX c g)⁻¹ * (u * h) = ((embX c g)⁻¹ * u * embX c g) * ((embX c g)⁻¹ * h) by group,
          chi_mul ψ p (conj_mem hu g), simpleSum_conj]
        ring
  · intro g' φ v
    induction φ using Finsupp.induction_linear with
    | zero => simp
    | add a a' h1 h2 => simp only [map_add, LinearMap.add_apply, h1, h2]; ring
    | single g x =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add a a' h1 h2 => simp only [map_add, h1, h2]; ring
      | single h y =>
        rw [reg_single, reg_single, hb, hb,
          hw, show (embX c (g' * g))⁻¹ * (embX c g' * h) = (embX c g)⁻¹ * h by rw [map_mul]; group]
        simp only [w]; ring
  · intro h0
    have := hb 1 1 1 1
    rw [h0] at this
    simp [w, nabs, chi, one_mem] at this
    exact Circle.coe_ne_zero _ this.symm
end GlobalTheory.RootEx.Model
