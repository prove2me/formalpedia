-- Prove2me | solution 1 for GlobalTheory.SplitWeil.Model.om_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:58.974607+00:00
-- url     : https://prove2.me/submissions/e8671e1c-7131-40b0-8a3b-d14990b03c19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
omit [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitWeil.Model
theorem _root_.solution {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) {Φ : Matrix b a k → ℂ} (hΦ : Φ ∈ SB (Matrix b a k)) :
    om μ g h Φ ∈ SB (Matrix b a k) := by
  let e : Matrix b a k ≃ₜ Matrix b a k :=
    { toFun := fun x => (h⁻¹ : GL b k).val * x * g.val
      invFun := fun x => h.val * x * (g⁻¹ : GL a k).val
      left_inv := fun x => by
        simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      right_inv := fun x => by
        simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  have h1 : (Φ ∘ e) ∈ SB (Matrix b a k) :=
    ⟨hΦ.1.comp_continuous e.continuous, hΦ.2.comp_homeomorph e⟩
  exact (SB (Matrix b a k)).smul_mem _ h1
end GlobalTheory.SplitWeil.Model
