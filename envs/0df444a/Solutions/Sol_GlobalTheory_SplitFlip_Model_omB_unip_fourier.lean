-- Prove2me | solution 1 for GlobalTheory.SplitFlip.Model.omB_unip_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:12:33.884801+00:00
-- url     : https://prove2.me/submissions/483cdf7c-cbcd-43c1-be60-dc53cb66dcd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OmAUnipFourierInv
import Theorems.Thm_GlobalTheory_SplitFlip_Model_gdet_unip
import Theorems.Thm_GlobalTheory_SplitFlip_Model_pair_two

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
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Model
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D₁ D₂ : Type*} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitFlip.Model
theorem _root_.solution (ψ : AddChar k Circle) (m : Measure k) (ν α : kˣ →* ℂˣ) (b : Matrix D₁ D₂ k)
    (Φ : Matrix A (D₁ ⊕ D₂) k → ℂ) :
    omB ν α 1 (unip b) (fourierInt ψ m (Assignment.two.block D₁ D₂) Φ) =
      fourierInt ψ m (Assignment.two.block D₁ D₂)
        fun T => (ψ (trace (T.toCols₁ * b * T.toCols₂ᵀ)) : ℂ) * Φ T := by
  funext Y
  simp only [omB, gdet_unip, map_one, Units.val_one, apow_one, one_mul, transpose_one, Matrix.one_mul, fourierInt]
  congr 1
  funext T
  have h1 : setCols _ (Y * (unip b).val) T = setCols _ Y T := by
    ext i (j | j) <;> simp [setCols, Assignment.block, unip, Matrix.mul_apply, one_apply]
  have h2 : pairCols _ (Y * (unip b).val) T = trace ((setCols _ Y T).toCols₁ * b * (setCols _ Y T).toCols₂ᵀ)
      + pairCols _ Y T := by
    rw [pair_two, pair_two, trace, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [diag_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [setCols, Assignment.block, unip, Matrix.mul_apply, one_apply, toCols₁, toCols₂]
    ring
  rw [h1, h2, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring
end GlobalTheory.SplitFlip.Model
