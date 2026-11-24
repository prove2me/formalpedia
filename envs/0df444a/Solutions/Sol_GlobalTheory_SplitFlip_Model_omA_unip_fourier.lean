-- Prove2me | solution 1 for GlobalTheory.SplitFlip.Model.omA_unip_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:06:49.082182+00:00
-- url     : https://prove2.me/submissions/92c1d7d7-7a2d-4f17-baf6-993023b43656

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OmAUnipFourierInv
import Theorems.Thm_GlobalTheory_SplitFlip_Model_gdet_unip
import Theorems.Thm_GlobalTheory_SplitFlip_Model_pair_one

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
theorem _root_.solution (ψ : AddChar k Circle) (m : Measure k) (ν β : kˣ →* ℂˣ) (b : Matrix D₁ D₂ k)
    (Φ : Matrix A (D₁ ⊕ D₂) k → ℂ) :
    omA ν β 1 (unip b) (fourierInt ψ m (Assignment.one.block D₁ D₂) Φ) =
      fourierInt ψ m (Assignment.one.block D₁ D₂)
        fun T => (ψ (-trace (T.toCols₁ * b * T.toCols₂ᵀ)) : ℂ) * Φ T := by
  funext Y
  simp only [omA, gdet_unip, map_one, inv_one, Units.val_one, apow_one, one_mul, Matrix.one_mul, fourierInt]
  congr 1
  funext T
  obtain ⟨M, hM⟩ : ∃ M : Matrix (D₁ ⊕ D₂) (D₁ ⊕ D₂) k, M = fromBlocks 1 0 (-bᵀ) 1 := ⟨_, rfl⟩
  have h0 : (invT (unip b)).val = M := by
    rw [hM]
    show (fromBlocks 1 (-b) 0 1)ᵀ = _
    simp [fromBlocks_transpose]
  rw [h0]
  have h1 : setCols _ (Y * M) T = setCols _ Y T := by
    ext i (j | j) <;> simp [hM, setCols, Assignment.block, Matrix.mul_apply, one_apply]
  have h2 : pairCols _ (Y * M) T =
      -trace ((setCols _ Y T).toCols₁ * b * (setCols _ Y T).toCols₂ᵀ) + pairCols _ Y T := by
    rw [pair_one, pair_one, trace, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [diag_apply, Matrix.mul_assoc, Matrix.mul_apply, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hM, setCols, Assignment.block, Matrix.mul_apply, one_apply, toCols₁, toCols₂, mul_comm (b _ _)]
    ring
  rw [h1, h2, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring
end GlobalTheory.SplitFlip.Model
