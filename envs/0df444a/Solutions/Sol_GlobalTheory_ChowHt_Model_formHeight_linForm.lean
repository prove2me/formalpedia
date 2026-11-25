-- Prove2me | solution 1 for GlobalTheory.ChowHt.Model.formHeight_linForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:40:20.349212+00:00
-- url     : https://prove2.me/submissions/48e3afb4-7b24-4e0d-9c3e-8f10a45a6249

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BlockSphereMeanLinForm
import Theorems.Thm_GlobalTheory_ChowHt_Model_linSubst_linForm
import Theorems.Thm_GlobalTheory_ChowHt_Model_gaussAbs_linForm
import Theorems.Thm_GlobalTheory_ChowHt_Model_blockSphereMean_linForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial NumberField
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.ChowHt.Model
namespace GlobalTheory.ChowHt.Model
theorem _root_.solution {F : Type} [Field F] [NumberField F] {N n : ℕ}
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ σ, (A σ).det ≠ 0) (y : Fin N → F) (hy : y ≠ 0) :
    formHeight 1 w A (linForm y) = pointHeight w A y := by
  unfold formHeight pointHeight
  congr 2
  · simp [linSubst_linForm, gaussAbs_linForm]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    have hm : MvPolynomial.map σ (linForm y) = linForm (fun j => σ (y j)) := by
      simp [linForm]
    have hσ : σ.comp (algebraMap F F) = σ := by ext; simp
    rw [hm, linSubst_linForm, blockSphereMean_linForm, hσ]
    · simp
    · intro h
      apply hy
      have : Matrix.vecMul (fun j => σ (y j)) (A σ) = 0 := by
        funext k
        have := congrFun h k
        simpa [Matrix.vecMul, dotProduct, mul_comm] using this
      have h2 := Matrix.eq_zero_of_vecMul_eq_zero (hA σ) this
      funext j
      simpa using congrFun h2 j
end GlobalTheory.ChowHt.Model
