-- Prove2me | solution 1 for GlobalTheory.Cyc.descent_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:24:51.378457+00:00
-- url     : https://prove2.me/submissions/2f3c657e-b1d7-4d1a-b3b2-765cfe801e7e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantsOfSubgroup
import Theorems.Thm_GlobalTheory_Cyc_descent_act_chiC
import Theorems.Thm_GlobalTheory_Cyc_descent_chiC_mul
import Theorems.Thm_GlobalTheory_Cyc_descent_chiC_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc
theorem _root_.solution {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (hact : IsActC act)
    (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (H : Subgroup (GQ l)) (y : PadicComplex l)
    (hy : ∀ g ∈ H, chiC χ i g * act g y = y) :
    ∃ F : GQ l ⧸ H → PadicComplex l, F ((1 : GQ l) : GQ l ⧸ H) = y ∧
      (∀ q, F q = 0 → y = 0) ∧ ∀ (g : GQ l) q, chiC χ i g * act g (F q) = F (g • q) := by
  have key : ∀ g σ : GQ l, chiC χ i (g * σ) * act (g * σ) y
      = chiC χ i g * act g (chiC χ i σ * act σ y) := by
    intro g σ
    rw [descent_chiC_mul, map_mul act, map_mul (act g), descent_act_chiC hact, mul_assoc]
    rfl
  refine ⟨fun q => Quotient.liftOn' q (fun σ => chiC χ i σ * act σ y) ?_, ?_, ?_, ?_⟩
  · intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have := key a (a⁻¹ * b)
    rw [hy _ hab, mul_inv_cancel_left] at this
    exact this.symm
  · change chiC χ i 1 * act 1 y = y
    rw [descent_chiC_one, map_one, one_mul]
    rfl
  · intro q
    induction q using QuotientGroup.induction_on with
    | H σ =>
      intro h
      change chiC χ i σ * act σ y = 0 at h
      have := key σ⁻¹ σ
      rw [h, map_zero, mul_zero, inv_mul_cancel, descent_chiC_one, map_one, one_mul] at this
      exact this
  · intro g q
    induction q using QuotientGroup.induction_on with
    | H σ => exact (key g σ).symm
end GlobalTheory.Cyc
