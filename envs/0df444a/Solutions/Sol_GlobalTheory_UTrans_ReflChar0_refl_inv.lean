-- Prove2me | solution 1 for GlobalTheory.UTrans.ReflChar0.refl_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:30.000805+00:00
-- url     : https://prove2.me/submissions/15696271-cf95-43bd-b571-9db831362c17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryGeneratedByQuasiReflectionsAndWitt
import Theorems.Thm_GlobalTheory_UTrans_Calc_tv_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.ReflChar0
open GlobalTheory.UTrans.Calc
variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.UTrans.ReflChar0
theorem _root_.solution {x : Fin n → E} (hx : hf σ G x x ≠ 0) {u : E} (hu : u * σ u = 1) :
    tv σ G x ((σ u - 1) / hf σ G x x) * tv σ G x ((u - 1) / hf σ G x x) = 1 := by
  rw [tv_mul]
  have : (σ u - 1) / hf σ G x x + (u - 1) / hf σ G x x +
      (σ u - 1) / hf σ G x x * ((u - 1) / hf σ G x x) * hf σ G x x = 0 := by
    field_simp
    linear_combination hu
  rw [this]
  ext a b
  simp [tv]
end GlobalTheory.UTrans.ReflChar0
