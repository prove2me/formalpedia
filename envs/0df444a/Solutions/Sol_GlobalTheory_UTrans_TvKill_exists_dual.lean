-- Prove2me | solution 1 for GlobalTheory.UTrans.TvKill.exists_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:32.986911+00:00
-- url     : https://prove2.me/submissions/671e3ec6-f18c-4988-845c-00794a9018b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryCharacterKillsUnitaryTransvections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.TvKill
open GlobalTheory.UTrans GlobalTheory.UTrans.Calc
variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.UTrans.TvKill
theorem _root_.solution (hG : IsHerm σ G) {x : Fin n → E} (hx : x ≠ 0) : ∃ y, hf σ G x y = 1 := by
  have h1 : Matrix.vecMul x G ≠ 0 := fun h => hx (Matrix.eq_zero_of_vecMul_eq_zero hG.det_ne h)
  obtain ⟨b, hb⟩ := Function.ne_iff.mp h1
  refine ⟨Pi.single b (σ (Matrix.vecMul x G b)⁻¹), ?_⟩
  have : hf σ G x (Pi.single b (σ (Matrix.vecMul x G b)⁻¹)) =
      Matrix.vecMul x G b * (Matrix.vecMul x G b)⁻¹ := by
    simp only [hf, Pi.single_apply, apply_ite σ, map_zero, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hG.invol, ← Finset.sum_mul]
    rfl
  rw [this, mul_inv_cancel₀ hb]
end GlobalTheory.UTrans.TvKill
