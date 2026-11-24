-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwContraction.val_det_sub_prod_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:02:54.309379+00:00
-- url     : https://prove2.me/submissions/fc405b91-8671-4502-bd1b-056d648f5e28

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistedIwahoriContractionHolds
import Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_perm_eq_one_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Tf.Loc Matrix ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwContraction
variable {F : Type*} [Field F] [ValuativeRel F] {n : ℕ}
namespace GlobalTheory.CompanionTheory.TwContraction
theorem _root_.solution (M : Matrix (Fin n) (Fin n) F)
    (h0 : ∀ i l, valuation F (M i l) ≤ 1) (hl : ∀ i l, l < i → valuation F (M i l) < 1) :
    valuation F (M.det - ∏ i, M i i) < 1 := by
  classical
  rw [Matrix.det_apply', ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n)))]
  simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, Equiv.Perm.coe_one, id_eq, one_mul]
  rw [add_sub_cancel_left]
  refine Valuation.map_sum_lt _ one_ne_zero fun π hπ => ?_
  have hπ1 : π ≠ 1 := (Finset.mem_erase.mp hπ).1
  obtain ⟨i, hi⟩ : ∃ i, i < π i := by
    by_contra hcon
    exact hπ1 (perm_eq_one_of_le π fun i => not_lt.mp fun h => hcon ⟨i, h⟩)
  have hs : valuation F (((Equiv.Perm.sign π : ℤˣ) : ℤ) : F) ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  rw [map_mul, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul]
  have hrest : valuation F (∏ r ∈ Finset.univ.erase i, M (π r) r) ≤ 1 := by
    rw [map_prod]
    exact Finset.prod_le_one' fun r _ => h0 _ _
  calc _ ≤ 1 * (valuation F (M (π i) i) * 1) := mul_le_mul' hs (mul_le_mul' le_rfl hrest)
    _ < 1 := by simpa using hl _ _ hi
end GlobalTheory.CompanionTheory.TwContraction
