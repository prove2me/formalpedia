-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.one_le_detW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:00:05.348587+00:00
-- url     : https://prove2.me/submissions/e9cb1fa5-f693-407d-99bd-7ce7c9ddacd3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_OneLeDetW
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_det_one_add_sq_eq_prod_eigenvalues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
theorem _root_.solution : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → 1 ≤ detW b := by
  intro n b hb
  unfold detW
  rw [det_one_add_sq_eq_prod_eigenvalues n b hb, Complex.ofReal_re]
  have : ∀ i ∈ (Finset.univ : Finset (Fin n)), (1 : ℝ) ≤ 1 + hb.eigenvalues i ^ 2 := fun i _ => by
    nlinarith [sq_nonneg (hb.eigenvalues i)]
  calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) this
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
