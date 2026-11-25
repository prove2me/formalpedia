-- Prove2me | solution 1 for GlobalTheory.WachTie.Laur.co_smul_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:08.258802+00:00
-- url     : https://prove2.me/submissions/69688506-6baf-46f3-b2c2-7c2e9c191859

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_GradedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfSumSmul
import Theorems.Thm_GlobalTheory_WachTie_Laur_co_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open PowerSeries GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
namespace GlobalTheory.WachTie
namespace Laur
variable {L M M' : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L M']
private theorem co_smul_add_eq_coeff_smul_co (f : L⟦X⟧) (x : Laur L M) (m : ℤ) (n : ℕ)
    (hf : ∀ j < n, PowerSeries.coeff j f = 0) (hx : ∀ k < m, co x k = 0) :
    co (f • x) (m + n) = PowerSeries.coeff n f • co x m := by
  rw [co_smul]
  show ∑ᶠ j : ℕ, PowerSeries.coeff j f • co x (m + n - j) = _
  rw [finsum_eq_single _ n]
  · simp
  · intro j hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hf j h, zero_smul]
    · rw [hx (m + n - j) (by omega), smul_zero]
end Laur
end GlobalTheory.WachTie
end
end

set_option autoImplicit false
noncomputable section
open PowerSeries GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
open GlobalTheory GlobalTheory.WachTie
open GlobalTheory.WachTie.Laur
variable {L M M' : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L M']
namespace GlobalTheory.WachTie.Laur
theorem _root_.solution (f : L⟦X⟧) (x : Laur L M) (m : ℤ) (hx : ∀ k < m, co x k = 0) :
    (∀ k < m, co (f • x) k = 0) ∧ co (f • x) m = constantCoeff f • co x m := by
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [co_smul]
    show ∑ᶠ j : ℕ, PowerSeries.coeff j f • co x (k - j) = 0
    exact (finsum_congr fun j => by rw [hx (k - j) (by omega), smul_zero]).trans finsum_zero
  · have e := co_smul_add_eq_coeff_smul_co f x m 0 (fun j hj => absurd hj (Nat.not_lt_zero j)) hx
    simpa using e
end GlobalTheory.WachTie.Laur
