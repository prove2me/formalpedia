-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSNormLt.normLt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:16:28.07368+00:00
-- url     : https://prove2.me/submissions/da03ba27-aa19-42c2-91ec-7aac9dacbb61

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_normSq_le
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_pair_lt
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_wtA_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_tt_anti
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_tt_of
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_abs_tt
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_rho_eq
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSNormLt
open CompanionTheory.D.DSIC
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSNormLt
theorem _root_.solution : CompanionTheory.D.DSIC.NormLt := by
  intro n ε lam hl A hA
  obtain ⟨⟨⟨c, d⟩, h⟩, hi⟩ : ∃ i : NC ε, ¬ (i ∈ A ↔ i ∈ A1 ε) := by
    by_contra hc
    push Not at hc
    exact hA (Finset.ext fun i => by simpa using hc i)
  have hcd : c ≠ d := by rintro rfl; simp [h.1] at h
  have hne : tt A c d = - sig c d := by rw [tt_of A h, if_neg hi]
  have i1 := pair_lt (tt A) (tt_anti A) (abs_tt A) hl c d hcd hne
  have i2 := normSq_le (tt A) (tt_anti A) (abs_tt A)
  have f1 : ∀ a, (gam ε lam - wtA A + (2 : ℝ) • PI.UpqRep.rhoC ε) a = lam a + (∑ b, tt A a b) / 2 := fun a => by
    have := rho_eq ε a
    simp only [gam, PI.UpqRep.lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, wtA_eq, tt,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_sub_distrib (f := fun b => ind (A1 ε) a b - ind (A1 ε) b a)]
    linarith
  have f2 : ∀ a, (PI.UpqRep.lowK ε lam + (2 : ℝ) • PI.UpqRep.rhoC ε) a = lam a + (∑ b, sig a b) / 2 := fun a => by
    have := rho_eq ε a
    simp only [PI.UpqRep.lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have ex : ∀ y : Fin n → ℝ, ∑ a, (lam a + y a) * (lam a + y a) =
      ∑ a, lam a ^ 2 + 2 * ∑ a, lam a * y a + ∑ a, y a ^ 2 := fun y => by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  unfold PI.UpqRep.vNormSq PI.UpqRep.nsq PI.UpqRep.dot
  simp only [f1, f2]
  rw [ex, ex]
  linarith
end GlobalTheory.CompanionTheory.DSNormLt
