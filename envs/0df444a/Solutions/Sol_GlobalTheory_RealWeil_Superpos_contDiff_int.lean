-- Prove2me | solution 1 for GlobalTheory.RealWeil.Superpos.contDiff_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:18:59.708577+00:00
-- url     : https://prove2.me/submissions/002ed8fb-25e6-480d-927b-c15b804b062b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeisenbergSmoothRapidSuperpositionTranslates
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_mom_dh
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_hasFDerivAt_int
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_fderiv_int_apply
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped ContDiff Real
noncomputable section
open GlobalTheory GlobalTheory.RealWeil
open GlobalTheory.RealWeil.Superpos
variable {V Y B : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
variable {om : V →L[ℝ] V →L[ℝ] ℝ} {ρ : V → B →L[ℂ] B} {ι : Y →L[ℝ] V} {ν : Measure Y}
namespace GlobalTheory.RealWeil.Superpos
theorem _root_.solution (hρ : IsHeis (fun x y => om x y) ρ) (n : ℕ) : ∀ h : Y → ℂ, Mom ν h → ∀ g : V → B,
    ContDiff ℝ ∞ g → ContDiff ℝ n fun v => ∫ y, itg om ρ ι h g v y ∂ν := by
  induction n with
  | zero =>
    intro h hh g hg
    exact contDiff_zero.2 (Differentiable.continuous fun v => (hasFDerivAt_int hρ hh hg v).differentiableAt)
  | succ n ih =>
    intro h hh g hg
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun v => (hasFDerivAt_int hρ hh hg v).differentiableAt, by simp, fun z => ?_⟩
    simp only [fderiv_int_apply hρ hh hg]
    have hg' : ContDiff ℝ ∞ fun w => fderiv ℝ g w z :=
      (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact (ih _ (mom_dh hh z) g hg).add (ih h hh _ hg')
end GlobalTheory.RealWeil.Superpos
