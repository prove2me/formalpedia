-- Prove2me | solution 1 for GlobalTheory.FrameBiextId.ext_of_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:47:51.163369+00:00
-- url     : https://prove2.me/submissions/db9b7653-1a8a-41ab-917f-31c7ce5e0a46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FormalPointSubstitutionSeriesValueAtTwoPoints
import Theorems.Thm_GlobalTheory_FrameBiextId_sq_gen
import Theorems.Thm_GlobalTheory_FrameBiextId_formalPointSubstitutionSeries_valueAtTwoPoints
import Theorems.Thm_GlobalTheory_FrameBiextId_formalPointSubstitutionSeries_valueAtThreePoints
import Theorems.Thm_GlobalTheory_FrameBiextId_sq_ac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FrameBiextId.sq_gen
attribute [local simp] GlobalTheory.FrameBiextId.formalPointSubstitutionSeries_valueAtTwoPoints
attribute [local simp] GlobalTheory.FrameBiextId.formalPointSubstitutionSeries_valueAtThreePoints
attribute [local simp] GlobalTheory.FrameBiextId.sq_ac

set_option autoImplicit false
noncomputable section
open MvPowerSeries
open GlobalTheory GlobalTheory.FrameBiextId
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}
namespace GlobalTheory.FrameBiextId
theorem _root_.solution {R σ : Type} [CommRing R] [Finite σ] {f g : MvPowerSeries σ R}
    (h : ∀ m : ℕ, Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ (m + 1)) (truncTotal (m + 1) f) =
      Ideal.Quotient.mk _ (truncTotal (m + 1) g)) : f = g := by
  ext e
  have h1 := h (Finsupp.degree e)
  rw [Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff'] at h1
  have h2 := h1 e (Nat.lt_succ_self _)
  rw [MvPolynomial.coeff_sub, coeff_truncTotal _ (Nat.lt_succ_self _),
    coeff_truncTotal _ (Nat.lt_succ_self _), sub_eq_zero] at h2
  exact h2
end GlobalTheory.FrameBiextId
