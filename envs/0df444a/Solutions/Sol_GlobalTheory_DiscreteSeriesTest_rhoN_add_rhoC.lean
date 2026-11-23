-- Prove2me | solution 1 for GlobalTheory.DiscreteSeriesTest.rhoN_add_rhoC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:26.044888+00:00
-- url     : https://prove2.me/submissions/c3968c44-9581-4663-b4b9-396c00ff7b27

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_LowKAddStrictAnti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI.UpqRep MeasureTheory Matrix Finset
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.DiscreteSeriesTest
namespace GlobalTheory.DiscreteSeriesTest
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    rhoN ε a + rhoC ε a = ((n : ℝ) - 1) / 2 - a := by
  have h1 := Finset.card_filter_add_card_filter_not (s := univ.filter fun b : Fin n => a < b) (fun b => ε b = ε a)
  have h2 := Finset.card_filter_add_card_filter_not (s := univ.filter fun b : Fin n => b < a) (fun b => ε b = ε a)
  rw [Finset.filter_filter, Finset.filter_filter] at h1 h2
  have e1 : (univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext; simp
  have e2 : (univ.filter fun b : Fin n => b < a) = Finset.Iio a := by ext; simp
  rw [e1, Fin.card_Ioi] at h1
  rw [e2, Fin.card_Iio] at h2
  have ha := a.isLt
  have h3 : ((n - 1 - (a : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - a := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
  have h1' := congrArg (Nat.cast : ℕ → ℝ) h1
  have h2' := congrArg (Nat.cast : ℕ → ℝ) h2
  rw [h3] at h1'
  push_cast at h1' h2'
  simp only [rhoN, rhoC, ne_eq]
  linarith
end GlobalTheory.DiscreteSeriesTest
