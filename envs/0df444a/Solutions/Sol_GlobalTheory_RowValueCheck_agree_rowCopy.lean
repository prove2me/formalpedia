-- Prove2me | solution 1 for GlobalTheory.RowValueCheck.agree_rowCopy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:38:04.426677+00:00
-- url     : https://prove2.me/submissions/ceb75a04-e01c-4b50-ac2b-b9c71a02c1f3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_ValOfKindIndep
import Theorems.Thm_GlobalTheory_RowValueCheck_Agree_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open GlobalTheory GlobalTheory.RowValueCheck
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
namespace GlobalTheory.RowValueCheck
theorem _root_.solution {N : ℕ} (S : Set (Fin N × WV I)) (ρ : Fin N) (F F' : MvPowerSeries (WV I) C)
    (h : Agree {w | (ρ, w) ∈ S} F F') : Agree S (rowCopy ρ F) (rowCopy ρ F') := by
  intro μ hμ
  have hs : MvPowerSeries.HasSubst
      (fun w : WV I => (MvPowerSeries.X (ρ, w) : MvPowerSeries (Fin N × WV I) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by simp)
  unfold rowCopy
  rw [MvPowerSeries.coeff_subst hs, MvPowerSeries.coeff_subst hs]
  refine finsum_congr fun e => ?_
  by_cases he : ∀ x, e x ≠ 0 → (ρ, x) ∈ S
  · rw [h e he]
  · push Not at he
    obtain ⟨x, hx, hxS⟩ := he
    have h0 : μ (ρ, x) = 0 := by
      by_contra h1
      exact hxS (hμ _ h1)
    have hd : (MvPowerSeries.X (ρ, x) : MvPowerSeries (Fin N × WV I) C) ∣
        e.prod fun s k => (MvPowerSeries.X (ρ, s) : MvPowerSeries (Fin N × WV I) C) ^ k :=
      (dvd_pow_self _ hx).trans (Finset.dvd_prod_of_mem
        (fun s => (MvPowerSeries.X (ρ, s) : MvPowerSeries (Fin N × WV I) C) ^ e s)
        (Finsupp.mem_support_iff.2 hx))
    rw [MvPowerSeries.X_dvd_iff.1 hd μ h0]
    simp
end GlobalTheory.RowValueCheck
