-- Prove2me | solution 1 for GlobalTheory.RowValueCheck.valOf_kind_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:10:06.038453+00:00
-- url     : https://prove2.me/submissions/a7ff4d35-0771-4212-9011-2eab8ccaca6b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_ValOfKindIndep
import Theorems.Thm_GlobalTheory_RowValueCheck_Agree_mul
import Theorems.Thm_GlobalTheory_RowValueCheck_Agree_exp
import Theorems.Thm_GlobalTheory_RowValueCheck_Agree_prod
import Theorems.Thm_GlobalTheory_RowValueCheck_agree_rowCopy
import Theorems.Thm_GlobalTheory_RowValueCheck_valOf_eq
import Theorems.Thm_GlobalTheory_RowValueCheck_agree_hOf_zero
import Theorems.Thm_GlobalTheory_RowValueCheck_hOf_mixed
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul


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
theorem _root_.solution [NeZero d] (X : RowData C V d I J) {N : ℕ}
    (P : MvPolynomial (Fin N × WV I) C) (k k' : Fin N → Option (Fin 2 × ZMod d × ZMod d))
    (hk : RowsOK X.G X.Alt P k) (hk' : RowsOK X.G X.Alt P k')
    (gr : Fin N → MvPowerSeries (WV I) C) : ValOf X.hL P k gr = ValOf X.hL P k' gr := by
  rw [valOf_eq, valOf_eq]
  set S : Set (Fin N × WV I) := {x | ∃ μ ∈ P.support, μ x ≠ 0} with hS
  have key : ∀ ρ, Agree {w | (ρ, w) ∈ S} (hOf X.hL (k ρ)) (hOf X.hL (k' ρ)) := by
    intro ρ
    by_cases hone : ∃ g0 : Fin 2, ∀ w ∈ {w | (ρ, w) ∈ S}, w.1 = g0
    · obtain ⟨g0, hg0⟩ := hone
      intro μ hμ
      rw [agree_hOf_zero X _ g0 hg0 _ μ hμ, agree_hOf_zero X _ g0 hg0 _ μ hμ]
    · push Not at hone
      obtain ⟨w1, ⟨μ1, m1, n1⟩, e1⟩ := hone 0
      obtain ⟨w0, ⟨μ0, m0, n0⟩, e0⟩ := hone 1
      have f1 : w1.1 = 1 := by revert e1; generalize w1.1 = g; revert g; decide
      have f0 : w0.1 = 0 := by revert e0; generalize w0.1 = g; revert g; decide
      have aux : ∀ kk : Fin N → Option (Fin 2 × ZMod d × ZMod d), RowsOK X.G X.Alt P kk →
          hOf X.hL (kk ρ) = X.hL 0 (tyW X.G w0) (tyW X.G w1) := by
        intro kk hkk
        rcases hr : kk ρ with _ | ⟨g, a, a'⟩
        · obtain ⟨g, hg⟩ := hkk.2 ρ hr
          have := (hg μ0 m0 w0 n0).trans (hg μ1 m1 w1 n1).symm
          rw [f0, f1] at this
          exact absurd this (by decide)
        · obtain ⟨-, -, hl⟩ := hkk.1 ρ g a a' hr
          exact hOf_mixed X w0 w1 f0 f1 g a a' (hl μ0 m0 w0 n0) (hl μ1 m1 w1 n1)
      rw [aux k hk, aux k' hk']
      intro μ _
      rfl
  have hA := Agree.prod (S := S) Finset.univ (fun ρ =>
    Agree.mul (F := rowCopy ρ (gr ρ)) (F' := rowCopy ρ (gr ρ)) (fun _ _ => rfl)
      (agree_rowCopy S ρ _ _ (key ρ)).exp)
  unfold jetAt0
  exact Finset.sum_congr rfl fun μ hμ => by rw [hA μ fun x hx => ⟨μ, hμ, hx⟩]
end GlobalTheory.RowValueCheck
