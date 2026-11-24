-- Prove2me | solution 1 for GlobalTheory.PushHarm.pderiv_push_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:56:32.173286+00:00
-- url     : https://prove2.me/submissions/63fa9131-f254-4153-8420-49c02591c120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UnitaryDetClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PushMemHarmK
import Theorems.Thm_GlobalTheory_PushHarm_push_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PushHarm
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l) {n : ℕ}
open Classical
namespace GlobalTheory.PushHarm
theorem _root_.solution (γ : Matrix (Fin n) (Fin n) E) (τ : E →+* ℂ) (a : Fin (Dw.mult τ)) (b : Fin n)
    (ℓ : LtN Dw n) :
    pderiv (⟨τ, a, b⟩ : LtN Dw n) (push c γ (X ℓ)) =
      ∑ j, embF c τ (γ b j) • push c γ (pderiv (⟨τ, a, j⟩ : LtN Dw n) (X ℓ)) := by
  obtain ⟨σ, i, j⟩ := ℓ
  rw [push_X, map_sum]
  simp only [pderiv_C_mul, pderiv_X]
  by_cases hσ : σ = τ
  · subst hσ
    by_cases hi : i = a
    · subst hi
      rw [Finset.sum_eq_single b, Finset.sum_eq_single j]
      · simp [smul_eq_C_mul]
      · intro k _ hk
        rw [Pi.single_eq_of_ne]
        · simp
        · simpa using hk.symm
      · simp
      · intro k _ hk
        rw [Pi.single_eq_of_ne]
        · simp
        · simpa using hk
      · simp
    · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
      · intro k _
        rw [Pi.single_eq_of_ne]
        · simp
        · simp [hi]
      · intro k _
        rw [Pi.single_eq_of_ne]
        · simp
        · simp [hi]
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro k _
      rw [Pi.single_eq_of_ne]
      · simp
      · exact fun h => hσ (congrArg Sigma.fst h)
    · intro k _
      rw [Pi.single_eq_of_ne]
      · simp
      · exact fun h => hσ (congrArg Sigma.fst h)
end GlobalTheory.PushHarm
