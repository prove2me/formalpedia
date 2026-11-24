-- Prove2me | solution 1 for GlobalTheory.PushHarm.pderiv_push
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:15:35.9711+00:00
-- url     : https://prove2.me/submissions/119847dd-67f7-49ec-a30c-8620b0092cb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UnitaryDetClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PushMemHarmK
import Theorems.Thm_GlobalTheory_PushHarm_pderiv_push_X

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
namespace GlobalTheory.PushHarm
theorem _root_.solution (γ : Matrix (Fin n) (Fin n) E) (τ : E →+* ℂ) (a : Fin (Dw.mult τ)) (b : Fin n)
    (P : MvPolynomial (LtN Dw n) c.F) :
    pderiv (⟨τ, a, b⟩ : LtN Dw n) (push c γ P) =
      ∑ j, embF c τ (γ b j) • push c γ (pderiv (⟨τ, a, j⟩ : LtN Dw n) P) := by
  induction P using MvPolynomial.induction_on with
  | C x => simp [push]
  | add p q hp hq => simp [hp, hq, Finset.sum_add_distrib]
  | mul_X p ℓ hp =>
    rw [map_mul, Derivation.leibniz, hp, pderiv_push_X]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, smul_add, Finset.sum_add_distrib,
      Finset.mul_sum, mul_smul_comm]
end GlobalTheory.PushHarm
