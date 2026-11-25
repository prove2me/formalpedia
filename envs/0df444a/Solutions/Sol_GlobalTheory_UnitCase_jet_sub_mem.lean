-- Prove2me | solution 1 for GlobalTheory.UnitCase.jet_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:38:52.169581+00:00
-- url     : https://prove2.me/submissions/1bf572fb-83b6-4d10-99a1-199627302314

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_offDiag_mem
import Theorems.Thm_GlobalTheory_UnitCase_diag_mem
import Theorems.Thm_GlobalTheory_UnitCase_jetAt0_rename_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.UnitCase
theorem _root_.solution [CharZero C] [Fintype κ] {l : ℕ} (hl : l.Prime) (O : Subring C)
    (hO : ∀ n : ℕ, ¬ l ∣ n → (n : C)⁻¹ ∈ O) (q : MvPolynomial κ ℤ)
    (hB : ∀ B ∈ q.support, ∀ j, B j < l)
    (hAB : ∀ A ∈ (q ^ l).support, ∀ B ∈ q.support, ∑ j, A j = l * ∑ j, B j)
    (G : MvPowerSeries (κ ⊕ κ) C) (hG0 : MvPowerSeries.coeff 0 G = 1)
    (hG : ∀ A ∈ (q ^ l).support, ∀ B ∈ q.support,
      ∀ m ≤ Finsupp.sumElim A B, MvPowerSeries.coeff m G ∈ O) :
    jetAt0 (MvPolynomial.rename Sum.inl (MvPolynomial.map (Int.castRingHom C) (q ^ l)) *
        MvPolynomial.rename Sum.inr (MvPolynomial.map (Int.castRingHom C) q))
        (mvExp (mainTerm l (-(l : C)⁻¹)) * G) -
      ∑ B ∈ q.support, ((MvPolynomial.coeff B q : ℤ) : C) * mfact B *
        (MvPolynomial.coeff B q : ℤ) ∈ mult O l := by
  have h1 := sum_mem fun A hA => sum_mem fun B hB' =>
    offDiag_mem hl O hO q (MvPolynomial.coeff B q) A B (hB B hB') (hAB A hA B hB') G hG0
      (hG A hA B hB')
  have h2 := sum_mem (t := q.support) fun B _ => diag_mem hl O q B
  have h3 := add_mem h1 h2
  simp only [Finset.sum_sub_distrib] at h3
  rw [Finset.sum_comm (s := q.support), sub_add_sub_cancel] at h3
  rwa [jetAt0_rename_mul]
end GlobalTheory.UnitCase
