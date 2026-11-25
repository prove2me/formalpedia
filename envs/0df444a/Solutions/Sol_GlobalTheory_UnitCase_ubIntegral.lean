-- Prove2me | solution 1 for GlobalTheory.UnitCase.ubIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:56:37.544616+00:00
-- url     : https://prove2.me/submissions/3fb2256a-b3e2-4db3-97c0-cc28eb3f381a

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_mvExp_sum
import Theorems.Thm_GlobalTheory_UnitCase_inv_mem_intRing
import Theorems.Thm_GlobalTheory_UnitCase_le_weight_of_coeff_pow
import Theorems.Thm_GlobalTheory_UnitCase_degL_eq_row
import Theorems.Thm_GlobalTheory_UnitCase_degR_eq_row
import Theorems.Thm_GlobalTheory_UnitCase_constantCoeff_eq_zero

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
theorem _root_.solution : UBIntegral := by
  intro C _ _ v l hl h5 hvl hp n0 y hy h1 H m hm hm'
  classical
  let hb : Fin n0 → MvPowerSeries (PVar n0) C := fun b p =>
    if ∀ x ∈ p.support, rowOf x = b then MvPowerSeries.coeff p h1 else 0
  have hbc : ∀ b p, MvPowerSeries.coeff p (hb b) =
      if ∀ x ∈ p.support, rowOf x = b then MvPowerSeries.coeff p h1 else 0 := fun _ _ => rfl
  have hdec : h1 = ∑ b, hb b := by
    ext p
    rw [map_sum]
    simp only [hbc]
    by_cases h0 : MvPowerSeries.coeff p h1 = 0
    · simp [h0]
    · obtain ⟨b, hb'⟩ := H.1 p h0
      rw [Finset.sum_eq_single b, if_pos hb']
      · intro b' _ hne
        rw [if_neg]
        intro h
        have hp0 : p ≠ 0 := by
          rintro rfl
          exact h0 (constantCoeff_eq_zero H)
        obtain ⟨x, hx⟩ := Finsupp.support_nonempty_iff.2 hp0
        exact hne ((h x hx).symm.trans (hb' x hx))
      · simp
  have hb0 : ∀ b, MvPowerSeries.constantCoeff (hb b) = 0 := by
    intro b
    change MvPowerSeries.coeff 0 (hb b) = 0
    rw [hbc, if_pos (by simp)]
    exact constantCoeff_eq_zero H
  have hZ : ∀ p ≤ m, ∀ b, rowDegZ p b ≤ l * y := fun p hpm b =>
    le_trans (Finset.sum_le_sum fun c _ => hpm _) (hm b)
  have hZ' : ∀ p ≤ m, ∀ b, rowDegZ' p b ≤ y := fun p hpm b =>
    le_trans (Finset.sum_le_sum fun c _ => hpm _) (hm' b)
  have hint : ∀ b, hb b ∈ intBelow (intRing v) m := by
    intro b p hpm
    rw [hbc]
    split_ifs with h
    · refine H.2.2 p ?_ ?_
      · rw [degL_eq_row h, sq]
        exact (hZ p hpm b).trans_lt (Nat.mul_lt_mul_of_pos_left hy hl.pos)
      · rw [degR_eq_row h]
        exact (hZ' p hpm b).trans_lt hy
    · exact zero_mem _
  have hexp : ∀ b, mvExp (hb b) ∈ intBelow (intRing v) m := by
    intro b p hpm
    change ∑ k ∈ Finset.range (p.degree + 1), _ ∈ _
    refine sum_mem fun k _ => ?_
    by_cases h0 : MvPowerSeries.coeff p (hb b ^ k) = 0
    · rw [h0, zero_div]
      exact zero_mem _
    · have hk : k ≤ rowDegZ' p b := by
        refine le_weight_of_coeff_pow (fun p => rowDegZ' p b)
          (fun a c => by simp [rowDegZ', Finset.sum_add_distrib]) ?_ k p h0
        intro r hr
        rw [hbc] at hr
        split_ifs at hr with h
        · change 1 ≤ rowDegZ' r b
          rw [← degR_eq_row h]
          exact H.2.1 r hr
        · exact absurd rfl hr
      have := hZ' p hpm b
      rw [div_eq_mul_inv]
      refine mul_mem (pow_mem (hint b) k p hpm) (inv_mem_intRing hp _ fun hd => ?_)
      have := hl.dvd_factorial.1 hd
      omega
  rw [hdec, mvExp_sum _ _ hb0]
  exact prod_mem (fun b _ => hexp b) m le_rfl
end GlobalTheory.UnitCase
