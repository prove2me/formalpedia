-- Prove2me | solution 1 for OAI.ShortDraftDescent.binary_energy_descent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:21.603195+00:00
-- url     : https://prove2.me/submissions/5fe94cf9-ead3-456e-8c9f-5a97429bcff5

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.ShortDraftDescent
namespace OAI.ShortDraftDescent
theorem _root_.solution
    {Node : Type*} (rank : Node → ℕ) (energy mass : Node → ℝ)
    (left right : Node → Node) (costLeft costRight : Node → ℝ)
    (henergy : ∀ x, 0 ≤ energy x)
    (hmass : ∀ x, 0 ≤ mass x)
    (hcostLeft : ∀ x, 0 ≤ costLeft x)
    (hcostRight : ∀ x, 0 ≤ costRight x)
    (hterminal : ∀ x, rank x = 0 → energy x ≤ mass x)
    (hstep : ∀ x, rank x ≠ 0 →
      rank (left x) < rank x ∧ rank (right x) < rank x ∧
      energy x ^ 2 ≤
        (costLeft x * energy (left x)) *
          (costRight x * energy (right x)) ∧
      costLeft x * mass (left x) ≤ mass x ∧
      costRight x * mass (right x) ≤ mass x) :
    ∀ x, energy x ≤ mass x := by
  have H : ∀ n : ℕ, ∀ x, rank x = n → energy x ≤ mass x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      by_cases hn : n = 0
      · exact hterminal x (hx.trans hn)
      obtain ⟨hrl, hrr, hE, hMl, hMr⟩ := hstep x (by omega)
      have hEl := ih (rank (left x)) (by omega) (left x) rfl
      have hEr := ih (rank (right x)) (by omega) (right x) rfl
      have hcl := mul_le_mul_of_nonneg_left hEl (hcostLeft x)
      have hcr := mul_le_mul_of_nonneg_left hEr (hcostRight x)
      have hcl0 : 0 ≤ costLeft x * energy (left x) :=
        mul_nonneg (hcostLeft x) (henergy (left x))
      have hcr0 : 0 ≤ costRight x * energy (right x) :=
        mul_nonneg (hcostRight x) (henergy (right x))
      have hml0 : 0 ≤ costLeft x * mass (left x) :=
        mul_nonneg (hcostLeft x) (hmass (left x))
      have hmr0 : 0 ≤ costRight x * mass (right x) :=
        mul_nonneg (hcostRight x) (hmass (right x))
      have hprod₁ :
          (costLeft x * energy (left x)) *
            (costRight x * energy (right x)) ≤
          (costLeft x * mass (left x)) *
            (costRight x * mass (right x)) :=
        mul_le_mul hcl hcr hcr0 hml0
      have hprod₂ :
          (costLeft x * mass (left x)) *
            (costRight x * mass (right x)) ≤ mass x ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hMl) hmr0,
          mul_nonneg (hmass x) (sub_nonneg.mpr hMr)]
      have hsq : energy x ^ 2 ≤ mass x ^ 2 :=
        le_trans hE (le_trans hprod₁ hprod₂)
      nlinarith [henergy x, hmass x]
  intro x
  exact H (rank x) x rfl
end OAI.ShortDraftDescent
