-- Prove2me | solution 1 for LassoDantzig.Dantzig.eq_B27
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T00:11:05.448457+00:00
-- url     : https://prove2.me/submissions/f119b341-7436-4c98-869e-cc1e9c129f93

import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

open LassoDantzig.Dantzig

theorem solution {M : ℕ} (s : ℕ) (c0 : ℝ) (hc0 : 0 < c0) (J0 : Finset (Fin M))
    (hJ0 : J0.card ≤ s) (δ : Fin M → ℝ) (hcone : ConeCond c0 J0 δ) :
    ∑ j, |δ j| = l1On δ J0 + l1On δ J0ᶜ ∧
    l1On δ J0 + l1On δ J0ᶜ ≤ (1 + c0) * l1On δ J0 ∧
    (1 + c0) * l1On δ J0 ≤ (1 + c0) * Real.sqrt s * l2On δ J0 := by
  have hc : l1On δ J0ᶜ ≤ c0 * l1On δ J0 := hcone
  have hsplit : ∑ j, |δ j| = l1On δ J0 + l1On δ J0ᶜ :=
    (Finset.sum_add_sum_compl J0 (fun j => |δ j|)).symm
  have hcs : (∑ j ∈ J0, |δ j|) ≤ Real.sqrt (J0.card) * Real.sqrt (∑ j ∈ J0, δ j ^ 2) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt J0 (fun _ => (1 : ℝ)) (fun j => |δ j|)
    simpa [sq_abs] using h
  have hcs' : l1On δ J0 ≤ Real.sqrt (J0.card) * l2On δ J0 := by
    unfold l1On l2On
    exact hcs
  have hsq : Real.sqrt (J0.card) ≤ Real.sqrt s :=
    Real.sqrt_le_sqrt (by exact_mod_cast hJ0)
  have hl2 : 0 ≤ l2On δ J0 := Real.sqrt_nonneg _
  have hpos : (0 : ℝ) ≤ 1 + c0 := by linarith
  refine ⟨hsplit, by linarith, ?_⟩
  have h1 : l1On δ J0 ≤ Real.sqrt s * l2On δ J0 :=
    le_trans hcs' (mul_le_mul_of_nonneg_right hsq hl2)
  calc (1 + c0) * l1On δ J0 ≤ (1 + c0) * (Real.sqrt s * l2On δ J0) :=
        mul_le_mul_of_nonneg_left h1 hpos
    _ = (1 + c0) * Real.sqrt s * l2On δ J0 := by ring
