-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_cleared_fe_of_laurent_fe_of_rational_forms
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/98c9f24d-9e6e-5c39-bb86-70788c237c3e

import Mathlib
import Theorems.Thm_Complex_forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_cleared_fe_of_laurent_fe_of_rational_forms

set_option autoImplicit false

theorem solution
    (q : ℕ) (hq : 1 < q) (Z Zd γ : ℂ → ℂ)

    (P₀ Pd₀ : Polynomial ℂ) (m₀ md₀ : ℤ) (σ₀ σd₀ : ℝ)
    (hZ₀ : ∀ s : ℂ, σ₀ < s.re → Z s = (q : ℂ) ^ ((m₀ : ℂ) * s) * P₀.eval ((q : ℂ) ^ (-s)))
    (hZd₀ : ∀ s : ℂ, σd₀ < s.re → Zd s = (q : ℂ) ^ ((md₀ : ℂ) * s) * Pd₀.eval ((q : ℂ) ^ (-s)))
    (hFE₀ : ∀ s : ℂ, (q : ℂ) ^ ((md₀ : ℂ) * s) * Pd₀.eval ((q : ℂ) ^ (-s)) =
      γ s * ((q : ℂ) ^ ((m₀ : ℂ) * (-s)) * P₀.eval ((q : ℂ) ^ s)))

    (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ σd : ℝ) (hQ : Q ≠ 0) (hQd : Qd ≠ 0)
    (hZ : ∀ s : ℂ, σ < s.re → Z s * Q.eval ((q : ℂ) ^ (-s)) = (q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)))
    (hZd : ∀ s : ℂ, σd < s.re →
      Zd s * Qd.eval ((q : ℂ) ^ (-s)) = (q : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((q : ℂ) ^ (-s))) :
    ∀ s : ℂ, (q : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((q : ℂ) ^ (-s)) * Q.eval ((q : ℂ) ^ s) =
      γ s * ((q : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((q : ℂ) ^ s)) * Qd.eval ((q : ℂ) ^ (-s)) := by

  have hreal : ∀ τ : ℝ, {t : ℝ | ((t : ℂ)) ∈ {s : ℂ | τ < s.re}}.Infinite := by
    intro τ
    have : {t : ℝ | ((t : ℂ)) ∈ {s : ℂ | τ < s.re}} = Set.Ioi τ := by
      ext t; simp
    rw [this]; exact Set.Ioi_infinite τ
  have hprim : ∀ s : ℂ, (q : ℂ) ^ ((m₀ : ℂ) * s) * P₀.eval ((q : ℂ) ^ (-s)) * Q.eval ((q : ℂ) ^ (-s)) =
      P.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((m : ℂ) * s) := by
    refine (Complex.forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite q hq P₀ P Q hQ
      m₀ m γ Zd {s : ℂ | max σ₀ σ < s.re} ∅ (hreal _) ?_ (fun s hs => absurd hs (Set.notMem_empty s))).1
    intro s hs
    have h1 : σ₀ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have h2 : σ < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    rw [← hZ₀ s h1, mul_comm (P.eval _), ← hZ s h2]
  have hdual : ∀ s : ℂ, (q : ℂ) ^ ((md₀ : ℂ) * s) * Pd₀.eval ((q : ℂ) ^ (-s)) * Qd.eval ((q : ℂ) ^ (-s)) =
      Pd.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((md : ℂ) * s) := by
    refine (Complex.forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite q hq Pd₀ Pd Qd hQd
      md₀ md γ Zd {s : ℂ | max σd₀ σd < s.re} ∅ (hreal _) ?_ (fun s hs => absurd hs (Set.notMem_empty s))).1
    intro s hs
    have h1 : σd₀ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have h2 : σd < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    rw [← hZd₀ s h1, mul_comm (Pd.eval _), ← hZd s h2]
  intro s
  have hp := hprim (-s)
  simp only [neg_neg] at hp
  calc (q : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((q : ℂ) ^ (-s)) * Q.eval ((q : ℂ) ^ s)
      = ((q : ℂ) ^ ((md₀ : ℂ) * s) * Pd₀.eval ((q : ℂ) ^ (-s)) * Qd.eval ((q : ℂ) ^ (-s))) * Q.eval ((q : ℂ) ^ s) := by
        rw [hdual s, mul_comm (Pd.eval _)]
    _ = γ s * ((q : ℂ) ^ ((m₀ : ℂ) * (-s)) * P₀.eval ((q : ℂ) ^ s) * Q.eval ((q : ℂ) ^ s)) *
          Qd.eval ((q : ℂ) ^ (-s)) := by rw [hFE₀ s]; ring
    _ = γ s * ((q : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((q : ℂ) ^ s)) * Qd.eval ((q : ℂ) ^ (-s)) := by
        rw [hp, mul_comm (P.eval _)]

end S_LanglandsTunnell_RankinSelberg_forall_cleared_fe_of_laurent_fe_of_rational_forms
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_cleared_fe_of_laurent_fe_of_rational_forms (solution)
