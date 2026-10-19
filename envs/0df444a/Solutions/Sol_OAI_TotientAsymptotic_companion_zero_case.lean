-- Prove2me | solution 1 for OAI.TotientAsymptotic.companion_zero_case
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:02:16.693694+00:00
-- url     : https://prove2.me/submissions/e8b9725c-2bf0-43b9-ad22-a6b209c1d8d5

import Definitions.Def_TotientCompanionZero

open scoped BigOperators Topology
open Filter OAI.TotientAsymptotic

theorem solution (k : ℕ) (_hk : 0 < k)
    (hno : ¬ ∃ d : ℕ, IsTotient d ∧ k*d < ell d) :
    (∀ x : ℝ, 0 < x → N k x = 0) ∧
    (∀ s ∈ Set.Ico (0 : ℝ) 1, A (fk k) s = 0) := by
  classical
  have hbound (d : ℕ) (hd : IsTotient d) : ell d ≤ k * d := by
    by_contra h
    exact hno ⟨d, hd, Nat.lt_of_not_ge h⟩
  have hweight (d : ℕ) (hd : IsTotient d) : fk k ((ell d : ℝ) / d) = 0 := by
    have hdpos : 0 < d := by
      obtain ⟨n, hn, rfl⟩ := hd
      exact Nat.totient_pos.mpr hn
    have hepos : 0 < ell d := by
      simpa only [ell, dif_pos hd] using (Nat.find_spec hd).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    have heR : (0 : ℝ) < ell d := by exact_mod_cast hepos
    have hqpos : 0 < (ell d : ℝ) / d := div_pos heR hdR
    have hqle : (ell d : ℝ) / d ≤ k := by
      apply (div_le_iff₀ hdR).mpr
      exact_mod_cast hbound d hd
    have h1 : (1 : ℝ) ≤ (k : ℝ) / ((ell d : ℝ) / d) :=
      (le_div_iff₀ hqpos).mpr (by simpa using hqle)
    have h2 : (1 : ℝ) ≤ (k + 1 : ℝ) / ((ell d : ℝ) / d) :=
      (le_div_iff₀ hqpos).mpr (by linarith)
    simp only [fk, min_eq_left h1, min_eq_left h2, sub_self]
  constructor
  · intro x hx
    have hempty : ((Finset.Icc 1 ⌊x⌋₊).filter fun v =>
        IsTotient v ∧ (k : ℝ) * x < ell v ∧ (ell v : ℝ) ≤ (k+1 : ℝ) * x) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      rcases Finset.mem_filter.mp hv with ⟨hv, hd, hlt, _⟩
      have hvx : (v : ℝ) ≤ x :=
        (Nat.cast_le.mpr (Finset.mem_Icc.mp hv).2).trans (Nat.floor_le (le_of_lt hx))
      have hb : (ell v : ℝ) ≤ (k : ℝ) * v := by exact_mod_cast hbound v hd
      have hmul := mul_le_mul_of_nonneg_left hvx (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      linarith
    simp only [N, hempty, Finset.card_empty, Nat.cast_zero]
  · have hAH (H : ℕ) (s : ℝ) : AH H (fk k) s = 0 := by
      unfold AH
      have hz : (fun d : ℕ => if IsTotient d then
          fk k ((ell d : ℝ) / d) / d *
            ∑ᶠ T : Finset (TailDatum H),
              if T.Nonempty ∧ (↑T : Set (TailDatum H)) ⊆ witnesses H s d then
                (-1 : ℝ)^(T.card-1) *
                  Real.exp (-(gamma / alpha s) *
                    ∑' n : ℕ, rho^(H+n) * maxD (H+n) T)
              else 0
          else 0) = fun _ => 0 := by
        funext d
        by_cases hd : IsTotient d
        · simp only [if_pos hd, hweight d hd, zero_div, zero_mul]
        · simp only [if_neg hd]
      rw [hz]
      simp
    intro s _
    simp only [A, hAH]
    exact tendsto_const_nhds.limUnder_eq
