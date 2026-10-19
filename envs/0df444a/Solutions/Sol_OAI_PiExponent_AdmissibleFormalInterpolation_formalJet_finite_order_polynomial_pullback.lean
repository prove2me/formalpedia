-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalJet_finite_order_polynomial_pullback
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T12:08:04.607756+00:00
-- url     : https://prove2.me/submissions/684a2b85-6cb2-41ba-9a6f-c02bf79b1c91
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation_FiniteLogPullback
import Theorems.Thm_MvPowerSeries_coeff_polynomial_algHom_eq_of_X_eq_below
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftLogSeries_log_coeff_finite_sum

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution {m : ℕ} (T : ℕ) :
    ∃ A : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ]
        MvPolynomial (Fin (m + 1)) ℂ,
      ∀ (c : Fin m → ℂ) (a : Fin (m + 1) →₀ ℕ),
        a 0 < T → ∀ P : MvPolynomial (Fin (m + 1)) ℂ,
          MvPowerSeries.coeff a (formalJet c (A P)) =
            MvPowerSeries.coeff a
              ((MvPolynomial.aeval (fun i : Fin (m + 1) =>
                  MvPowerSeries.C
                    ((Fin.cases (1 : ℂ) c : Fin (m + 1) → ℂ) i) +
                  MvPowerSeries.X i) :
                MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ]
                  MvPowerSeries (Fin (m + 1)) ℂ) P) := by
  refine ⟨finiteLogPullback T, ?_⟩
  intro c a ha P
  let Q : MvPolynomial (Fin (m + 1)) ℂ :=
    ∑ k ∈ Finset.range T,
      (if k = 0 then 0 else
        (((-1 : ℂ) ^ (k + 1)) / (k : ℂ)) •
          (MvPolynomial.X 0 - 1) ^ k)
  let S : MvPowerSeries (Fin (m + 1)) ℂ :=
    ∑ k ∈ Finset.range T,
      (if k = 0 then 0 else
        (((-1 : ℂ) ^ (k + 1)) / (k : ℂ)) •
          (MvPowerSeries.X 0) ^ k)
  have hX : formalJet c (MvPolynomial.X 0 - 1) = MvPowerSeries.X 0 := by
    simp [formalJet]
  have hQ : formalJet c Q = S := by
    dsimp only [Q, S]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hk0 : k = 0
    · simp only [if_pos hk0, map_zero]
    · simp only [if_neg hk0, map_smul, map_pow, hX]
  let F : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ]
      MvPowerSeries (Fin (m + 1)) ℂ :=
    (formalJet c).comp (finiteLogPullback T)
  let G : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ]
      MvPowerSeries (Fin (m + 1)) ℂ :=
    MvPolynomial.aeval (fun i : Fin (m + 1) =>
      MvPowerSeries.C
        ((Fin.cases (1 : ℂ) c : Fin (m + 1) → ℂ) i) +
      MvPowerSeries.X i)
  have hgen : ∀ (i : Fin (m + 1)) (b : Fin (m + 1) →₀ ℕ), b 0 < T →
      MvPowerSeries.coeff b (F (MvPolynomial.X i)) =
        MvPowerSeries.coeff b (G (MvPolynomial.X i)) := by
    intro i b hb
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [F, G, finiteLogPullback, formalJet]
    · have hlog : MvPowerSeries.coeff b (liftLogSeries m (PowerSeries.log ℂ)) =
          MvPowerSeries.coeff b S :=
        liftLogSeries_log_coeff_finite_sum T b hb
      have hA : finiteLogPullback T (MvPolynomial.X j.succ) =
          MvPolynomial.X j.succ - Q := by
        simp [finiteLogPullback, Q]
      simp only [F, G, AlgHom.comp_apply, MvPolynomial.aeval_X, Fin.cases_succ]
      rw [hA, map_sub, hQ]
      simp only [formalJet, MvPolynomial.aeval_X, Fin.cases_succ,
        map_sub, map_add, hlog, add_sub_cancel_right]
  exact MvPowerSeries.coeff_polynomial_algHom_eq_of_X_eq_below F G 0 T hgen P a ha
