-- Prove2me | solution 1 for MasulloRH.logDeriv_analytic_of_local_ode
-- status  : ACCEPTED   (prove)
-- author  : @ijawdoij123
-- created : 2026-11-20T21:53:09.756146+00:00
-- url     : https://prove2.me/submissions/6b5d1224-52c3-47b3-8aab-e7d920ebb18a

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- `riemannZeta` is analytic on the complement of its pole. -/
private lemma zeta_analyticOnNhd_compl_one : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
  DifferentiableOn.analyticOnNhd
    (fun _ hz => (differentiableAt_riemannZeta hz).differentiableWithinAt) isOpen_compl_singleton

/-- `riemannZeta` has finite analytic order at every point other than `1`. -/
private lemma zeta_analyticOrderAt_ne_top {s : ℂ} (hs : s ≠ 1) : analyticOrderAt riemannZeta s ≠ ⊤ := by
  have hU : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  refine zeta_analyticOnNhd_compl_one.analyticOrderAt_ne_top_of_isPreconnected hU h2 hs ?_
  rw [(zeta_analyticOnNhd_compl_one 2 h2).analyticOrderAt_eq_zero.mpr
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num))]
  exact ENat.zero_ne_top

theorem solution (s : ℂ) (hs : s ≠ 1)
    (H : ℂ → ℂ) (hH : AnalyticAt ℂ H s)
    (heq : ∀ᶠ z in 𝓝 s, deriv riemannZeta z = H z * riemannZeta z) :
    AnalyticAt ℂ MasulloRH.zetaLogDeriv s := by
  have hζ : AnalyticAt ℂ riemannZeta s := zeta_analyticOnNhd_compl_one s hs
  have hne : riemannZeta s ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (zeta_analyticOrderAt_ne_top hs)
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact (hζ.analyticOrderAt_eq_zero.mp hm.symm) h0
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have hd : analyticOrderAt (deriv riemannZeta) s = n :=
      analyticOrderAt_deriv_of_pos hζ (by rw [← hm]; push_cast; rfl)
    have hprod : analyticOrderAt (fun z => H z * riemannZeta z) s =
        analyticOrderAt H s + (n + 1 : ℕ) := by
      rw [hm]; exact analyticOrderAt_mul hH hζ
    rw [analyticOrderAt_congr heq, hprod] at hd
    -- `n = ord_s H + (n + 1)` is impossible in `ℕ∞`.
    cases hk : analyticOrderAt H s with
    | top => rw [hk] at hd; simp at hd
    | coe k => rw [hk] at hd; norm_cast at hd; omega
  exact hζ.deriv.div hζ hne
