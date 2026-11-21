-- Prove2me | solution 1 for MasulloRH.logDeriv_on_strip_complement
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-11-20T21:37:11.541183+00:00
-- url     : https://prove2.me/submissions/301d5ba1-b787-4eb3-a64d-27f944ae247d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_regularized_rhs_analytic
import Theorems.Thm_MasulloRH_regularized_initial_identity
import Theorems.Thm_MasulloRH_derivative_identity_continuation
import Theorems.Thm_MasulloRH_logDeriv_analytic_of_local_ode

set_option autoImplicit false

open MasulloRH Set Filter
open scoped Topology

/-- Continue an analytic derivative identity, then use local analytic ODE uniqueness. -/
theorem solution (α : ℝ) (hα : 0 < α) (hαsmall : α < 1 / 2)
    (s : ℂ) (hs : InTraceContinuationDomain α s) :
    AnalyticAt ℂ zetaLogDeriv s := by
  have hhol := regularized_rhs_analytic α hα hαsmall
  have hinit := regularized_initial_identity α hα hαsmall
  apply logDeriv_analytic_of_local_ode s hs.2 (regularizedTraceRHS α) (hhol s hs)
  have hopen : IsOpen {z : ℂ | InTraceContinuationDomain α z} := by
    change IsOpen ({z : ℂ | 1 / 2 + α < z.re} ∩ {z : ℂ | z ≠ 1})
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      isOpen_compl_singleton
  filter_upwards [hopen.mem_nhds hs] with z hz
  exact derivative_identity_continuation α hα hαsmall hhol hinit z hz
