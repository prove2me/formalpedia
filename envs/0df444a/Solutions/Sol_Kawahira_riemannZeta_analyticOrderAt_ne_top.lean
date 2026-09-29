-- Prove2me | solution 1 for Kawahira.riemannZeta_analyticOrderAt_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:07:41.888207+00:00
-- url     : https://prove2.me/submissions/db4e5a8a-237c-404b-bb7f-ac9192687955

import Definitions.Def_Kawahira_zeta

open Complex Topology Set

theorem solution (a : ℂ) (ha : a ≠ 1) :
    analyticOrderAt riemannZeta a ≠ ⊤ := by
  have hconn : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  apply analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected hconn
      (x := (0 : ℂ)) (y := a)
  · simp
  · simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using ha
  · have hzeta0 : riemannZeta (0 : ℂ) ≠ 0 := by
      rw [riemannZeta_zero]
      norm_num
    rw [analyticOrderAt_eq_zero.mpr (.inr hzeta0)]
    simp
