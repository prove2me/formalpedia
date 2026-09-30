-- Prove2me | solution 1 for KellyStochasticNetworks.detailedBalance_implies_fullBalance
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T19:59:46.31655+00:00
-- url     : https://prove2.me/submissions/1029f0c0-c5d2-4313-b940-52b0c7bc3e98

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance

open KellyStochasticNetworks

theorem solution {S : Type*} (π : S → ℝ) (q : S → S → ℝ)
    (h : DetailedBalance π q) : FullBalance π q := by
  intro j
  have hk : (fun k => π k * q k j) = fun k => π j * q j k := by
    funext k
    exact (h j k).symm
  rw [hk, tsum_mul_left]
