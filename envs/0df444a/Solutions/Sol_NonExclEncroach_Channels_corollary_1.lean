-- Prove2me | solution 1 for NonExclEncroach.Channels.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:23:57.572987+00:00
-- url     : https://prove2.me/submissions/e61a9f3c-12b3-44db-8fee-a9ef99bfb3d4

import Mathlib
import Definitions.Def_NonExclEncroach_Channels_Model

open NonExclEncroach.Channels

theorem solution (θ c b q1 : ℝ) : q2III θ c b b q1 = q2conj θ c b q1 := by
  unfold q2III q2conj q2IIIUpper q2conjUpper
  split_ifs
  · ring
  · rfl
