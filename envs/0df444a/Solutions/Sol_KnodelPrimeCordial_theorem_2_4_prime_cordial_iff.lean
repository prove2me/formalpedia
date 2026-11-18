-- Prove2me | solution 1 for KnodelPrimeCordial.theorem_2_4_prime_cordial_iff
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T08:11:02.670711+00:00
-- url     : https://prove2.me/submissions/767e5d94-8ec1-456a-818a-68a65640df2d

import Theorems.Thm_KnodelPrimeCordial_lemma_2_1
import Theorems.Thm_KnodelPrimeCordial_lemma_2_3

open KnodelPrimeCordial

theorem solution (n : ℕ) (hn : Even n) (h8 : 8 ≤ n) :
    PrimeCordial (knodel 3 n) ↔ n ≠ 8 := by
  constructor
  · intro hCordial hEq
    subst n
    exact (lemma_2_1 hCordial).elim
  · intro hne
    apply lemma_2_3 n hn
    rcases hn with ⟨k, hk⟩
    omega
