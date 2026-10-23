-- Prove2me | solution 1 for KellerTrotter2017.thm5_9_degree_sum_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:58:25.502199+00:00
-- url     : https://prove2.me/submissions/3f2cbf46-5f53-4431-8bae-44f5b0ead9f7

import Mathlib

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v, G.degree v = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
