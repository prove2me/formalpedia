-- Prove2me | solution 1 for KellerTrotter2017.cor5_10_odd_degree_count_even_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:58:53.122692+00:00
-- url     : https://prove2.me/submissions/72370b96-ddcb-4eac-959f-56e4460d9a7c

import Mathlib

theorem solution {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Even (Finset.univ.filter (fun v => Odd (G.degree v))).card := G.even_card_odd_degree_vertices
