-- Prove2me | solution 1 for NishtAbel2024V5.theorem_15
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T04:30:27.783052+00:00
-- url     : https://prove2.me/submissions/ae929c20-6234-4b3f-9cf7-abdcaa32308b

import Definitions.Def_NishtAbel2024V5_Syntax
import Definitions.Def_NishtAbel2024V5_Semantics
import Definitions.Def_NishtAbel2024V5_Inference
import Definitions.Def_NishtAbel2024V5_InfAlgorithm

open NishtAbel2024V5

theorem solution (W sig Ξ Ξannot : List FunDecl)
    (hsigwf : ∀ g ∈ sig, SizeCtxWf g.sizeParams ∧ KindingC g.sizeParams [] g.ty .star)
    (hacc : Algorithm2Accepts sig Ξ Ξannot)
    (hW : ∀ d ∈ sig ++ Ξannot, d ∈ W)
    (hnames : (W.map FunDecl.name).Nodup)
    (hclosed : ∀ d ∈ W, (Tm.lam d.clauses).Closed)
    (hsig : SemValid W sig) :
    BlockTy sig Ξannot ∧ SemValid W Ξannot :=
  theorem_15_proof ramseyPairs W sig Ξ Ξannot hsigwf hacc hW hnames hclosed hsig
