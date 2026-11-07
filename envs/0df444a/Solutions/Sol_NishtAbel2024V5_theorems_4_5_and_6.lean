-- Prove2me | solution 1 for NishtAbel2024V5.theorems_4_5_and_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T04:29:43.760193+00:00
-- url     : https://prove2.me/submissions/6d611823-fd9f-4123-9fdc-501a81556468

import Definitions.Def_NishtAbel2024V5_Syntax
import Definitions.Def_NishtAbel2024V5_Semantics
import Definitions.Def_NishtAbel2024V5_Inference
import Definitions.Def_NishtAbel2024V5_SemFundamental

open NishtAbel2024V5

theorem solution :
    (∀ (W sig Ξ : List FunDecl),
      (∀ d ∈ sig ++ Ξ, d ∈ W) →
      (W.map FunDecl.name).Nodup →
      (∀ d ∈ W, (Tm.lam d.clauses).Closed) →
      BlockTy sig Ξ →
      SemValid W sig →
      SemValid W Ξ) ∧
    (∀ (W : List FunDecl) (blocks : List (List FunDecl)),
      (∀ d ∈ blocks.flatten, d ∈ W) →
      (W.map FunDecl.name).Nodup →
      (∀ d ∈ W, (Tm.lam d.clauses).Closed) →
      BlocksTy blocks →
      SemValid W blocks.flatten) ∧
    (∀ (blocks : List (List FunDecl)) (main : Tm) (A : Ty),
      ProgramTy blocks main A →
      SN blocks.flatten main) ∧
    (∀ (sig Ξ : List FunDecl),
      LexBlockTy sig Ξ →
      BlockTy sig Ξ) :=
  ⟨theorem_4_core,
   fun _ _ hsub hnames hwc hbt => blocks_valid ramseyPairs hnames hwc hbt hsub,
   theorem_5_core,
   fun _ _ h => theorem_6_proof h⟩
