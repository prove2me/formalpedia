-- Prove2me | solution 1 for GeneralCK.generalCourtadeKumar_of_finiteHybridBellman
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T22:25:17.236467+00:00
-- url     : https://prove2.me/submissions/6a630df1-524d-404f-a3fc-f181e5004c86

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_statement
import Theorems.Thm_GeneralCK_LimitTransfer_regularizedEntropyBound_implies_CK
import Theorems.Thm_GeneralCK_regularizedEntropyBound_of_bellman

open scoped BigOperators
namespace GeneralCK
end GeneralCK

open GeneralCK in
open scoped BigOperators in
theorem solution
    (hB : FiniteHybridBellman) : GeneralCourtadeKumar :=
  LimitTransfer.regularizedEntropyBound_implies_CK (regularizedEntropyBound_of_bellman hB)
