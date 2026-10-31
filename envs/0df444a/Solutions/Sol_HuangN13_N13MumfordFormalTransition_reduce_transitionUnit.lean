-- Prove2me | solution 1 for HuangN13.N13MumfordFormalTransition.reduce_transitionUnit
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:32:12.018966+00:00
-- url     : https://prove2.me/submissions/d7c306a1-34b0-4850-9c38-cb330d4b5d80

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DoublingStatementCore
import Theorems.Thm_MazurProof_N13FormalLineBundleCech_reduceOverlap_mul

set_option autoImplicit false


set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem solution
    (D : MazurProof.N13MumfordFormalTransition.NearBaseMumford) :
    MazurProof.N13FormalLineBundleCech.reduceOverlap
        (MazurProof.N13FormalCurveOverlap.toOverlap
          (MazurProof.N13MumfordFormalTransition.transitionUnit D : MazurProof.N13MumfordFormalTransition.FormalCurve)) =
      MazurProof.N13FormalLineBundleCech.oneOverlap (R := MazurProof.N13MumfordFormalTransition.K) := by
  exact MazurProof.N13MumfordFormalTransition.reduce_transitionUnit D
