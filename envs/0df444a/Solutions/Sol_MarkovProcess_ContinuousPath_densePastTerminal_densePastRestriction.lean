-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.densePastTerminal_densePastRestriction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:26:57.390042+00:00
-- url     : https://prove2.me/submissions/5277298f-a29c-454a-a4d6-f6b83d7ca8bb

import Definitions.Def_MarkovProcess_V3H_Path_DenseFiltration_62a9879d
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Definitions.Def_MarkovProcess_V3H_Restart_RationalRestrictedRestart_3bd46ae7
import Definitions.Def_MarkovProcess_V3H_Restart_RestrictedRestartOfJoint_e84e7ad8
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Restricted restart at rational times

This file turns a full joint-law factorization of the rational past and shifted future into the
event-restricted restart identity on the canonical continuous-path filtration.  The joint-law
factorization remains an explicit input; proving it from the finite-dimensional Markov laws is the
next process-construction step.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ContinuousPath

noncomputable section

variable {alpha : Type*} [MetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]









end
end ContinuousPath
end MarkovProcess


open MarkovProcess
open MarkovProcess.ContinuousPath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Restricted restart at rational times

This file turns a full joint-law factorization of the rational past and shifted future into the
event-restricted restart identity on the canonical continuous-path filtration.  The joint-law
factorization remains an explicit input; proving it from the finite-dimensional Markov laws is the
next process-construction step.
-/

open MeasureTheory ProbabilityTheory



variable {alpha : Type*} [MetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]





namespace MarkovProcess.ContinuousPath
end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath
omit [MeasurableSpace alpha] [BorelSpace alpha] in

@[simp]
theorem solution (S : DenseTime) (omega : ContinuousPath alpha) :
    densePastTerminal S (densePastRestriction S omega) =
      coordinateProcess (alpha := alpha) (DenseTime.castOrderEmbedding S) omega :=
  rfl
