-- Prove2me | solution 1 for MarkovProcess.DenseTime.addOrderEmbedding_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:44:46.512388+00:00
-- url     : https://prove2.me/submissions/ca3cc5a3-dd9a-4a25-95e1-ba773eaa0762

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_DenseTime_Shift_b3e2f7d9
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Shifts of dense-time paths

This file defines addition by a nonnegative rational time on the fixed dense carrier and the
induced shift of dense-time paths.  Restriction of a continuous path commutes with this shift.
No probability law or Markov property is asserted.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

namespace MarkovProcess

noncomputable section

namespace DenseTime







end DenseTime

namespace DenseTimePath

variable {alpha : Type*}









variable [MeasurableSpace alpha]



end DenseTimePath

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]



end ContinuousPath
end
end MarkovProcess


open MarkovProcess
open MarkovProcess.DenseTime
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Shifts of dense-time paths

This file defines addition by a nonnegative rational time on the fixed dense carrier and the
induced shift of dense-time paths.  Restriction of a continuous path commutes with this shift.
No probability law or Markov property is asserted.
-/






namespace MarkovProcess.DenseTime
end MarkovProcess.DenseTime
open MarkovProcess.DenseTime
@[simp]
theorem solution (s t : DenseTime) : addOrderEmbedding s t = s + t := rfl
