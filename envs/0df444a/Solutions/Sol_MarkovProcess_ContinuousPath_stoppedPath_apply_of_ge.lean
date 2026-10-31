-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.stoppedPath_apply_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:44:09.795435+00:00
-- url     : https://prove2.me/submissions/0e9d8ebd-5baa-49f1-9443-1f417bd746d9

import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_Stopping_15bd9e0d
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Deterministic stopping of continuous paths

This file defines stopping a continuous path at a fixed deterministic time. It proves only
topological and Borel-measurability properties of this operation; it introduces no stopping
times or stochastic laws.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]





















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
# Deterministic stopping of continuous paths

This file defines stopping a continuous path at a fixed deterministic time. It proves only
topological and Borel-measurability properties of this operation; it introduces no stopping
times or stochastic laws.
-/



variable {alpha : Type*} [TopologicalSpace alpha]











namespace MarkovProcess.ContinuousPath
end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath
@[simp]
theorem solution (T : NNReal) (omega : ContinuousPath alpha) (t : NNReal)
    (ht : T ≤ t) : stoppedPath T omega t = omega T := by
  rw [stoppedPath_apply, min_eq_right ht]
