-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.stoppedPath_stoppedPath
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:44:11.568134+00:00
-- url     : https://prove2.me/submissions/42ccb2e9-5590-4223-867a-10bf5895ad20

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
theorem solution (S T : NNReal) (omega : ContinuousPath alpha) :
    stoppedPath S (stoppedPath T omega) = stoppedPath (min S T) omega := by
  apply ContinuousMap.ext
  intro t
  simp only [stoppedPath_apply, min_assoc]
