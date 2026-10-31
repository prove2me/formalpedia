-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.measurable_stoppedPath_operator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:35:17.768978+00:00
-- url     : https://prove2.me/submissions/bc140406-0c8a-453b-9f29-9cbf202ab3f9

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















/-- Stopping at a fixed deterministic time is continuous in the compact-open topology. -/
theorem continuous_stoppedPath_operator (T : NNReal) :
    Continuous (stoppedPath (alpha := alpha) T) :=
  ContinuousMap.continuous_precomp (clampTime T)





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
theorem solution (T : NNReal) :
    @Measurable (ContinuousPath alpha) (ContinuousPath alpha)
      (borel (ContinuousPath alpha)) (borel (ContinuousPath alpha))
      (stoppedPath (alpha := alpha) T) :=
  (continuous_stoppedPath_operator T).borel_measurable
