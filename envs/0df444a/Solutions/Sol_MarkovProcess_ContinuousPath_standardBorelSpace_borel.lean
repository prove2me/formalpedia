-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.standardBorelSpace_borel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:44:02.083413+00:00
-- url     : https://prove2.me/submissions/579a6772-60e5-4f24-b5fe-242f435d46f3

import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_Polish_87f91693
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Polish structure of continuous-path space

For a complete separable metric state space, the compact-open topology on continuous paths is
Polish: it is second countable, and it is induced by the compact-convergence uniformity, which is
complete and countably generated because nonnegative time is locally compact and sigma-compact.
With the Borel sigma-algebra the path space is therefore a standard Borel space.

This is ordinary topological infrastructure.  It proves no probabilistic statement.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [SecondCountableTopology alpha]





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
# Polish structure of continuous-path space

For a complete separable metric state space, the compact-open topology on continuous paths is
Polish: it is second countable, and it is induced by the compact-convergence uniformity, which is
complete and countably generated because nonnegative time is locally compact and sigma-compact.
With the Borel sigma-algebra the path space is therefore a standard Borel space.

This is ordinary topological infrastructure.  It proves no probabilistic statement.
-/


variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [SecondCountableTopology alpha]



namespace MarkovProcess.ContinuousPath

end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath
theorem solution :
    @StandardBorelSpace (ContinuousPath alpha) (borel (ContinuousPath alpha)) := by
  let : MeasurableSpace (ContinuousPath alpha) := borel (ContinuousPath alpha)
  have : BorelSpace (ContinuousPath alpha) := ⟨rfl⟩
  infer_instance
