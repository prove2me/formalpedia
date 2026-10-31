-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.shift_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:44:04.00636+00:00
-- url     : https://prove2.me/submissions/b2d93bd9-10d2-4ba8-a07d-fb4ae3d85340

import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Deterministic shifts of continuous paths

This file defines translation by a fixed nonnegative time on canonical continuous-path space.
The shift is jointly continuous in the shift time and path for the compact-open topology.  It also
records the corresponding deterministic relation between the canonical filtrations.

No random-time shift, Markov property, strong Markov property, or Hunt-process assertion is made.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

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
# Deterministic shifts of continuous paths

This file defines translation by a fixed nonnegative time on canonical continuous-path space.
The shift is jointly continuous in the shift time and path for the compact-open topology.  It also
records the corresponding deterministic relation between the canonical filtrations.

No random-time shift, Markov property, strong Markov property, or Hunt-process assertion is made.
-/

open MeasureTheory


variable {alpha : Type*} [TopologicalSpace alpha]









namespace MarkovProcess.ContinuousPath
end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath
@[simp]
theorem solution (omega : ContinuousPath alpha) : shift 0 omega = omega := by
  ext t
  simp only [shift_apply, zero_add]
