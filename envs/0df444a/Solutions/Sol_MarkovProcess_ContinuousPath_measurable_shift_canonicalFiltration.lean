-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.measurable_shift_canonicalFiltration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:31:55.283074+00:00
-- url     : https://prove2.me/submissions/3c080780-7ab6-4bbe-9bb2-4927d5b83922

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
theorem solution [MeasurableSpace alpha] [BorelSpace alpha]
    (S t : NNReal) :
    Measurable[canonicalFiltration (alpha := alpha) (S + t),
      canonicalFiltration (alpha := alpha) t]
      (shift S : ContinuousPath alpha → ContinuousPath alpha) := by
  apply Measurable.of_comap_le
  rw [canonicalFiltration, MeasurableSpace.comap_iSup]
  rw [iSup_le_iff]
  intro u
  rw [MeasurableSpace.comap_comp]
  have hfun : coordinateProcess (alpha := alpha) u ∘ shift S =
      coordinateProcess (alpha := alpha) (S + u) := by
    funext omega
    exact shift_apply S u omega
  rw [hfun]
  exact le_iSup_of_le
    (⟨S + u.1, by simpa only [add_comm] using! add_le_add_left u.2 S⟩ :
      Set.Iic (S + t)) le_rfl
