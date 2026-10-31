-- Prove2me | solution 1 for MarkovProcess.DenseTimeHistory.iicEquivFin_symm_apply_val
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:45:00.616065+00:00
-- url     : https://prove2.me/submissions/9204011b-c2a3-4321-8a83-636e9e4e311b

import Definitions.Def_MarkovProcess_V3H_Time_DenseTimeHistory_28830881
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite dense-time histories

This file provides measurable coordinate equivalences for histories indexed by an initial
segment of the natural numbers. It makes no probability-law, kernel, or stochastic-process claim.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

namespace MarkovProcess



namespace DenseTimeHistory

variable {α : Type*} [MeasurableSpace α]



























end DenseTimeHistory

end MarkovProcess


open MarkovProcess
open MarkovProcess.DenseTimeHistory
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite dense-time histories

This file provides measurable coordinate equivalences for histories indexed by an initial
segment of the natural numbers. It makes no probability-law, kernel, or stochastic-process claim.
-/





variable {α : Type*} [MeasurableSpace α]





namespace MarkovProcess.DenseTimeHistory
end MarkovProcess.DenseTimeHistory
open MarkovProcess.DenseTimeHistory
@[simp]
theorem solution (n : ℕ) (i : Fin (n + 1)) :
    ((iicEquivFin n).symm i).val = i.val :=
  rfl
