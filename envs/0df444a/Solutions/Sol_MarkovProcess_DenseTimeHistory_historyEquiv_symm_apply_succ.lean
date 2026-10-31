-- Prove2me | solution 1 for MarkovProcess.DenseTimeHistory.historyEquiv_symm_apply_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:44:53.072974+00:00
-- url     : https://prove2.me/submissions/2b58709a-0f50-42de-8331-faa04e654b21

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
theorem solution (n : ℕ) (x : α) (path : Fin n → α) (i : Fin n) :
    (historyEquiv n).symm (x, path) ⟨i.succ, i.isLt⟩ = path i :=
  rfl
