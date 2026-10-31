-- Prove2me | solution 1 for MarkovProcess.CountableEnumeration.exists_mem_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:44:32.290878+00:00
-- url     : https://prove2.me/submissions/c45f9273-bd27-4d52-90fb-24a029245939

import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Countable dense time indices

This file gives finite prefixes and measurable path reindexings for an arbitrary enumeration of
a countably infinite type. The fixed enumeration of nonnegative rational times below is arbitrary,
not increasing. No probability law, projective limit, stochastic process, continuity, or path
regularity is constructed here.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

namespace MarkovProcess

noncomputable section

namespace CountableEnumeration

variable {D : Type*}













theorem mem_prefix_self (e : ℕ ≃ D) (d : D) : d ∈ «prefix» e (e.symm d + 1) := by
  rw [mem_prefix_iff]
  exact Nat.lt_succ_self _









end CountableEnumeration



namespace DenseTime











end DenseTime
end
end MarkovProcess


open MarkovProcess
open MarkovProcess.CountableEnumeration
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Countable dense time indices

This file gives finite prefixes and measurable path reindexings for an arbitrary enumeration of
a countably infinite type. The fixed enumeration of nonnegative rational times below is arbitrary,
not increasing. No probability law, projective limit, stochastic process, continuity, or path
regularity is constructed here.
-/




variable {D : Type*}















namespace MarkovProcess.CountableEnumeration
end MarkovProcess.CountableEnumeration
open MarkovProcess.CountableEnumeration
theorem solution (e : ℕ ≃ D) (d : D) : ∃ n, d ∈ «prefix» e n :=
  ⟨e.symm d + 1, mem_prefix_self e d⟩
