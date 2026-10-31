-- Prove2me | solution 1 for MarkovProcess.CountableEnumeration.prefix_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:44:35.451511+00:00
-- url     : https://prove2.me/submissions/abe18b80-8e0b-4ff2-9bda-33ff21629464

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
@[simp]
theorem solution (e : ℕ ≃ D) (n : ℕ) :
    «prefix» e (n + 1) =
      Finset.cons (e n) («prefix» e n) (by
        rw [mem_prefix_iff, e.symm_apply_apply]
        exact Nat.lt_irrefl n) := by
  ext d
  rw [mem_prefix_iff, Finset.mem_cons, mem_prefix_iff, Nat.lt_succ_iff]
  constructor
  · intro h
    obtain h | h := h.eq_or_lt
    · left
      apply e.symm.injective
      simpa only [e.symm_apply_apply] using h
    · exact Or.inr h
  · rintro (rfl | h)
    · rw [e.symm_apply_apply]
    · exact h.le
