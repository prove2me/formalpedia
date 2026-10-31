-- Prove2me | solution 1 for MarkovProcess.FiniteOrderedTimes.restrictPath_empty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:50:57.502198+00:00
-- url     : https://prove2.me/submissions/72136c19-f3cc-40d0-9067-e8987a9bbe61

import Definitions.Def_MarkovProcess_V3H_Time_FiniteOrderedTimes_717796dd
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite ordered time families

This file provides increasing finite families of nonnegative times and the elementary operations
for restricting such families and their coordinate paths along order embeddings.  It is an
ordinary finite-dimensional API and makes no probability-law or stochastic-process claim.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

namespace MarkovProcess



namespace FiniteOrderedTimes









































end FiniteOrderedTimes

end MarkovProcess


open MarkovProcess
open MarkovProcess.FiniteOrderedTimes
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite ordered time families

This file provides increasing finite families of nonnegative times and the elementary operations
for restricting such families and their coordinate paths along order embeddings.  It is an
ordinary finite-dimensional API and makes no probability-law or stochastic-process claim.
-/











































namespace MarkovProcess.FiniteOrderedTimes

end MarkovProcess.FiniteOrderedTimes
open MarkovProcess.FiniteOrderedTimes
@[simp]
theorem solution {n : ℕ} (e : Fin 0 ↪o Fin n) {α : Type*}
    (path : Fin n → α) : restrictPath e path = emptyPath α :=
  Subsingleton.elim _ _
