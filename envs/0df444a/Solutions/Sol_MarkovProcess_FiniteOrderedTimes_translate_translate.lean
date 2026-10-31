-- Prove2me | solution 1 for MarkovProcess.FiniteOrderedTimes.translate_translate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:51:11.14887+00:00
-- url     : https://prove2.me/submissions/1fa8c885-1624-43ff-95b8-ca57abc576c7

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
theorem solution {n : ℕ} (s r : NNReal) (times : FiniteOrderedTimes n) :
    (times.translate r).translate s = times.translate (s + r) := by
  apply DFunLike.ext _ _
  intro i
  exact (add_assoc s r (times i)).symm
