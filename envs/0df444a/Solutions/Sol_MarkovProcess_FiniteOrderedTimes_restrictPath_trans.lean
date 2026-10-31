-- Prove2me | solution 1 for MarkovProcess.FiniteOrderedTimes.restrictPath_trans
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:51:03.862115+00:00
-- url     : https://prove2.me/submissions/61a9cd1d-becf-43d7-87bc-606e0aef69aa

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
theorem solution {k m n : ℕ} (e : Fin m ↪o Fin n) (d : Fin k ↪o Fin m)
    {α : Type*} (path : Fin n → α) :
    restrictPath d (restrictPath e path) = restrictPath (d.trans e) path :=
  rfl
