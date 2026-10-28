-- Prove2me | solution 1 for MarkovProcess.tendstoUniformly_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T07:40:58.819906+00:00
-- url     : https://prove2.me/submissions/d4f53857-c28c-45ea-80d7-bc924afdb89f

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators CompactlySupported
variable {beta : Type*} {iota : Type*} {l : Filter iota}

theorem solution (c : ℝ) :
    TendstoUniformly (fun (_ : iota) (_ : beta) ↦ c) (fun _ ↦ c) l :=
  tendstoUniformlyOn_univ.mp (tendsto_const_nhds.tendstoUniformlyOn_const Set.univ)
