-- Prove2me | solution 1 for MarkovProcess.tendstoUniformly_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T07:41:03.653372+00:00
-- url     : https://prove2.me/submissions/bb4155df-4e3e-4dee-ad23-2ad64ba09940

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

theorem solution {F : iota → beta → ℝ} {f : beta → ℝ}
    (h : TendstoUniformly F f l) (c : ℝ) :
    TendstoUniformly (fun i x ↦ c * F i x) (fun x ↦ c * f x) l :=
  (uniformContinuous_const_smul c).comp_tendstoUniformly h
