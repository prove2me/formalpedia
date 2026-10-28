-- Prove2me | solution 1 for MarkovProcess.tendstoUniformly_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T07:41:08.437501+00:00
-- url     : https://prove2.me/submissions/71c0c6b0-6493-472d-8b1d-40909b25cfb8

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

theorem solution {F G : iota → beta → ℝ} {f g : beta → ℝ}
    (hf : TendstoUniformly F f l) (hg : TendstoUniformly G g l) :
    TendstoUniformly (fun i x ↦ F i x + G i x) (fun x ↦ f x + g x) l :=
  hf.add hg
