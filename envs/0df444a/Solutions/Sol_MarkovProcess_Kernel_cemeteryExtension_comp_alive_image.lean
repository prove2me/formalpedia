-- Prove2me | solution 1 for MarkovProcess.Kernel.cemeteryExtension_comp_alive_image
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:51:59.526984+00:00
-- url     : https://prove2.me/submissions/1f915d2b-327a-4500-b2b0-aca9efa42a02

import Definitions.Def_MarkovProcess_V3H_DenseTime_CemeteryExtension_b0b7bd17
import Definitions.Def_MarkovProcess_V3H_DenseTime_CemeterySemigroup_149c26e5
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Topology.Constructions.SumProd

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Cemetery extensions of sub-Markov kernel semigroups

This file shows that conservative cemetery extension preserves the identity
kernel and composition of sub-Markov kernels.  Consequently, applying the
extension at every time turns any sub-Markov kernel semigroup into a
conservative semigroup on the cemetery state space.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

namespace Kernel







end Kernel

namespace SubMarkovKernelSemigroup



variable (P : SubMarkovKernelSemigroup α)







end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.Kernel
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Cemetery extensions of sub-Markov kernel semigroups

This file shows that conservative cemetery extension preserves the identity
kernel and composition of sub-Markov kernels.  Consequently, applying the
extension at every time turns any sub-Markov kernel semigroup into a
conservative semigroup on the cemetery state space.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal



variable {α : Type*} [MeasurableSpace α]




namespace MarkovProcess.Kernel

end MarkovProcess.Kernel
open MarkovProcess.Kernel
theorem solution (η κ : Kernel α α)
    (x : α) {s : Set α} (hs : MeasurableSet s) :
    cemeteryExtension (η.comp κ) (Cemetery.alive x) (Cemetery.alive '' s) =
      ((cemeteryExtension η).comp (cemeteryExtension κ))
        (Cemetery.alive x) (Cemetery.alive '' s) := by
  rw [cemeteryExtension_alive_image _ x hs, Kernel.comp_apply' _ _ _ hs.inl_image,
    cemeteryExtension_alive_apply, lintegral_add_measure,
    lintegral_map ((cemeteryExtension η).measurable_coe hs.inl_image) measurable_inl]
  have hnot : Cemetery.delta ∉ Cemetery.alive '' s := by
    rintro ⟨a, -, h⟩
    exact Sum.inl_ne_inr h
  simp only [cemeteryExtension_alive_image _ _ hs, lintegral_smul_measure]
  rw [MeasureTheory.lintegral_dirac' Cemetery.delta
    ((cemeteryExtension η).measurable_coe hs.inl_image)]
  rw [cemeteryExtension_delta_apply' _ hs.inl_image, Set.indicator_of_notMem hnot,
    smul_zero, add_zero]
  rw [Kernel.comp_apply' _ _ _ hs]
