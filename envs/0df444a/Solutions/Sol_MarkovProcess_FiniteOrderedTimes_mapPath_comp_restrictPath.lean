-- Prove2me | solution 1 for MarkovProcess.FiniteOrderedTimes.mapPath_comp_restrictPath
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:50:44.635688+00:00
-- url     : https://prove2.me/submissions/01c0c08b-4195-4b63-a610-5aa6ef7d3951

import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelEquivariance_10113825
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Definitions.Def_MarkovProcess_V3H_Kernel_KolmogorovMoments_9b991370
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Rescaled conjugation of finite-time kernels

A sub-Markov kernel semigroup `P'` on a state space `beta` is the *rescaled conjugate* of `P` on
`alpha` when it is obtained from `P` by conjugating the state with a homeomorphism `e : alpha ≃ₜ beta`
and speeding time up by a positive factor `c`, that is `P' t x = ((P (c * t)) (e.symm x)).map e`.

This file transfers the finite-dimensional laws across such a relation.  The main result is
`SubMarkovKernelSemigroup.IsRescaledConjugate.finiteTimeKernel_eq`, which computes every
finite-time kernel of `P'` from the finite-time kernel of `P` at the rescaled times.  Supporting
API: the time-scaling operation `FiniteOrderedTimes.rescale`, the coordinatewise state map
`FiniteOrderedTimes.mapPath`, and two composition-product lemmas, `comap_compProd_prodMkLeft` and
`map_compProd_prodMkLeft_conjugate`, which have no direct Mathlib counterpart.

Nothing here mentions path space; the path-space equivariance statement is in
`MarkovProcess/Trajectory/Equivariance.lean`.  When the state map is an isometry, the intrinsic
Kolmogorov moment criterion also transfers, with the constant multiplied by `c ^ q`
(`IsRescaledConjugate.hasKolmogorovMoments`).
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace MarkovProcess

namespace FiniteOrderedTimes





















end FiniteOrderedTimes

namespace SubMarkovKernelSemigroup



section CompProd

variable {X X' Y Y' Z Z' : Type*} [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y]
  [MeasurableSpace Y'] [MeasurableSpace Z] [MeasurableSpace Z']





end CompProd

section RescaledConjugate

variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [TopologicalSpace beta] [MeasurableSpace beta] [BorelSpace beta]



namespace IsRescaledConjugate

variable {P : SubMarkovKernelSemigroup alpha} {P' : SubMarkovKernelSemigroup beta} {e : alpha ≃ₜ beta}
  {c : NNReal}









end IsRescaledConjugate

section Moments

variable {alpha beta : Type*} [PseudoEMetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [PseudoEMetricSpace beta] [MeasurableSpace beta] [BorelSpace beta]
variable {P : SubMarkovKernelSemigroup alpha} {P' : SubMarkovKernelSemigroup beta} {e : alpha ≃ₜ beta}
  {c : NNReal}



end Moments

end RescaledConjugate

end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.FiniteOrderedTimes
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Rescaled conjugation of finite-time kernels

A sub-Markov kernel semigroup `P'` on a state space `beta` is the *rescaled conjugate* of `P` on
`alpha` when it is obtained from `P` by conjugating the state with a homeomorphism `e : alpha ≃ₜ beta`
and speeding time up by a positive factor `c`, that is `P' t x = ((P (c * t)) (e.symm x)).map e`.

This file transfers the finite-dimensional laws across such a relation.  The main result is
`SubMarkovKernelSemigroup.IsRescaledConjugate.finiteTimeKernel_eq`, which computes every
finite-time kernel of `P'` from the finite-time kernel of `P` at the rescaled times.  Supporting
API: the time-scaling operation `FiniteOrderedTimes.rescale`, the coordinatewise state map
`FiniteOrderedTimes.mapPath`, and two composition-product lemmas, `comap_compProd_prodMkLeft` and
`map_compProd_prodMkLeft_conjugate`, which have no direct Mathlib counterpart.

Nothing here mentions path space; the path-space equivariance statement is in
`MarkovProcess/Trajectory/Equivariance.lean`.  When the state map is an isometry, the intrinsic
Kolmogorov moment criterion also transfers, with the constant multiplied by `c ^ q`
(`IsRescaledConjugate.hasKolmogorovMoments`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory



















namespace MarkovProcess.FiniteOrderedTimes

end MarkovProcess.FiniteOrderedTimes
open MarkovProcess.FiniteOrderedTimes
theorem solution {m n : ℕ} (d : Fin m ↪o Fin n) {alpha beta : Type*}
    (e : alpha → beta) :
    mapPath e ∘ (restrictPath d : (Fin n → alpha) → Fin m → alpha) =
      restrictPath d ∘ mapPath e :=
  rfl
