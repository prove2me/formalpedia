-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsRescaledConjugate.finiteTimeKernel_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:39:00.369935+00:00
-- url     : https://prove2.me/submissions/2ff8d4dc-3053-4be8-9b98-c21a014e19fa

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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_map_compProd_prodMkLeft_conjugate

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



/-- Rescaled times, evaluated. -/
@[simp]
theorem rescale_apply {n : ℕ} (c : NNReal) (hc : 0 < c) (times : FiniteOrderedTimes n)
    (i : Fin n) : times.rescale c hc i = c * times i :=
  rfl





/-- Rescaling commutes with passing to the relative tail: subtracting the first time and then
scaling is the same as scaling and then subtracting the scaled first time. -/
@[simp]
theorem relativeTail_rescale {n : ℕ} (c : NNReal) (hc : 0 < c)
    (times : FiniteOrderedTimes (n + 1)) :
    (times.rescale c hc).relativeTail = times.relativeTail.rescale c hc := by
  apply DFunLike.ext _ _
  intro i
  simp only [relativeTail_apply, rescale_apply]
  exact (mul_tsub c (times i.succ) (times 0)).symm





/-- The coordinatewise state map is measurable when the state map is. -/
theorem measurable_mapPath {ι alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    {e : alpha → beta} (he : Measurable e) :
    Measurable (mapPath e : (ι → alpha) → ι → beta) :=
  measurable_pi_iff.mpr fun i ↦ he.comp (measurable_pi_apply i)



/-- Prepending a state to a finite path commutes with the coordinatewise state map. -/
theorem mapPath_finCons {n : ℕ} {alpha beta : Type*} (e : alpha → beta)
    (z : alpha × (Fin n → alpha)) :
    mapPath e (@Fin.cons n (fun _ : Fin (n + 1) ↦ alpha) z.1 z.2) =
      @Fin.cons n (fun _ : Fin (n + 1) ↦ beta) (e z.1) (mapPath e z.2) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · rfl

end FiniteOrderedTimes

namespace SubMarkovKernelSemigroup



section CompProd

variable {X X' Y Y' Z Z' : Type*} [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y]
  [MeasurableSpace Y'] [MeasurableSpace Z] [MeasurableSpace Z']

/-- Pulling the source of a composition-product back along a measurable map only affects the first
factor, because a `prodMkLeft` second factor does not read the source. -/
theorem comap_compProd_prodMkLeft (kappa : Kernel X Y) [IsSFiniteKernel kappa]
    (eta : Kernel Y Z) [IsSFiniteKernel eta] {g : X' → X} (hg : Measurable g) :
    Kernel.comap (kappa ⊗ₖ Kernel.prodMkLeft X eta) g hg =
      (Kernel.comap kappa g hg) ⊗ₖ Kernel.prodMkLeft X' eta := by
  ext x s hs
  rw [Kernel.comap_apply', Kernel.compProd_apply hs, Kernel.compProd_apply hs]
  simp only [Kernel.prodMkLeft_apply, Kernel.comap_apply]



end CompProd

section RescaledConjugate

variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [TopologicalSpace beta] [MeasurableSpace beta] [BorelSpace beta]



namespace IsRescaledConjugate

variable {P : SubMarkovKernelSemigroup alpha} {P' : SubMarkovKernelSemigroup beta} {e : alpha ≃ₜ beta}
  {c : NNReal}

/-- The rescaled-conjugacy relation in kernel form: at every time the transition kernel of `P'` is
the transition kernel of `P` at the sped-up time, conjugated by `e`. -/
theorem kernel_eq (h : IsRescaledConjugate P P' e c) (t : NNReal) :
    P' t = (Kernel.comap (P (c * t)) e.symm e.symm.measurable).map e := by
  refine Kernel.ext fun x ↦ ?_
  rw [Kernel.map_apply _ e.measurable, Kernel.comap_apply]
  exact h t x







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
open MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsRescaledConjugate
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








variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [TopologicalSpace beta] [MeasurableSpace beta] [BorelSpace beta]




variable {P : SubMarkovKernelSemigroup alpha} {P' : SubMarkovKernelSemigroup beta} {e : alpha ≃ₜ beta}
  {c : NNReal}





namespace MarkovProcess.SubMarkovKernelSemigroup.IsRescaledConjugate

end MarkovProcess.SubMarkovKernelSemigroup.IsRescaledConjugate
open MarkovProcess.SubMarkovKernelSemigroup.IsRescaledConjugate
theorem solution (h : IsRescaledConjugate P P' e c) (hc : 0 < c)
    (hP : P.IsConservative) :
    ∀ {n : ℕ} (times : FiniteOrderedTimes n),
      finiteTimeKernel P' times =
        (Kernel.comap (finiteTimeKernel P (times.rescale c hc)) e.symm
          e.symm.measurable).map (FiniteOrderedTimes.mapPath e) := by
  intro n
  induction n with
  | zero =>
      intro times
      refine Kernel.ext fun x ↦ ?_
      simp only [finiteTimeKernel_zero]
      rw [Kernel.map_apply _ (FiniteOrderedTimes.measurable_mapPath (ι := Fin 0) e.measurable),
        Kernel.comap_apply, Kernel.const_apply, Kernel.const_apply,
        Measure.map_dirac (FiniteOrderedTimes.emptyPath alpha)]
      congr 1
      exact Subsingleton.elim _ _
  | succ n ih =>
      intro times
      let : IsFiniteKernel (P (c * times 0)) :=
        (P.isSubMarkovKernel (c * times 0)).isFiniteKernel
      let : IsMarkovKernel (finiteTimeKernel P (times.relativeTail.rescale c hc)) :=
        hP.isMarkovKernel_finiteTimeKernel P (times.relativeTail.rescale c hc)
      have hmapn : Measurable
          (FiniteOrderedTimes.mapPath e : (Fin n → alpha) → Fin n → beta) :=
        FiniteOrderedTimes.measurable_mapPath e.measurable
      have hconj : Measurable (fun z : alpha × (Fin n → alpha) ↦
          (e z.1, FiniteOrderedTimes.mapPath e z.2)) :=
        (e.measurable.comp measurable_fst).prodMk (hmapn.comp measurable_snd)
      rw [finiteTimeKernel_succ, finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
        Kernel.mapOfMeasurable_eq_map, FiniteOrderedTimes.relativeTail_rescale,
        FiniteOrderedTimes.rescale_apply,
        Kernel.comap_map_comm _ e.symm.measurable measurable_finCons,
        ← Kernel.map_comp_right _ measurable_finCons
          (FiniteOrderedTimes.measurable_mapPath (ι := Fin (n + 1)) e.measurable),
        show (FiniteOrderedTimes.mapPath e ∘ fun z : alpha × (Fin n → alpha) ↦
              @Fin.cons n (fun _ : Fin (n + 1) ↦ alpha) z.1 z.2) =
            (fun z : beta × (Fin n → beta) ↦
                @Fin.cons n (fun _ : Fin (n + 1) ↦ beta) z.1 z.2) ∘
              (fun z : alpha × (Fin n → alpha) ↦ (e z.1, FiniteOrderedTimes.mapPath e z.2)) from
          funext fun z ↦ FiniteOrderedTimes.mapPath_finCons e z,
        Kernel.map_comp_right _ hconj (measurable_finCons (α := beta)),
        comap_compProd_prodMkLeft _ _ e.symm.measurable,
        map_compProd_prodMkLeft_conjugate _ _ e.measurable e.symm.measurable
          e.symm_apply_apply e.apply_symm_apply hmapn,
        ← h.kernel_eq (times 0), ← ih times.relativeTail]
