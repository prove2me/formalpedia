-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.isKolmogorovProcess_denseTimeTrajectory
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:46:15.017959+00:00
-- url     : https://prove2.me/submissions/a46ea985-afff-4b6f-a8eb-1c7bf1205cf1

import Definitions.Def_MarkovProcess_DenseTime_ConditionalKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixRecursion
import Definitions.Def_MarkovProcess_DenseTime_Trajectory
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KolmogorovMoments_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Definitions.Def_MarkovProcess_Time_DenseTimeHistory
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Kolmogorov
import Theorems.Thm_MarkovProcess_DenseTime_edist_eq_castOrderEmbedding_sub
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_enumeratedDenseTimeTrajectory_map_prefix
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_finiteTimeKernel_map_restrictPath
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_finiteTimeKernel_two_map_pair
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup MarkovProcess.SubMarkovKernelSemigroup.IsConservative
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

namespace MarkovProcess



namespace FiniteOrderedTimes

































/-- Restriction of finite coordinate paths is measurable for product measurable spaces. -/
theorem measurable_restrictPath {m n : ℕ} (e : Fin m ↪o Fin n)
    {α : Type*} [MeasurableSpace α] :
    Measurable (restrictPath e : (Fin n → α) → Fin m → α) :=
  measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (e i)
end FiniteOrderedTimes
end MarkovProcess

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Trajectories on countable dense time

This file transports the finite-history transition kernels to the history carrier used by
Mathlib's Ionescu--Tulcea construction, starts the resulting trajectory at a deterministic state,
and reindexes its positive coordinates by a countable dense-time enumeration.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {D α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]















































omit [StandardBorelSpace α] [Nonempty α] in
/-- Restriction to the first `n` dense-time labels is measurable. -/
theorem measurable_denseTimeTrajectoryPrefix (e : ℕ ≃ D) (n : ℕ) :
    Measurable (denseTimeTrajectoryPrefix (α := α) e n) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_pi_apply (X := fun _ : D ↦ α) (e i)

omit [StandardBorelSpace α] [Nonempty α] in
private theorem denseTimeTrajectoryPrefix_measurableEquivPath
    (e : ℕ ≃ D) (n : ℕ) :
    denseTimeTrajectoryPrefix (α := α) e n ∘
        CountableEnumeration.measurableEquivPath e α =
      enumeratedDenseTimePrefix n := by
  funext path i
  dsimp only [Function.comp_apply, denseTimeTrajectoryPrefix,
    enumeratedDenseTimePrefix]
  exact MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : D ↦ α) e path i

/-- Restricting the dense-time-labelled trajectory to the first `n` enumerated labels gives
exactly the prescribed enumeration-prefix law. -/
theorem denseTimeTrajectory_map_prefix
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    (denseTimeTrajectory P hP e ι).map
        (denseTimeTrajectoryPrefix e n) =
      denseTimePrefixKernel P e ι n := by
  rw [denseTimeTrajectory, ← Kernel.map_comp_right]
  · rw [denseTimeTrajectoryPrefix_measurableEquivPath]
    exact enumeratedDenseTimeTrajectory_map_prefix P hP e ι n
  · exact (CountableEnumeration.measurableEquivPath e α).measurable
  · exact measurable_denseTimeTrajectoryPrefix e n
end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Intrinsic Kolmogorov moment bounds for a transition semigroup

Kolmogorov's continuity criterion is usually imposed on an already constructed coordinate
process.  This file states the same criterion directly on the transition semigroup: the
`p`-th moment of the displacement accumulated over a time step `h` is at most `M * h ^ q`,
uniformly in the starting point.

The predicate is purely a moment bound on the transition kernels.  It makes no path-space,
continuity, or stochastic-process claim; the transport of this bound to the canonical
dense-time coordinate process is proved elsewhere.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [PseudoEMetricSpace alpha] [MeasurableSpace alpha]



namespace HasKolmogorovMoments

variable {P : SubMarkovKernelSemigroup alpha} {p q : ℝ} {M : ℝ≥0}

/-- The moment exponent of a Kolmogorov moment bound is positive. -/
theorem p_pos (hmom : P.HasKolmogorovMoments p q M) : 0 < p :=
  hmom.1

/-- The time exponent of a Kolmogorov moment bound is strictly larger than one. -/
theorem one_lt_q (hmom : P.HasKolmogorovMoments p q M) : 1 < q :=
  hmom.2.1

/-- The time exponent of a Kolmogorov moment bound is positive. -/
theorem q_pos (hmom : P.HasKolmogorovMoments p q M) : 0 < q :=
  lt_trans zero_lt_one hmom.one_lt_q

/-- The displacement moment estimate carried by a Kolmogorov moment bound. -/
theorem lintegral_edist_le (hmom : P.HasKolmogorovMoments p q M) (h : ℝ≥0) (y : alpha) :
    ∫⁻ z, edist z y ^ p ∂(P h y) ≤ M * (h : ℝ≥0∞) ^ q :=
  hmom.2.2 h y
end HasKolmogorovMoments
end SubMarkovKernelSemigroup
end MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Two-point marginals of the dense-time trajectory, and the intrinsic Kolmogorov bridge

The dense-time trajectory of a conservative sub-Markov kernel semigroup already has identified
one-time marginals.  This file identifies its two-time marginals: at dense times whose physical
images satisfy `iota d < iota d'`, the pair `(path d, path d')` has the law obtained by running
`P` for time `iota d` and then, from the state reached, for the increment `iota d' - iota d`.

The identification is then used to discharge the coordinate Kolmogorov hypothesis that every
trajectory theorem of the library assumes.  Under the intrinsic semigroup bound
`SubMarkovKernelSemigroup.HasKolmogorovMoments`, the canonical dense-time coordinate process is a
Kolmogorov process with a positive Hölder exponent below `(q - 1) / p`.

No continuity, modification, Markov-property, or path-regularity statement is proved here; only
the two-point law and the moment estimate it transports.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


noncomputable section











variable {A B C E : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [MeasurableSpace E]

/-- A composition-product whose second factor ignores the starting point is the measure-level
composition-product of the first factor's law with that second factor. -/
private theorem compProd_prodMkLeft_apply (kappa : Kernel A B) [IsSFiniteKernel kappa]
    (eta : Kernel B C) [IsSFiniteKernel eta] (x : A) :
    (kappa ⊗ₖ Kernel.prodMkLeft A eta) x = (kappa x) ⊗ₘ eta := by
  ext s hs
  rw [Kernel.compProd_apply hs, Measure.compProd_apply hs]
  simp only [Kernel.prodMkLeft_apply]





variable {D alpha : Type*} [MeasurableSpace alpha]






variable [StandardBorelSpace alpha] [Nonempty alpha]

private theorem denseTimeTrajectory_map_pair_aux
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) {n : ℕ} (k l : ℕ) (hk : k < n) (hl : l < n)
    (hlt : iota (e k) < iota (e l)) :
    (denseTimeTrajectory P hP e iota).map (fun path ↦ (path (e k), path (e l))) =
      P (iota (e k)) ⊗ₖ Kernel.prodMkLeft alpha (P (iota (e l) - iota (e k))) := by
  classical
  set i : Fin n := ⟨k, hk⟩ with hi
  set j : Fin n := ⟨l, hl⟩ with hj
  have hpair : Measurable (fun path : Fin n → alpha ↦ (path i, path j)) := by fun_prop
  have hstep1 :
      (fun path : Fin n → alpha ↦ (path i, path j)) ∘ denseTimeTrajectoryPrefix e n =
        fun path : D → alpha ↦ (path (e k), path (e l)) := rfl
  rw [← hstep1, Kernel.map_comp_right _ (measurable_denseTimeTrajectoryPrefix e n) hpair,
    denseTimeTrajectory_map_prefix P hP e iota n, denseTimePrefixKernel_eq_map,
    ← Kernel.map_comp_right _ (measurable_denseTimePrefixReindex e iota n) hpair]
  set J : Finset NNReal := denseTimePhysicalPrefix e iota n with hJ
  have hmem : ∀ m : Fin n, iota (e (m : ℕ)) ∈ J := by
    intro m
    rw [hJ, denseTimePhysicalPrefix, Finset.mem_map]
    refine ⟨e (m : ℕ), ?_, rfl⟩
    rw [CountableEnumeration.mem_prefix_iff, e.symm_apply_apply]
    exact m.isLt
  have hstep2 :
      (fun path : Fin n → alpha ↦ (path i, path j)) ∘ denseTimePrefixReindex e iota n =
        fun path : J → alpha ↦
          (path ⟨iota (e (i : ℕ)), hmem i⟩, path ⟨iota (e (j : ℕ)), hmem j⟩) := rfl
  have hpairJ : Measurable (fun path : J → alpha ↦
      (path ⟨iota (e (i : ℕ)), hmem i⟩, path ⟨iota (e (j : ℕ)), hmem j⟩)) := by fun_prop
  rw [hstep2, finiteSetKernel_eq_map,
    ← Kernel.map_comp_right _ (measurable_orderedPathToFiniteSet J) hpairJ]
  set a : Fin J.card := (J.orderIsoOfFin rfl).symm ⟨iota (e (i : ℕ)), hmem i⟩ with ha
  set b : Fin J.card := (J.orderIsoOfFin rfl).symm ⟨iota (e (j : ℕ)), hmem j⟩ with hb
  have hstep3 :
      (fun path : J → alpha ↦
          (path ⟨iota (e (i : ℕ)), hmem i⟩, path ⟨iota (e (j : ℕ)), hmem j⟩)) ∘
            orderedPathToFiniteSet J =
        fun path : Fin J.card → alpha ↦ (path a, path b) := rfl
  rw [hstep3]
  have hab : a < b := by
    rw [ha, hb, OrderIso.lt_iff_lt, Subtype.mk_lt_mk]
    exact hlt
  set select : Fin 2 ↪o Fin J.card :=
    OrderEmbedding.ofStrictMono (fun m ↦ if m = 0 then a else b) (by
      rw [Fin.strictMono_iff_lt_succ]
      intro m
      have hm : m = 0 := Subsingleton.elim m 0
      subst hm
      simpa only [Fin.castSucc_zero, if_pos rfl, Fin.succ_zero_eq_one] using! hab) with hselect
  have hpair2 : Measurable (fun path : Fin 2 → alpha ↦ (path 0, path 1)) := by fun_prop
  have hstep4 :
      (fun path : Fin 2 → alpha ↦ (path 0, path 1)) ∘
          FiniteOrderedTimes.restrictPath select =
        fun path : Fin J.card → alpha ↦ (path a, path b) := rfl
  rw [← hstep4,
    Kernel.map_comp_right _ (FiniteOrderedTimes.measurable_restrictPath select) hpair2,
    hP.finiteTimeKernel_map_restrictPath P (finiteSetTimes J) select,
    finiteTimeKernel_two_map_pair P hP]
  have hta : ((finiteSetTimes J).restrict select) 0 = iota (e k) := by
    change ((((J.orderIsoOfFin rfl) a) : J) : NNReal) = iota (e k)
    rw [ha, OrderIso.apply_symm_apply]
  have htb : ((finiteSetTimes J).restrict select) 1 = iota (e l) := by
    change ((((J.orderIsoOfFin rfl) b) : J) : NNReal) = iota (e l)
    rw [hb, OrderIso.apply_symm_apply]
  rw [hta, htb]

/-- The two-time marginal of the dense-time trajectory: at dense labels whose physical times are
strictly ordered, the pair of coordinates has the law of `P` run for the first physical time and
then, from the state reached, for the increment to the second physical time. -/
theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory_map_pair
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) {d d' : D} (hlt : iota d < iota d') :
    (denseTimeTrajectory P hP e iota).map (fun path ↦ (path d, path d')) =
      P (iota d) ⊗ₖ Kernel.prodMkLeft alpha (P (iota d' - iota d)) := by
  have hd : e (e.symm d) = d := e.apply_symm_apply d
  have hd' : e (e.symm d') = d' := e.apply_symm_apply d'
  have hpair := denseTimeTrajectory_map_pair_aux P hP e iota
    (n := max (e.symm d) (e.symm d') + 1) (e.symm d) (e.symm d')
    (Nat.lt_succ_of_le (le_max_left _ _)) (Nat.lt_succ_of_le (le_max_right _ _))
    (by rw [hd, hd']; exact hlt)
  rwa [hd, hd'] at hpair




variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [StandardBorelSpace alpha] [Nonempty alpha]


private theorem lintegral_edist_le_of_lt
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    {p q : ℝ} {M : ℝ≥0} (hmom : P.HasKolmogorovMoments p q M) (x : alpha)
    {s t : DenseTime} (hst : s < t) :
    ∫⁻ omega, edist (omega s) (omega t) ^ p
        ∂(denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) ≤ M * edist s t ^ q := by
  set iota : DenseTime ↪ NNReal := DenseTime.castOrderEmbedding.toEmbedding with hiota
  have hlt : iota s < iota t := DenseTime.castOrderEmbedding.strictMono hst
  set Delta : NNReal := iota t - iota s with hDelta
  let : IsFiniteKernel (P (iota s)) := (P.isSubMarkovKernel (iota s)).isFiniteKernel
  let : IsFiniteKernel (P Delta) := (P.isSubMarkovKernel Delta).isFiniteKernel
  have hF : Measurable (fun z : alpha × alpha ↦ edist z.1 z.2 ^ p) :=
    measurable_edist.pow_const p
  have hev : Measurable (fun omega : DenseTime → alpha ↦ (omega s, omega t)) := by fun_prop
  have hmapint :
      ∫⁻ z, edist z.1 z.2 ^ p
          ∂((denseTimeTrajectory P hP DenseTime.enumeration iota x).map
            (fun omega ↦ (omega s, omega t))) =
        ∫⁻ omega, edist (omega s) (omega t) ^ p
          ∂(denseTimeTrajectory P hP DenseTime.enumeration iota x) :=
    lintegral_map hF hev
  have hlaw :
      (denseTimeTrajectory P hP DenseTime.enumeration iota x).map
          (fun omega ↦ (omega s, omega t)) = (P (iota s) x) ⊗ₘ P Delta := by
    rw [← Kernel.map_apply _ hev,
      denseTimeTrajectory_map_pair P hP DenseTime.enumeration iota hlt,
      compProd_prodMkLeft_apply]
  have hinner : ∀ y : alpha,
      ∫⁻ z, edist y z ^ p ∂(P Delta y) ≤ (M : ℝ≥0∞) * (Delta : ℝ≥0∞) ^ q := by
    intro y
    have hcongr : ∫⁻ z, edist y z ^ p ∂(P Delta y) = ∫⁻ z, edist z y ^ p ∂(P Delta y) :=
      lintegral_congr fun z ↦ by rw [edist_comm]
    rw [hcongr]
    exact hmom.lintegral_edist_le Delta y
  rw [← hmapint, hlaw, Measure.lintegral_compProd hF]
  calc ∫⁻ y, ∫⁻ z, edist y z ^ p ∂(P Delta y) ∂(P (iota s) x)
      ≤ ∫⁻ _, (M : ℝ≥0∞) * (Delta : ℝ≥0∞) ^ q ∂(P (iota s) x) := lintegral_mono hinner
    _ = (M : ℝ≥0∞) * (Delta : ℝ≥0∞) ^ q := by
        rw [lintegral_const, hP (iota s) x, mul_one]
    _ = (M : ℝ≥0∞) * edist s t ^ q := by
        rw [DenseTime.edist_eq_castOrderEmbedding_sub hst.le]
        rfl


theorem solution
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    {p q : ℝ} {M : ℝ≥0} (hmom : P.HasKolmogorovMoments p q M) (x : alpha) :
    IsKolmogorovProcess (fun r omega ↦ omega r)
      (denseTimeTrajectory P hP DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding x) p q M := by
  refine IsKolmogorovProcess.mk_of_secondCountableTopology
    (fun r ↦ measurable_pi_apply r) ?_ hmom.p_pos hmom.q_pos
  intro s t
  rcases lt_trichotomy s t with hst | hst | hst
  · exact lintegral_edist_le_of_lt P hP hmom x hst
  · subst hst
    simp only [edist_self, ENNReal.zero_rpow_of_pos hmom.p_pos, lintegral_zero]
    exact zero_le
  · have hsym := lintegral_edist_le_of_lt P hP hmom x hst
    have hcongr :
        ∫⁻ omega, edist (omega s) (omega t) ^ p
            ∂(denseTimeTrajectory P hP DenseTime.enumeration
              DenseTime.castOrderEmbedding.toEmbedding x) =
          ∫⁻ omega, edist (omega t) (omega s) ^ p
            ∂(denseTimeTrajectory P hP DenseTime.enumeration
              DenseTime.castOrderEmbedding.toEmbedding x) :=
      lintegral_congr fun omega ↦ by rw [edist_comm]
    rw [hcongr, edist_comm s t]
    exact hsym
