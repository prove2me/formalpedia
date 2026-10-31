-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.measurableSet_modulusSet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:31:18.21411+00:00
-- url     : https://prove2.me/submissions/7b02448a-d341-4df6-a586-b2d849ebdfb8

import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicChaining_a582e42e
import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicPathChaining_e74fe8f3
import Definitions.Def_MarkovProcess_V3H_Continuity_PathModulus_4f3af818
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.EMetricSpace.Basic

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# A quantitative modulus of continuity from a Kolmogorov moment bound

The Kolmogorov--Chentsov argument is usually stated as an almost-sure Hölder property of a
continuous modification.  This file records the *quantitative* form that a tightness argument
needs: for a probability law on continuous paths whose coordinate process satisfies the
Kolmogorov moment condition with exponents `p`, `q` and constant `M`, the mass of the paths that
oscillate by more than `r` at scale `delta` on `[0, T]` is at most `eps`, once `delta` is small
enough --- and the threshold `delta` depends only on `p`, `q`, `M`, the Hölder exponent, `T`,
`r` and `eps`, not on the law.  This uniformity is the whole point: it is what makes the estimate
usable simultaneously at every starting point of a Markov process.

Main results:

* `MarkovProcess.ContinuousPath.modulusSet`, the closed set of paths whose oscillation over
  `[0, T]` at scale `delta` is at most `r`, with `isClosed_modulusSet` and
  `measurableSet_modulusSet`;
* `MarkovProcess.ContinuousPath.exists_measure_compl_modulusSet_le`, the quantitative estimate,
  uniform over all laws obeying one and the same moment bound.

Nothing here constructs a law, asserts a Hölder exponent for individual paths, or claims
tightness; tightness is assembled from this estimate elsewhere.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoEMetricSpace alpha]





theorem isClosed_modulusSet (T : ℝ≥0) (delta r : ℝ≥0∞) :
    IsClosed (modulusSet (alpha := alpha) T delta r) := by
  have hrewrite : modulusSet (alpha := alpha) T delta r =
      ⋂ s : ℝ≥0, ⋂ t : ℝ≥0, ⋂ _ : s ≤ T, ⋂ _ : t ≤ T, ⋂ _ : edist s t ≤ delta,
        {omega : ContinuousPath alpha | edist (omega s) (omega t) ≤ r} := by
    ext omega
    simp only [modulusSet, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hrewrite]
  refine isClosed_iInter fun s ↦ isClosed_iInter fun t ↦ isClosed_iInter fun _ ↦
    isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦ ?_
  exact isClosed_le ((continuous_eval (alpha := alpha) s).edist (continuous_eval t))
    continuous_const



end ContinuousPath

section Estimate

variable {alpha : Type*} [PseudoEMetricSpace alpha]



















end Estimate

end MarkovProcess


open MarkovProcess
open MarkovProcess.ContinuousPath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# A quantitative modulus of continuity from a Kolmogorov moment bound

The Kolmogorov--Chentsov argument is usually stated as an almost-sure Hölder property of a
continuous modification.  This file records the *quantitative* form that a tightness argument
needs: for a probability law on continuous paths whose coordinate process satisfies the
Kolmogorov moment condition with exponents `p`, `q` and constant `M`, the mass of the paths that
oscillate by more than `r` at scale `delta` on `[0, T]` is at most `eps`, once `delta` is small
enough --- and the threshold `delta` depends only on `p`, `q`, `M`, the Hölder exponent, `T`,
`r` and `eps`, not on the law.  This uniformity is the whole point: it is what makes the estimate
usable simultaneously at every starting point of a Markov process.

Main results:

* `MarkovProcess.ContinuousPath.modulusSet`, the closed set of paths whose oscillation over
  `[0, T]` at scale `delta` is at most `r`, with `isClosed_modulusSet` and
  `measurableSet_modulusSet`;
* `MarkovProcess.ContinuousPath.exists_measure_compl_modulusSet_le`, the quantitative estimate,
  uniform over all laws obeying one and the same moment bound.

Nothing here constructs a law, asserts a Hölder exponent for individual paths, or claims
tightness; tightness is assembled from this estimate elsewhere.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal



variable {alpha : Type*} [PseudoEMetricSpace alpha]







namespace MarkovProcess.ContinuousPath
end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath
theorem solution (T : ℝ≥0) (delta r : ℝ≥0∞) :
    MeasurableSet (modulusSet (alpha := alpha) T delta r) :=
  (isClosed_modulusSet T delta r).measurableSet
