-- Prove2me | solution 1 for MarkovProcess.ParameterizedSubMarkovKernelSemigroup.parameterizedDenseTimeTrajectory_map_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T17:21:37.132978+00:00
-- url     : https://prove2.me/submissions/c1185a05-b4a6-44f3-829e-79fb53ef8cd7

import Definitions.Def_MarkovProcess_V3H_Parameterized_DenseTimeTrajectory_d8dd1c30

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

open MarkovProcess MarkovProcess.ParameterizedSubMarkovKernelSemigroup

noncomputable section

universe uTheta uAlpha

variable {Theta : Type uTheta} {D : Type*} {alpha : Type uAlpha}
  [MeasurableSpace Theta] [MeasurableSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

/-- Source-faithful proof reused from the fully proved Definition-embedded original. -/
theorem solution
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (n : ℕ) :
    (P.parameterizedDenseTimeTrajectory hP e iota).map
        (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix e n) =
      P.parameterizedDenseTimePrefixKernel e iota n := by
  exact p2m_embedded_c425cb990d127140 P hP e iota n

end
