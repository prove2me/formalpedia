-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.progMeasurable_coordinateProcess
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:49:13.588839+00:00
-- url     : https://prove2.me/submissions/206f4cbd-07de-467d-80bc-ccffe161085f

import Mathlib.Probability.Process.Stopping
import Definitions.Def_MarkovProcess_ContinuousPath
open MeasureTheory MarkovProcess MarkovProcess.ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha]
  [TopologicalSpace.PseudoMetrizableSpace alpha]
  [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]

theorem solution :
    IsStronglyProgressive (canonicalFiltration (alpha := alpha))
      (coordinateProcess (alpha := alpha)) :=
  StronglyAdapted.isStronglyProgressive_of_continuous
    (fun t => (measurable_coordinateProcess_canonicalFiltration t).stronglyMeasurable)
    (fun ω => ω.continuous)
