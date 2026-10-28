-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.adapted_coordinateProcess
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:43:14.951483+00:00
-- url     : https://prove2.me/submissions/519675f8-5a38-4d10-9f49-b5dbe7d59208

import Mathlib.Probability.Process.Stopping
import Definitions.Def_MarkovProcess_ContinuousPath
open MeasureTheory MarkovProcess MarkovProcess.ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha]
  [TopologicalSpace.PseudoMetrizableSpace alpha]
  [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]

theorem solution :
    StronglyAdapted (canonicalFiltration (alpha := alpha)) (coordinateProcess (alpha := alpha)) :=
  fun t => (measurable_coordinateProcess_canonicalFiltration t).stronglyMeasurable
