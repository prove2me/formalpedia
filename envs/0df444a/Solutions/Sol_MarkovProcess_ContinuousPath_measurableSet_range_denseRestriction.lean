-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.measurableSet_range_denseRestriction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:31:25.801764+00:00
-- url     : https://prove2.me/submissions/02e36241-4617-4d32-8829-a08b17333294

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuous extension from dense-time paths

This file embeds ordinary continuous paths into paths on the fixed dense time carrier. It proves
that the image is measurable and supplies a measurable total inverse. The inverse is the genuine
continuous extension on the image and is arbitrarily equal to a caller-supplied default path away
from the image.

No probability law is shown to be supported on this image, and no continuous modification,
stochastic-process association, or path-regularity claim is made here.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

namespace MarkovProcess

noncomputable section

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

















section Measurable

variable [MeasurableSpace alpha] [BorelSpace alpha]



variable [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]







end Measurable
end ContinuousPath
end
end MarkovProcess


open MarkovProcess
open MarkovProcess.ContinuousPath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuous extension from dense-time paths

This file embeds ordinary continuous paths into paths on the fixed dense time carrier. It proves
that the image is measurable and supplies a measurable total inverse. The inverse is the genuine
continuous extension on the image and is arbitrarily equal to a caller-supplied default path away
from the image.

No probability law is shown to be supported on this image, and no continuous modification,
stochastic-process association, or path-regularity claim is made here.
-/

open MeasureTheory Set




variable {alpha : Type*} [TopologicalSpace alpha]


















variable [MeasurableSpace alpha] [BorelSpace alpha]



variable [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]



namespace MarkovProcess.ContinuousPath

end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath
theorem solution :
    MeasurableSet (Set.range (denseRestriction (alpha := alpha))) :=
  measurableEmbedding_denseRestriction.measurableSet_range
