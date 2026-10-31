-- Prove2me | solution 1 for MarkovProcess.DenseTimePath.pullbackAddFinset_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:45:08.723406+00:00
-- url     : https://prove2.me/submissions/81eb54bf-02d0-4eca-9510-2d4eb68c6eee

import Definitions.Def_MarkovProcess_V3H_DenseTime_Shift_b3e2f7d9
import Definitions.Def_MarkovProcess_V3H_FiniteTime_DenseTimeFiniteShift_11c70184
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
# Finite-coordinate shifts on dense-time paths

Addition by a dense time transports finite sets of dense-time coordinates injectively.  This file
provides the resulting coordinate equivalence and relates restriction after shifting a dense-time
path to restriction on the translated finite set.  It makes no probability-law or Markov claim.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

namespace MarkovProcess

noncomputable section

namespace DenseTime









end DenseTime

namespace DenseTimePath

variable {alpha : Type*}





variable [MeasurableSpace alpha]





end DenseTimePath
end
end MarkovProcess


open MarkovProcess
open MarkovProcess.DenseTimePath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-coordinate shifts on dense-time paths

Addition by a dense time transports finite sets of dense-time coordinates injectively.  This file
provides the resulting coordinate equivalence and relates restriction after shifting a dense-time
path to restriction on the translated finite set.  It makes no probability-law or Markov claim.
-/





variable {alpha : Type*}



namespace MarkovProcess.DenseTimePath
end MarkovProcess.DenseTimePath
open MarkovProcess.DenseTimePath
@[simp]
theorem solution (s : DenseTime) (I : Finset DenseTime)
    (path : DenseTime.addFinset s I → alpha) (t : I) :
    pullbackAddFinset s I path t = path (DenseTime.addFinsetEquiv s I t) := rfl
