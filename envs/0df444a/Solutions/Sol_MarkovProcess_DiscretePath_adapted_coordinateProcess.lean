-- Prove2me | solution 1 for MarkovProcess.DiscretePath.adapted_coordinateProcess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:46:29.938991+00:00
-- url     : https://prove2.me/submissions/0eb0ba22-aff2-42ec-aebc-493109ccc4bd

import Definitions.Def_MarkovProcess_V3H_DenseTime_CanonicalDiscretePath_a2b715fb
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Canonical discrete path space

This file records the elementary measurable and filtered structure on the
discrete path space `ℕ → α`.  It does not equip paths with a probability law or
assert any Markov property.

## Main definitions

* `DiscretePath`: the canonical space of `α`-valued discrete paths.
* `DiscretePath.coordinate`: evaluation of a path at one time.
* `DiscretePath.coordinateProcess`: the canonical coordinate process.
* `DiscretePath.canonicalFiltration`: the natural filtration of the coordinate process.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open TopologicalSpace

namespace MarkovProcess



namespace DiscretePath

variable {α : Type*}









section Measurable

variable [MeasurableSpace α]





end Measurable

section NaturalFiltration

variable [TopologicalSpace α]
variable [MetrizableSpace α]
variable [MeasurableSpace α]
variable [BorelSpace α]
variable [SecondCountableTopology α]











end NaturalFiltration

end DiscretePath

end MarkovProcess


open MarkovProcess
open MarkovProcess.DiscretePath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Canonical discrete path space

This file records the elementary measurable and filtered structure on the
discrete path space `ℕ → α`.  It does not equip paths with a probability law or
assert any Markov property.

## Main definitions

* `DiscretePath`: the canonical space of `α`-valued discrete paths.
* `DiscretePath.coordinate`: evaluation of a path at one time.
* `DiscretePath.coordinateProcess`: the canonical coordinate process.
* `DiscretePath.canonicalFiltration`: the natural filtration of the coordinate process.
-/

open MeasureTheory
open TopologicalSpace





variable {α : Type*}











variable [TopologicalSpace α]
variable [MetrizableSpace α]
variable [MeasurableSpace α]
variable [BorelSpace α]
variable [SecondCountableTopology α]









namespace MarkovProcess.DiscretePath

end MarkovProcess.DiscretePath
open MarkovProcess.DiscretePath
theorem solution :
    Adapted (canonicalFiltration (α := α)) (coordinateProcess (α := α)) := by
  exact (Filtration.stronglyAdapted_natural
    (u := coordinateProcess (α := α)) stronglyMeasurable_coordinateProcess).adapted
