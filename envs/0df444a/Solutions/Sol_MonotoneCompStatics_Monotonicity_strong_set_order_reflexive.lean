-- Prove2me | solution 1 for MonotoneCompStatics.Monotonicity.strong_set_order_reflexive
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:26:45.39844+00:00
-- url     : https://prove2.me/submissions/45624728-b285-4cac-810e-0c0a15555dd1

import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_MonotoneCompStatics_Monotonicity_argmaxOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_ArgmaxMonotone
import Definitions.Def_MonotoneCompStatics_Monotonicity_SingleCrossing
import Definitions.Def_MonotoneCompStatics_Monotonicity_StrictSingleCrossing

open MonotoneCompStatics.Monotonicity Supermodularity.Lattices


theorem solution {X : Type*} [Lattice X] (S : Set X) :
    Supermodularity.Lattices.InducedSetOrder S S ↔ IsSublattice S := by
  constructor
  · intro h
    exact ⟨fun a ha b hb => (h ha hb).2, fun a ha b hb => (h ha hb).1⟩
  · intro h a ha b hb
    exact ⟨h.infClosed ha hb, h.supClosed ha hb⟩

#print axioms solution
