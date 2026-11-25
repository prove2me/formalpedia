-- Prove2me | solution 1 for GroundTheory.Global.card_primesOver_le_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:02.92183+00:00
-- url     : https://prove2.me/submissions/3b1c59f9-c6ef-4ab7-94d4-8bace455ba6d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set
noncomputable section
namespace GroundTheory.Global
theorem _root_.solution {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [Algebra R S] [Module.Finite R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime]
    [Finite (p.primesOver S)] :
    Nat.card (p.primesOver S) ≤ Module.finrank R S := by
  classical
  let _ := Fintype.ofFinite (p.primesOver S)
  rw [← Ideal.sum_ramification_inertia_eq_finrank p S, Nat.card_eq_fintype_card,
    Fintype.card_eq_sum_ones]
  refine Finset.sum_le_sum fun q _ => ?_
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 R).ne' (Ideal.inertiaDeg_pos q.1 R).ne')
end GroundTheory.Global
