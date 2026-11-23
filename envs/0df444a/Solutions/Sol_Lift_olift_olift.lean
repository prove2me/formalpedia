-- Prove2me | solution 1 for Lift.olift_olift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:01:45.286337+00:00
-- url     : https://prove2.me/submissions/03fbfb95-b667-4b6c-a582-0b5fb0b20a41

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Lift
import Theorems.Thm_Lift_olift_evaluate
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const


attribute [local simp] Lift.olift_evaluate

set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered
open Lift
attribute [local implicit_reducible] olift
namespace Lift
theorem _root_.solution {h1 : n ≤ n'} {h2 : n' ≤ n''} {O : OBdd n m} : olift h2 (olift h1 O) = olift (.trans h1 h2) O := by
  simp only [olift, lift, Vector.map_map]
  congr
end Lift
