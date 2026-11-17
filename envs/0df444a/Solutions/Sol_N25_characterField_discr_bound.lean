-- Prove2me | solution 1 for N25.characterField_discr_bound
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:02.247214+00:00
-- url     : https://prove2.me/submissions/d2be6fe4-f7bb-4a15-8c69-939a07ff90a5

import Mathlib
import Definitions.Def_N25_CharacterField
import Theorems.Thm_N25_characterField_degree_and_totallyReal
import Definitions.Def_N25
import Theorems.Thm_NumberField_natAbs_discr_le_of_quintic_subfield_cyclotomic

set_option autoImplicit false

noncomputable section

namespace N25

/-- The actual H25-fixed field satisfies the discriminant bound needed for
its Minkowski ideal cover. -/
theorem _root_.solution :
    (NumberField.discr characterField).natAbs ≤ 5 ^ 8 := by
  exact NumberField.natAbs_discr_le_of_quintic_subfield_cyclotomic
    characterField cyclotomicField characterField_degree_and_totallyReal.1

end N25
