-- Prove2me | solution 1 for ModularCurve.finite_componentGroup_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/5e1aa1ca-38ea-52b6-be22-d36795a47165

import Definitions.Def_ModularCurve_ComponentGroup
import Theorems.Thm_ModularCurve_natCard_componentGroup_eq_kirchhoffCount
import Theorems.Thm_ModularCurve_componentGroup_subsingleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finite_componentGroup_of_pos

set_option autoImplicit false

open ModularCurve in
theorem solution {ι : Type*} [Fintype ι] (e : ι → ℕ)
    (he : ∀ x, 0 < e x) : Finite (componentGroup e) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI : Subsingleton (componentGroup e) :=
      componentGroup_subsingleton ((Fintype.card_eq_zero (α := ι)).le.trans zero_le_one) e
    infer_instance
  · have hcard : Nat.card (componentGroup e) = kirchhoffCount e :=
      natCard_componentGroup_eq_kirchhoffCount he
    exact Nat.finite_of_card_ne_zero (by rw [hcard]; exact (kirchhoffCount_pos he).ne')

end S_ModularCurve_finite_componentGroup_of_pos
end P2MW
export P2MW.S_ModularCurve_finite_componentGroup_of_pos (solution)
