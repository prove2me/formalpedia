-- Prove2me | solution 1 for HopfAlgebra.finiteFlat_tensorProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c13b1081-5bc5-5174-b300-5598ce677271

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_finiteFlat_tensorProduct

open scoped TensorProduct

theorem solution {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [HopfAlgebra R A] [HopfAlgebra R B]
    [Module.Finite R A] [Module.Flat R A] [Module.Finite R B] [Module.Flat R B] :
    Module.Finite R (A ⊗[R] B) ∧ Module.Flat R (A ⊗[R] B) :=
  ⟨inferInstance, inferInstance⟩

end S_HopfAlgebra_finiteFlat_tensorProduct
end P2MW
export P2MW.S_HopfAlgebra_finiteFlat_tensorProduct (solution)
