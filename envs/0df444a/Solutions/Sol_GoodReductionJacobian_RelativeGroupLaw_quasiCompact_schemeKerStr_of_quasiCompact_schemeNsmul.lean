-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.quasiCompact_schemeKerStr_of_quasiCompact_schemeNsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f5842b53-44ea-59d6-a9d1-6ea6aab0550b

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_quasiCompact_schemeKerStr_of_quasiCompact_schemeNsmul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (n : ℕ) [QuasiCompact (G.schemeNsmul n)] :
    QuasiCompact (G.schemeKerStr n) := by
  dsimp only [GoodReductionJacobian.RelativeGroupLaw.schemeKerStr]
  infer_instance

end S_GoodReductionJacobian_RelativeGroupLaw_quasiCompact_schemeKerStr_of_quasiCompact_schemeNsmul
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_quasiCompact_schemeKerStr_of_quasiCompact_schemeNsmul (solution)
