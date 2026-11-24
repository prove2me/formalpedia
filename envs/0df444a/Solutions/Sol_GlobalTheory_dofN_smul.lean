-- Prove2me | solution 1 for GlobalTheory.dofN_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:36:01.543176+00:00
-- url     : https://prove2.me/submissions/9db94928-1999-4a67-b887-a1bf9539189a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NablaValueCopiesBilinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory
variable {R : Type} [CommRing R] {d n : ℕ}
namespace GlobalTheory
theorem _root_.solution (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (t : R) (f : PS R n d) :
    DofN F b u (t • f) = t • DofN F b u f := by
  simp only [DofN, Derivation.map_smul, map_smul, mul_smul_comm, Finset.smul_sum]
end GlobalTheory
