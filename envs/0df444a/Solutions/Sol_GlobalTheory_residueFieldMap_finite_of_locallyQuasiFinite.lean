-- Prove2me | solution 1 for GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:38:48.685575+00:00
-- url     : https://prove2.me/submissions/89af1ea5-faa2-48f9-841c-2c1d76c43fb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldMapFiniteOfQuasiFinite
import Theorems.Thm_GlobalTheory_residueField_map_finite_of_quasiFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Y Z : Scheme.{0}} (g : Y ⟶ Z)
    [LocallyQuasiFinite g] (y : Y) : (g.residueFieldMap y).hom.Finite := by
  have hq : (g.stalkMap y).hom.QuasiFinite := g.quasiFiniteAt y
  exact residueField_map_finite_of_quasiFinite _ hq
end GlobalTheory
