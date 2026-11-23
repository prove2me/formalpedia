-- Prove2me | solution 1 for GlobalTheory.NoetherInt.quasiFiniteAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:32.948568+00:00
-- url     : https://prove2.me/submissions/9516b057-4b37-4b69-ae83-a7143fe4d91e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherInt
open MvPolynomial
namespace GlobalTheory.NoetherInt
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (q : Ideal S)
    [q.IsPrime] :
    f.QuasiFiniteAt q ↔ ((algebraMap S (Localization.AtPrime q)).comp f).QuasiFinite := by
  letI := f.toAlgebra
  have : f = algebraMap R S := rfl
  rw [this, ← IsScalarTower.algebraMap_eq R S (Localization.AtPrime q),
    RingHom.quasiFinite_algebraMap]
end GlobalTheory.NoetherInt
