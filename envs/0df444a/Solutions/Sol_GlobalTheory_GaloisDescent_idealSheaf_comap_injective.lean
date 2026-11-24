-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.idealSheaf_comap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:17:10.966897+00:00
-- url     : https://prove2.me/submissions/c06dd619-f204-44f2-9579-03b7d1d4d322

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueComapEqVanishingIdeal
import Theorems.Thm_GlobalTheory_GaloisDescent_idealSheaf_map_comap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace GlobalTheory.QCoh.Qcqs
universe u
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L : Type u} [Field K] [Field L] [Algebra K L] {X Y : Scheme.{u}}
  {p : X ⟶ Spec (.of K)} {q : Y ⟶ Spec (.of L)} {π : Y ⟶ X}
  (H : IsPullback π q p (Spec.map (CommRingCat.ofHom (algebraMap K L)))) {G : Type*}
include H
namespace GlobalTheory.GaloisDescent
theorem _root_.solution :
    Function.Injective fun J : X.IdealSheafData => J.comap π := fun J J' h => by
  rw [← idealSheaf_map_comap H J, ← idealSheaf_map_comap H J']
  exact congrArg (·.map π) h
end GlobalTheory.GaloisDescent
