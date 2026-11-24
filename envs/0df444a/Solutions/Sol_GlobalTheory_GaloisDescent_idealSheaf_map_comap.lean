-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.idealSheaf_map_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:56:29.534881+00:00
-- url     : https://prove2.me/submissions/fed6b102-cd74-4a08-ae2c-e330a072c5dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueComapEqVanishingIdeal

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
theorem _root_.solution (J : X.IdealSheafData) : (J.comap π).map π = J := by
  have : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    .of_isDominant _
  have h : IsSchemeTheoreticallyDominant (pullback.snd π J.subschemeι) :=
    .of_isPullback ((IsPullback.of_hasPullback π J.subschemeι).flip.paste_vert H).flip
  rw [Scheme.IdealSheafData.comap, Scheme.IdealSheafData.map_ker, pullback.condition,
    Scheme.Hom.ker_comp, h.ker_eq_bot, Scheme.IdealSheafData.map_bot,
    Scheme.IdealSheafData.ker_subschemeι]
end GlobalTheory.GaloisDescent
