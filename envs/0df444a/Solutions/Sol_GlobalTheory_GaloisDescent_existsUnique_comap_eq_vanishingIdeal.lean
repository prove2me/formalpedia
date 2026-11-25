-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.existsUnique_comap_eq_vanishingIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:57:37.822288+00:00
-- url     : https://prove2.me/submissions/f5f916dc-fb8d-455f-ad24-3f1593b09784

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueComapEqVanishingIdeal
import Theorems.Thm_GlobalTheory_GaloisDescent_idealSheaf_stable_iff_exists_comap

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
theorem _root_.solution (s : G → L →ₐ[K] L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L)) (Z : Closeds Y)
    (hZ : ∀ g, ∀ y ∈ Z, twist H (s g) y ∈ Z) :
    ∃! J : X.IdealSheafData, J.comap π = Scheme.IdealSheafData.vanishingIdeal Z := by
  refine (idealSheaf_stable_iff_exists_comap H s hs _).1 fun g => ?_
  rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
    Scheme.IdealSheafData.support_comap]
  intro y hy
  change twist H (s g) y ∈ ((Scheme.IdealSheafData.vanishingIdeal Z).support : Set Y)
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact hZ g y hy
end GlobalTheory.GaloisDescent
