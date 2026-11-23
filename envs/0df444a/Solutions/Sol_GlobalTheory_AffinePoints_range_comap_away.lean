-- Prove2me | solution 1 for GlobalTheory.AffinePoints.range_comap_away
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:23.874916+00:00
-- url     : https://prove2.me/submissions/b25d317a-1828-4d4d-892f-e9b7f2bc6344

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set
variable {R A B K : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B] [Field K] [Algebra R K]
namespace GlobalTheory.AffinePoints
theorem _root_.solution (f : A) [IsLocalization.Away f B] :
    range (comap (IsScalarTower.toAlgHom R A B) : (B →ₐ[R] K) → (A →ₐ[R] K)) = {p | p f ≠ 0} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ((IsLocalization.Away.algebraMap_isUnit (S := B) f).map q).ne_zero
  · intro hp
    refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers f) (f := p) ?_, ?_⟩
    · rintro ⟨_, n, rfl⟩
      simpa using (isUnit_iff_ne_zero.2 hp).pow n
    · ext a; simp
end GlobalTheory.AffinePoints
