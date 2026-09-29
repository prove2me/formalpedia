-- Prove2me | solution 1 for InverseGalois.fixedPoints_fieldRange_isRealizable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T01:35:36.887726+00:00
-- url     : https://prove2.me/submissions/427eff1e-4841-468e-80d0-4a945f75b64e

import Definitions.Def_InverseGalois_realizability
import Mathlib

open InverseGalois

universe u

theorem solution (G : Type u) (L : Type) [Fintype G] [Group G]
    [Field L] [CharZero L] [MulSemiringAction G L] [FaithfulSMul G L]
    (φ : FixedPoints.subfield G L →ₐ[ℚ] ℂ) :
    IsRealizable φ.fieldRange G := by
  let F := FixedPoints.subfield G L
  let e : F ≃+* φ.fieldRange := φ.equivFieldRange.toRingEquiv
  letI : Algebra F L := F.toAlgebra
  letI : IsGaloisGroup G F L := inferInstance
  letI : Algebra φ.fieldRange L :=
    ((algebraMap F L).comp e.symm.toRingHom).toAlgebra
  letI : IsGaloisGroup G φ.fieldRange L :=
    IsGaloisGroup.of_ringEquiv G F φ.fieldRange L e (by
      intro a
      change (algebraMap F L) (e.symm (e a)) = (algebraMap F L) a
      rw [e.symm_apply_apply])
  letI : FaithfulSMul φ.fieldRange L :=
    (faithfulSMul_iff_algebraMap_injective φ.fieldRange L).mpr
      (RingHom.injective (algebraMap φ.fieldRange L))
  constructor
  exact ⟨{
    L := L
    to_field := inferInstance
    to_algebra := inferInstance
    to_isGalois := IsGaloisGroup.isGalois G φ.fieldRange L
    iso := IsGaloisGroup.mulEquivAlgEquiv G φ.fieldRange L }⟩
