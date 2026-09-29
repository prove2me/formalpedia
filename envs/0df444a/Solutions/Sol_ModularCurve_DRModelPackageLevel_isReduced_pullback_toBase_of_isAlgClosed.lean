-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.isReduced_pullback_toBase_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d9d85b70-bc02-5050-b7e5-dd70c12698f3

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_isReduced_pullback_toBase_of_isAlgClosed
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
p2m_open "ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_isReduced_pullback_toBase_of_isAlgClosed.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel"

namespace ModularCurve
p2m_export "ModularCurve" "DRLevel.R DRLevel.toBase DRModelPackageLevel IgusaScheme"
namespace DRModelPackageLevel
p2m_export "ModularCurve.DRModelPackageLevel" "smooth_generic fibre_reduced comp"
p2m_open "ModularCurve.DRModelPackageLevel ModularCurve"

variable (q : ℕ) [Fact q.Prime]

theorem isUnit_natCast_R_of_prime_ne {p : ℕ} (hp : p.Prime) (hpq : p ≠ q) : IsUnit ((p : ℤ) : R q) := by
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := q) Fact.out
  have hmem : (p : ℤ) ∈ (Ideal.span {(q : ℤ)}).primeCompl := by
    intro h
    rw [SetLike.mem_coe, Ideal.mem_span_singleton] at h
    have : (q : ℤ).natAbs ∣ (p : ℤ).natAbs := Int.natAbs_dvd_natAbs.mpr h
    simp only [Int.natAbs_natCast] at this
    exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp).mp this).symm
  simpa using IsLocalization.map_units (R q) (⟨(p : ℤ), hmem⟩ : (Ideal.span {(q : ℤ)}).primeCompl)

theorem charZero_of_ringHom_of_ne_zero {k : Type} [Field k] (toκ : R q →+* k) (hq : (q : k) ≠ 0) : CharZero k := by
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hpp | rfl
  · exfalso
    by_cases hpq : p = q
    · subst hpq; exact hq (CharP.cast_eq_zero k p)
    · have hu := (isUnit_natCast_R_of_prime_ne q hpp hpq).map toκ
      rw [map_intCast, Int.cast_natCast, CharP.cast_eq_zero k p] at hu
      exact not_isUnit_zero hu
  · exact CharP.charP_to_charZero k

theorem ringHom_eq_algebraMap_comp {k : Type} [Field k] [CharZero k] (toκ : R q →+* k) :
    toκ = (algebraMap ℚ k).comp (algebraMap (R q) ℚ) := by
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := q) Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(q : ℤ)}).primeCompl (Subsingleton.elim _ _)

theorem isReduced_pullback_comp_generic (N₀ : ℕ) [NeZero N₀] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    {k : Type} [Field k]
    (y : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℚ)) :
    IsReduced (pullback (toBase N₀ q) (y ≫ Spec.map (CommRingCat.ofHom (algebraMap (R q) ℚ)))) := by
  set z := Spec.map (CommRingCat.ofHom (algebraMap (R q) ℚ))
  haveI : SmoothOfRelativeDimension 1 (pullback.snd (toBase N₀ q) z) := 𝔓.smooth_generic
  haveI : Smooth (pullback.snd (toBase N₀ q) z) := SmoothOfRelativeDimension.smooth 1 _
  haveI : Smooth (pullback.snd (pullback.snd (toBase N₀ q) z) y) := inferInstance
  haveI : IsReduced (pullback (pullback.snd (toBase N₀ q) z) y) :=
    AlgebraicGeometry.isReduced_of_smooth_of_field (pullback.snd (pullback.snd (toBase N₀ q) z) y)
  exact isReduced_of_isOpenImmersion (pullbackLeftPullbackSndIso (toBase N₀ q) z y).inv

end ModularCurve.DRModelPackageLevel

p2m_open "ModularCurve.DRModelPackageLevel P2MW.S_ModularCurve_DRModelPackageLevel_isReduced_pullback_toBase_of_isAlgClosed.ModularCurve.DRModelPackageLevel"

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (k : Type) [Field k] [IsAlgClosed k]
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DRLevel.R q))) :
    IsReduced (pullback (DRLevel.toBase N₀ q) x) := by
  classical
  obtain ⟨toκ, rfl⟩ : ∃ toκ : R q →+* k, x = Spec.map (CommRingCat.ofHom toκ) :=
    ⟨(Spec.preimage x).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  by_cases hq : (q : k) = 0
  · haveI : CharP k q := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hq
    exact 𝔓.fibre_reduced k toκ
  · haveI := charZero_of_ringHom_of_ne_zero q toκ hq
    obtain rfl := ringHom_eq_algebraMap_comp q toκ
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact isReduced_pullback_comp_generic q N₀ hqN 𝔓 _

end S_ModularCurve_DRModelPackageLevel_isReduced_pullback_toBase_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_isReduced_pullback_toBase_of_isAlgClosed (solution)
