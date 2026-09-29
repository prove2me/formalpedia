-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.mem_smoothLocus_of_mem_range_fst_geomGeneric
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/0fb31dfe-3722-50b8-9158-899a4923f078

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_mem_smoothLocus_of_mem_range_fst_geomGeneric

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra IsLocalRing ModularCurve ModularCurve.DRLevel

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

open GaloisRep

namespace G1dAux

theorem exists_mul_pow_mem (p : ℕ) (hp : p.Prime) (q : ℚ) :
    ∃ (n : ℕ) (a : ℚ), a ∈ ratLocalizedAt p ∧ q * (p : ℚ) ^ n = a := by

  obtain ⟨n, d, hd, hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd q.den_nz p hp.ne_one
  refine ⟨n, q * (p : ℚ) ^ n, ?_, rfl⟩
  show (q * (p : ℚ) ^ n).den.Coprime p

  have hq : q * (p : ℚ) ^ n = (q.num : ℚ) / (d : ℚ) := by
    have hdq : (q.den : ℚ) = (p : ℚ) ^ n * (d : ℚ) := by exact_mod_cast hden
    have hd0 : (d : ℚ) ≠ 0 := by
      intro h
      have : q.den = 0 := by exact_mod_cast (show (q.den : ℚ) = 0 by rw [hdq, h, mul_zero])
      exact q.den_nz this
    have hp0 : (p : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
    rw [eq_div_iff hd0]
    calc q * (p : ℚ) ^ n * (d : ℚ) = q * (q.den : ℚ) := by rw [hdq]; ring
      _ = (q.num : ℚ) := Rat.mul_den_eq_num q
  rw [hq]

  have hdvd : ((q.num : ℚ) / (d : ℚ)).den ∣ d := by
    have h1 : (((q.num : ℚ) / (d : ℚ)).den : ℤ) ∣ (d : ℤ) := by
      have := Rat.den_dvd q.num d
      simpa [Rat.divInt_eq_div] using this
    exact Int.natCast_dvd_natCast.mp h1
  exact Nat.Coprime.coprime_dvd_left hdvd ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd).symm

scoped instance isLocalizationAway (p : ℕ) [Fact p.Prime] :
    IsLocalization.Away ((p : ℕ) : ↥(ratLocalizedAt p)) ℚ where
  map_units := by
    rintro ⟨_, n, rfl⟩
    simp only [map_pow]
    exact IsUnit.pow _ (by
      rw [isUnit_iff_ne_zero, map_natCast]
      exact_mod_cast (Fact.out : p.Prime).ne_zero)
  surj := fun q => by
    obtain ⟨n, a, ha, hqa⟩ := exists_mul_pow_mem p Fact.out q
    exact ⟨⟨⟨a, ha⟩, ⟨_, n, rfl⟩⟩, by simp at hqa ⊢; exact hqa⟩
  exists_of_eq := fun {x y} h => ⟨1, by
    have : (x : ℚ) = y := h
    simpa using Subtype.ext this⟩

end G1dAux
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_mem_smoothLocus_of_mem_range_fst_geomGeneric.G1dAux"

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (x : ↥(X N₀ p))
    (hx : x ∈ Set.range (pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).base) :
    x ∈ (𝔓.smoothLocus : Set (X N₀ p)) := by
  classical
  let ι : Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of (R p)) := Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))
  haveI hι : IsOpenImmersion ι := IsOpenImmersion.of_isLocalization ((p : ℕ) : R p)
  let f₁ := pullback.fst (toBase N₀ p) ι
  let U : (X N₀ p).Opens := f₁.opensRange

  have hU : Smooth (U.ι ≫ toBase N₀ p) := by
    let e := IsOpenImmersion.isoOfRangeEq f₁ U.ι (by rw [Scheme.Opens.range_ι]; rfl)
    have he : e.hom ≫ U.ι = f₁ := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    have hfac : U.ι ≫ toBase N₀ p = e.inv ≫ pullback.snd (toBase N₀ p) ι ≫ ι := by
      rw [← pullback.condition, show pullback.fst (toBase N₀ p) ι = e.hom ≫ U.ι from he.symm, Category.assoc,
        Iso.inv_hom_id_assoc]
    rw [hfac]
    haveI : SmoothOfRelativeDimension 1 (pullback.snd (toBase N₀ p) ι) := 𝔓.smooth_generic
    haveI : Smooth (pullback.snd (toBase N₀ p) ι) := SmoothOfRelativeDimension.smooth 1 _
    infer_instance
  have hle := 𝔓.smoothLocus_maximal U hU
  obtain ⟨w, rfl⟩ := hx
  apply hle

  let k : pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶
      pullback (toBase N₀ p) ι :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) (by
      rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq (R p) ℚ (AlgebraicClosure ℚ)])
  have hk : k ≫ f₁ = pullback.fst _ _ := pullback.lift_fst _ _ _
  refine ⟨k.base w, ?_⟩
  change (k ≫ f₁).base w = _
  rw [hk]

#print axioms solution

end S_ModularCurve_DRModelPackageLevel_mem_smoothLocus_of_mem_range_fst_geomGeneric
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_mem_smoothLocus_of_mem_range_fst_geomGeneric (solution)
