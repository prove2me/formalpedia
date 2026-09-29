-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.isIntegral_xO_of_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/538e712a-5883-5d52-aa25-34a22fdf1480

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Theorems.Thm_AlgebraicGeometry_map_appTop_mem_nonZeroDivisors_of_flat
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_mem_nonZeroDivisors_of_isIntegral_basicOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_isIntegral_xO_of_mem_maximalIdeal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

private theorem isLocalization_away_of_mem_maximalIdeal {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (q : O) (hq0 : q ≠ 0) (hq : q ∈ IsLocalRing.maximalIdeal O)
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] : IsLocalization.Away q K where
  map_units y := by
    obtain ⟨n, hn⟩ := y.2
    have : (y : O) ≠ 0 := by rw [← hn]; exact pow_ne_zero _ hq0
    exact IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr this)
  surj z := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) z
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
    obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq0 hϖ

    have hm : m ≠ 0 := by
      rintro rfl
      apply (IsLocalRing.mem_maximalIdeal _).mp hq
      simp
    obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm

    refine ⟨(a * ↑u⁻¹ * (↑v) ^ n * ϖ ^ (n * m'), ⟨(↑v * ϖ ^ (m' + 1)) ^ n, n, rfl⟩), ?_⟩
    have hinj := IsFractionRing.injective O K
    have hu : algebraMap O K ↑u ≠ 0 := (map_ne_zero_iff _ hinj).mpr (Units.ne_zero u)
    have hϖn : algebraMap O K (ϖ ^ n) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ hϖ.ne_zero)
    show algebraMap O K a / algebraMap O K (↑u * ϖ ^ n) * algebraMap O K ((↑v * ϖ ^ (m' + 1)) ^ n) =
      algebraMap O K (a * ↑u⁻¹ * ↑v ^ n * ϖ ^ (n * m'))
    rw [div_mul_eq_mul_div, div_eq_iff ((map_ne_zero_iff _ hinj).mpr (mul_ne_zero (Units.ne_zero u) (pow_ne_zero _ hϖ.ne_zero))),
      ← map_mul, ← map_mul]
    congr 1
    have : (↑v * ϖ ^ (m' + 1)) ^ n = ↑v ^ n * ϖ ^ (n * m') * ϖ ^ n := by ring
    rw [this]
    have hu' : (↑u⁻¹ : O) * ↑u = 1 := Units.inv_mul u
    linear_combination (-(a * ↑v ^ n * ϖ ^ (n * m') * ϖ ^ n)) * hu'
  exists_of_eq {x y} h := ⟨1, by simpa using (IsFractionRing.injective O K) h⟩

private theorem charZero_of_ratLocalizedAt (q : ℕ) [Fact q.Prime] {O : Type} [CommRing O] [IsDomain O]
    (ρ : ↥(GaloisRep.ratLocalizedAt q) →+* O) (hq : ((q : ℕ) : O) ≠ 0) : CharZero O := by
  refine ⟨fun m n hmn => ?_⟩

  suffices key : ∀ k : ℕ, (k : O) = 0 → k = 0 by
    rcases Nat.le_total m n with h | h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      have : (d : O) = 0 := by
        have := hmn; push_cast at this; linear_combination -this
      simp [key d this]
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      have : (d : O) = 0 := by
        have := hmn; push_cast at this; linear_combination this
      simp [key d this]
  intro k hk
  by_contra hk0

  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0 q (Fact.out : q.Prime).ne_one

  have hmem : ((m : ℚ)⁻¹) ∈ GaloisRep.ratLocalizedAt q := by
    show ((m : ℚ)⁻¹).den.Coprime q
    have hm0 : m ≠ 0 := by rintro rfl; simp at hk0
    rw [Rat.inv_natCast_den_of_pos (Nat.pos_of_ne_zero hm0)]
    exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).mpr hm).symm
  have hunit : IsUnit ((m : ℕ) : O) := by
    refine isUnit_iff_exists_inv.mpr ⟨ρ ⟨(m : ℚ)⁻¹, hmem⟩, ?_⟩
    have hm0 : (m : ℚ) ≠ 0 := by
      have : m ≠ 0 := by rintro rfl; simp at hk0
      exact_mod_cast this
    have : ((m : ↥(GaloisRep.ratLocalizedAt q)) * ⟨(m : ℚ)⁻¹, hmem⟩ : ↥(GaloisRep.ratLocalizedAt q)) = 1 := by
      apply Subtype.ext
      push_cast
      exact mul_inv_cancel₀ hm0
    have h2 := congrArg ρ this
    rw [map_mul, map_one, map_natCast] at h2
    exact h2
  have : ((q : O) ^ a) * (m : O) = 0 := by exact_mod_cast hk
  rcases mul_eq_zero.mp this with h | h
  · exact hq (pow_eq_zero_iff'.mp h).1
  · exact hunit.ne_zero h

private theorem ratLocalizedAt_ringHom_apply (q : ℕ) {K : Type} [Field K] [CharZero K]
    (τ : ↥(GaloisRep.ratLocalizedAt q) →+* K) (r : ↥(GaloisRep.ratLocalizedAt q)) : τ r = ((r : ℚ) : K) := by
  have hden : (((r : ℚ).den : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (r : ℚ).den_nz
  apply mul_left_injective₀ hden

  have hmemd : (((r : ℚ).den : ℕ) : ℚ) ∈ GaloisRep.ratLocalizedAt q := by
    show ((((r : ℚ).den : ℕ) : ℚ)).den.Coprime q
    simp
  have hmemn : (((r : ℚ).num : ℤ) : ℚ) ∈ GaloisRep.ratLocalizedAt q := by
    show ((((r : ℚ).num : ℤ) : ℚ)).den.Coprime q
    simp
  have h1 : r * ⟨_, hmemd⟩ = (⟨_, hmemn⟩ : ↥(GaloisRep.ratLocalizedAt q)) := by
    apply Subtype.ext
    show (r : ℚ) * ((r : ℚ).den : ℚ) = ((r : ℚ).num : ℚ)
    exact Rat.mul_den_eq_num (r : ℚ)
  have h2 := congrArg τ h1
  rw [map_mul] at h2
  have hd : τ ⟨_, hmemd⟩ = (((r : ℚ).den : ℕ) : K) := by
    have : (⟨_, hmemd⟩ : ↥(GaloisRep.ratLocalizedAt q)) = (((r : ℚ).den : ℕ) : ↥(GaloisRep.ratLocalizedAt q)) :=
      Subtype.ext (by push_cast; rfl)
    rw [this, map_natCast]
  have hn : τ ⟨_, hmemn⟩ = (((r : ℚ).num : ℤ) : K) := by
    have : (⟨_, hmemn⟩ : ↥(GaloisRep.ratLocalizedAt q)) = (((r : ℚ).num : ℤ) : ↥(GaloisRep.ratLocalizedAt q)) :=
      Subtype.ext (by push_cast; rfl)
    rw [this, map_intCast]
  rw [hd, hn] at h2
  show τ r * _ = ((r : ℚ) : K) * _
  rw [h2, ← Rat.cast_natCast, ← Rat.cast_mul, Rat.mul_den_eq_num, Rat.cast_intCast]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ρO : R p →+* O) (hp0 : ((p : ℕ) : O) ≠ 0) (hp : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) :
    IsIntegral (XO (ΓM M H) hj ρO) := by
  classical
  set ι : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of (R p)) := Spec.map (CommRingCat.ofHom ρO) with hι
  set X := pullback (toBase p (ΓM M H) hj) ι
  set πX : X ⟶ Spec (CommRingCat.of O) := pullback.snd (toBase p (ΓM M H) hj) ι with hπX
  let K : Type := FractionRing O
  haveI : IsLocalization.Away ((p : ℕ) : O) K := isLocalization_away_of_mem_maximalIdeal _ hp0 hp K
  have hq0 : ((p : ℕ) : O) ≠ 0 := hp0
  haveI : CharZero O := charZero_of_ratLocalizedAt p ρO hq0
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective O K)

  haveI := 𝔛.flat
  haveI : Flat πX := inferInstance

  set s : Γ(X, ⊤) := πX.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ((p : ℕ) : O)) with hs
  have hreg : ∀ U : X.Opens, IsAffineOpen U → X.presheaf.map (homOfLE le_top).op s ∈ nonZeroDivisors Γ(X, U) :=
    fun U hU => AlgebraicGeometry.map_appTop_mem_nonZeroDivisors_of_flat πX _ (mem_nonZeroDivisors_of_ne_zero hq0) U hU

  set ιK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom (algebraMap O K)) with hιK
  haveI : IsOpenImmersion ιK := IsOpenImmersion.of_isLocalization ((p : ℕ) : O)
  let τ : R p →+* K := (algebraMap O K).comp ρO
  let ψ : ℚ →+* K := Rat.castHom K
  have hψ : ψ.comp (algebraMap (R p) ℚ) = τ := by
    ext r
    show ((algebraMap (R p) ℚ r : ℚ) : K) = τ r
    rw [ratLocalizedAt_ringHom_apply p τ r]
    rfl
  have hcompK : ιK ≫ ι = Spec.map (CommRingCat.ofHom τ) := by
    rw [hιK, hι, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hcompQ : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)) =
      Spec.map (CommRingCat.ofHom τ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
  haveI hgi := 𝔛.geomIntegral_generic
  haveI hZ : IsIntegral (pullback (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))))
      (Spec.map (CommRingCat.ofHom ψ))) :=
    hgi.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback _ _)
  let e1 := pullbackLeftPullbackSndIso (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))
    (Spec.map (CommRingCat.ofHom ψ)) ≪≫ pullback.congrHom rfl hcompQ
  let e2 := pullbackLeftPullbackSndIso (toBase p (ΓM M H) hj) ι ιK ≪≫ pullback.congrHom rfl hcompK
  haveI : IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom τ))) := IsIntegral.of_isIso e1.hom
  haveI : IsIntegral (pullback πX ιK) := IsIntegral.of_isIso e2.inv

  have hr : Set.range ⇑ιK = ((PrimeSpectrum.basicOpen ((p : ℕ) : O) : TopologicalSpace.Opens (PrimeSpectrum O)) :
      Set (PrimeSpectrum O)) := by
    rw [hιK]
    exact PrimeSpectrum.localization_away_comap_range K ((p : ℕ) : O)
  have hrange : Set.range ⇑(pullback.fst πX ιK) = Set.range ⇑((X.basicOpen s).ι) := by
    rw [Scheme.Pullback.range_fst, hr, Scheme.Opens.range_ι, hs, ← Scheme.preimage_basicOpen_top,
      basicOpen_eq_of_affine]
    rfl
  let e' : pullback πX ιK ≅ (X.basicOpen s : Scheme) := IsOpenImmersion.isoOfRangeEq _ _ hrange
  haveI : IsIntegral (X.basicOpen s : Scheme) := IsIntegral.of_isIso e'.hom
  exact AlgebraicGeometry.isIntegral_of_mem_nonZeroDivisors_of_isIntegral_basicOpen s hreg

end S_ModularCurve_XHDRModelAtP_isIntegral_xO_of_mem_maximalIdeal
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_isIntegral_xO_of_mem_maximalIdeal (solution)
