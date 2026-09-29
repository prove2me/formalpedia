-- Prove2me | solution 1 for M4aHerbrand.restrictNormalHom_idelicArtinMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/63cd115b-bb37-5400-9aee-9b0bd1f7a63a

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Theorems.Thm_HeckeCharacter_exists_isAdjuster
import Theorems.Thm_LT_Artin_eq_artinFrob_of_isArithFrobAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_restrictNormalHom_idelicArtinMap_eq
set_option autoImplicit false
p2m_open "NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_restrictNormalHom_idelicArtinMap_eq.M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin"
open scoped IsMulCommutative NumberField.PlaceDecomp

namespace M4aHerbrand
p2m_export "M4aHerbrand" "principalIdeles"
namespace ArtCompat
p2m_open "M4aHerbrand"

open scoped Pointwise

section Inertia

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [MulSemiringAction G B]

theorem inertia_smul_le [IsMulCommutative G] (g : G) (Q : Ideal B) :
    (g • Q).inertia G ≤ Q.inertia G := by
  intro σ hσ y
  have h : σ • (g • y) - g • y ∈ g • Q := hσ (g • y)
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at h
  simp only [smul_sub, smul_smul, inv_mul_cancel, one_smul] at h
  have hc : g⁻¹ * (σ * g) = σ := by rw [mul_comm σ g, inv_mul_cancel_left]
  rw [hc] at h
  exact h

theorem inertia_smul_eq [IsMulCommutative G] (g : G) (Q : Ideal B) :
    (g • Q).inertia G = Q.inertia G := by
  refine le_antisymm (inertia_smul_le g Q) ?_
  have h := inertia_smul_le g⁻¹ (g • Q)
  rwa [inv_smul_smul] at h

end Inertia

section Unramified

variable (E L : Type*) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L]
  [IsGalois E L] [IsMulCommutative (L ≃ₐ[E] L)]

omit [NumberField L] [IsGalois E L] [IsMulCommutative (L ≃ₐ[E] L)] in
theorem inertia_primeAbove_eq_bot_of_not_dvd {n : ℕ} {𝔣 : Ideal (𝓞 E)}
    (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E L n 𝔣)
    (v : HeightOneSpectrum (𝓞 E)) (hv : ¬ v.asIdeal ∣ 𝔣) :
    (primeAbove E L v).inertia (L ≃ₐ[E] L) = ⊥ := by
  by_contra h
  apply hv
  have hne : NumberField.NormIndex.admissibleExpOfDegree E n v ≠ 0 := by
    unfold NumberField.NormIndex.admissibleExpOfDegree; omega
  exact (dvd_pow_self v.asIdeal hne).trans (hadm.2 v h)

theorem inertia_eq_bot_of_not_dvd {n : ℕ} {𝔣 : Ideal (𝓞 E)}
    (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E L n 𝔣)
    (v : HeightOneSpectrum (𝓞 E)) (hv : ¬ v.asIdeal ∣ 𝔣)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q.under (𝓞 E) = v.asIdeal) :
    Q.inertia (L ≃ₐ[E] L) = ⊥ := by
  haveI : Q.LiesOver v.asIdeal := ⟨hQ.symm⟩
  obtain ⟨σ, hσ⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal (primeAbove E L v) Q (L ≃ₐ[E] L)
  rw [← hσ, inertia_smul_eq]
  exact inertia_primeAbove_eq_bot_of_not_dvd E L hadm v hv

end Unramified

section Restrict

theorem algebraMap_ringOfIntegers_smul_restrictNormalHom
    (E L F : Type*) [Field E] [Field L] [Field F]
    [Algebra E L] [Algebra E F] [Algebra L F] [IsScalarTower E L F] [Normal E L]
    (φ : F ≃ₐ[E] F) (x : 𝓞 L) :
    algebraMap (𝓞 L) (𝓞 F) (AlgEquiv.restrictNormalHom L φ • x) = φ • algebraMap (𝓞 L) (𝓞 F) x := by
  apply RingOfIntegers.coe_injective
  change algebraMap L F ((AlgEquiv.restrictNormalHom L φ) (x : L)) = φ (algebraMap L F (x : L))
  exact AlgEquiv.restrictNormal_commutes φ L x

theorem isArithFrobAt_restrictNormalHom
    (E L F : Type*) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra E F] [Algebra L F] [IsScalarTower E L F] [IsGalois E F] [IsGalois E L]
    {φ : F ≃ₐ[E] F} {P : Ideal (𝓞 F)}
    (H : IsArithFrobAt (𝓞 E) φ P) :
    IsArithFrobAt (𝓞 E) (AlgEquiv.restrictNormalHom L φ) (P.under (𝓞 L)) := by
  unfold IsArithFrobAt AlgHom.IsArithFrobAt at H ⊢
  intro x
  rw [Ideal.under_under, Ideal.under_def, Ideal.mem_comap, map_sub, map_pow,
    MulSemiringAction.toAlgHom_apply, algebraMap_ringOfIntegers_smul_restrictNormalHom E L F]
  have h := H (algebraMap (𝓞 L) (𝓞 F) x)
  rwa [MulSemiringAction.toAlgHom_apply] at h

end Restrict

section Frob

variable (E L F : Type*) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
  [Algebra E L] [Algebra E F] [Algebra L F] [IsScalarTower E L F] [IsGalois E F] [IsGalois E L]
  [IsMulCommutative (L ≃ₐ[E] L)]

theorem restrictNormalHom_artinFrob_eq {n : ℕ} {𝔣L : Ideal (𝓞 E)}
    (hadmL : NumberField.NormIndex.IsAdmissibleModulusOfDegree E L n 𝔣L)
    (v : HeightOneSpectrum (𝓞 E)) (hv : ¬ v.asIdeal ∣ 𝔣L) :
    AlgEquiv.restrictNormalHom L (artinFrob E F v) = artinFrob E L v := by
  have hP : (primeAbove E F v).under (𝓞 E) = v.asIdeal := under_primeAbove E F v
  have hQ : ((primeAbove E F v).under (𝓞 L)).under (𝓞 E) = v.asIdeal := by
    rw [Ideal.under_under]; exact hP
  have hI : ((primeAbove E F v).under (𝓞 L)).inertia (L ≃ₐ[E] L) = ⊥ :=
    inertia_eq_bot_of_not_dvd E L hadmL v hv _ hQ
  have H : IsArithFrobAt (𝓞 E) (AlgEquiv.restrictNormalHom L (artinFrob E F v))
      ((primeAbove E F v).under (𝓞 L)) :=
    isArithFrobAt_restrictNormalHom E L F (isArithFrobAt_artinFrob E F v)
  exact LT.Artin.eq_artinFrob_of_isArithFrobAt E L v H hQ hI

end Frob

section Adjuster

variable (K : Type*) [Field K] [NumberField K]

theorem isAdjuster_of_dvd {𝔣 𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) (hd : 𝔣 ∣ 𝔪)
    {u : (AdeleRing (𝓞 K) K)ˣ} {α : Kˣ} (h : IsAdjuster K 𝔪 u α) : IsAdjuster K 𝔣 u α := by
  refine ⟨fun v hv => ?_, h.sign⟩
  obtain ⟨h1, h2⟩ := h.cong v (hv.trans hd)
  refine ⟨h1, h2.trans ?_⟩
  rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
  exact Associates.count_le_count_of_le (Associates.mk_ne_zero.mpr h𝔪)
    (Associates.irreducible_mk.mpr v.irreducible) (Associates.mk_le_mk_of_dvd hd)

theorem isAdjuster_one_mul_inv {𝔣 : Ideal (𝓞 K)} {x : (AdeleRing (𝓞 K) K)ˣ} {α : Kˣ}
    (h : IsAdjuster K 𝔣 x α) :
    IsAdjuster K 𝔣 (x * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹) 1 := by
  have e : x * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹
      * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (1 : Kˣ))⁻¹
      = x * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ := by
    rw [map_one, inv_one, mul_one]
  exact ⟨fun v hv => by rw [e]; exact h.cong v hv, fun τ => by rw [e]; exact h.sign τ⟩

theorem placeOrd_projFin_eq_zero_of_isAdjuster_one {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ}
    (h : IsAdjuster K 𝔣 u 1) (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ 𝔣) :
    placeOrd K (projFin K u) v = 0 := by
  rw [placeOrd_eq_zero_iff]
  have h1 := (h.cong v hv).1
  rw [map_one, inv_one, mul_one] at h1
  exact h1

theorem hasFiniteMulSupport_artinFrob_zpow_placeOrd
    (M : Type*) [Field M] [NumberField M] [Algebra K M] [IsGalois K M] [IsMulCommutative (M ≃ₐ[K] M)]
    (u : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => artinFrob K M v ^ placeOrd K u v).Finite := by
  refine (finite_support_placeOrd K u).subset (Function.mulSupport_subset_iff'.mpr fun v hv => ?_)
  rw [Function.mem_support, not_not] at hv
  rw [hv, zpow_zero]

theorem map_algebraMap_mem_principalIdeles (α : Kˣ) :
    Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α ∈ principalIdeles (𝓞 K) K := ⟨α, rfl⟩

end Adjuster

end M4aHerbrand.ArtCompat

open M4aHerbrand.ArtCompat

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]
    (L : Type) [Field L] [NumberField L] [Algebra E L] [Algebra L F] [IsScalarTower E L F] [IsGalois E L]
    [IsMulCommutative (L ≃ₐ[E] L)]

    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)

    (𝔣L : Ideal (𝓞 E)) (hadmL : NumberField.NormIndex.IsAdmissibleModulusOfDegree E L (Module.finrank E L) 𝔣L)
    (rL : (AdeleRing (𝓞 E) E)ˣ →* (L ≃ₐ[E] L))
    (hrL₁ : principalIdeles (𝓞 E) E ≤ rL.ker)
    (hrL₂ : rL.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E L).idelicNorm.range)
    (hrL₃ : Function.Surjective rL)
    (hrL₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣L u 1 →
      rL u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E L v ^ placeOrd E (projFin E u) v)
    (x : (AdeleRing (𝓞 E) E)ˣ) :
    AlgEquiv.restrictNormalHom L (r x) = rL x := by
  classical

  have h𝔪 : 𝔣 * 𝔣L ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim hadm.1 hadmL.1
  obtain ⟨α, hα⟩ := HeckeCharacter.exists_isAdjuster E (𝔣 * 𝔣L) h𝔪 x
  set u : (AdeleRing (𝓞 E) E)ˣ := x * (Units.map (algebraMap E (AdeleRing (𝓞 E) E)) α)⁻¹ with hu
  have hu𝔪 : IsAdjuster E (𝔣 * 𝔣L) u 1 := isAdjuster_one_mul_inv E hα
  have huF : IsAdjuster E 𝔣 u 1 :=
    isAdjuster_one_mul_inv E (isAdjuster_of_dvd E h𝔪 (dvd_mul_right 𝔣 𝔣L) hα)
  have huL : IsAdjuster E 𝔣L u 1 :=
    isAdjuster_one_mul_inv E (isAdjuster_of_dvd E h𝔪 (dvd_mul_left 𝔣L 𝔣) hα)
  have hxu : x = u * Units.map (algebraMap E (AdeleRing (𝓞 E) E)) α := by
    rw [hu, inv_mul_cancel_right]
  have hprin := map_algebraMap_mem_principalIdeles E α
  have hrx : r x = r u := by
    rw [hxu, map_mul, MonoidHom.mem_ker.mp (hr₁ hprin), mul_one]
  have hrLx : rL x = rL u := by
    rw [hxu, map_mul, MonoidHom.mem_ker.mp (hrL₁ hprin), mul_one]
  rw [hrx, hrLx, hr₄ u huF, hrL₄ u huL,
    MonoidHom.map_finprod _ (hasFiniteMulSupport_artinFrob_zpow_placeOrd E F (projFin E u))]
  refine finprod_congr fun v => ?_
  rw [map_zpow]
  by_cases hv : v.asIdeal ∣ 𝔣 * 𝔣L
  · rw [placeOrd_projFin_eq_zero_of_isAdjuster_one E hu𝔪 v hv, zpow_zero, zpow_zero]
  · rw [restrictNormalHom_artinFrob_eq E L F hadmL v (fun h => hv (h.mul_left 𝔣))]

end S_M4aHerbrand_restrictNormalHom_idelicArtinMap_eq
end P2MW
export P2MW.S_M4aHerbrand_restrictNormalHom_idelicArtinMap_eq (solution)
